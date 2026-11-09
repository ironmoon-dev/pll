#!/usr/bin/env node
/**
 * The smoke suite, run in parallel: every test file, each section of the
 * tests made of sections, and the golden corpus in shards, as separate
 * processes - as many at once as the cores carry. Each test makes its own
 * temporary files and servers (on port 0), so running them together checks
 * exactly what running them one at a time does.
 *
 * Jobs that depend on real time - a Stop's latency, a reactor's ticks, a
 * Ctrl+C sent at a moment - run afterwards, in a second phase with the
 * machine otherwise idle, so that load cannot move their timing.
 *
 *   node scripts/smoke.mjs             everything (after `pnpm run build`)
 *   node scripts/smoke.mjs cli golden  only the jobs whose names contain these
 *   node scripts/smoke.mjs --serial    one job at a time
 *   node scripts/smoke.mjs --jobs=8    at most 8 at once
 *
 * Each job's output is kept in `.smoke-logs/<job>.log`, and a failing job's
 * is printed in full at the end. The time each took is kept there too, and
 * the longest start first next time.
 */
import { spawn } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { availableParallelism } from "node:os";
import { join } from "node:path";
import { CASES } from "./golden/cases.mjs";
import { ROOT } from "./lib/bundle.mjs";

/**
 * Jobs at once, by default. Nearly every job starts Pyodide, whose start
 * keeps about one and a half cores busy, so a job per core would oversubscribe
 * the machine and slow every job down.
 */
const WIDTH = Math.max(1, Math.round(availableParallelism() * 0.75));

/** Golden cases in a shard: few enough that the shards balance the pool. */
const GOLDEN_SHARD_CASES = 8;

/** Timed jobs at once, in the second phase: few, so that it stays quiet. */
const TIMED_WIDTH = 6;

/** A job still running after this has hung, and fails. */
const JOB_TIMEOUT_MS = 10 * 60_000;

/** The test files, each run as `node scripts/<file>.mjs`. */
const FILES = [
  "smoke-repl-session",
  "smoke-interactions-api",
  "smoke-new-file-level",
  "smoke-worker-protocol",
  "smoke-static-analyze",
  "smoke-level-line",
  "smoke-diagnostics",
  "smoke-python-sources",
  "smoke-explainers",
  "smoke-images",
  "smoke-tables",
  "smoke-tests",
  "smoke-typecheck",
  "smoke-contracts",
  "smoke-contracts-cost",
  "smoke-pandas",
  "smoke-input",
  "smoke-workspace-files",
  "smoke-universe",
  "smoke-examplar",
  "smoke-examplar-build",
  "smoke-bundle",
  "smoke-cli",
  "smoke-golden",
  "smoke-interrupt",
  "smoke-desktop-parity",
];

/**
 * Files whose checks measure real time, for the second phase: a Stop's
 * latency and its retries (smoke-interrupt, smoke-desktop-parity), and the
 * session's reactor clocks and Stop banners, which wait on timers
 * (smoke-repl-session).
 */
const TIMED_FILES = new Set(["smoke-interrupt", "smoke-desktop-parity", "smoke-repl-session"]);

/** The tests made of `section(...)`s, each of which stands alone. */
const SECTIONED = new Set(["smoke-cli", "smoke-examplar-build"]);

/**
 * A sectioned test's sections, as `PLL_SMOKE_ONLY` names them. One that
 * sends a signal or closes a pipe at a moment - the options of smoke-cli's
 * `run` that do - is timed, and waits for the second phase.
 */
function sections(file) {
  const source = readFileSync(join(ROOT, "scripts", `${file}.mjs`), "utf8");
  const found = [];
  const calls = (source.match(/\bsection\(/g) ?? []).length;
  for (const line of source.split("\n")) {
    const start = /if \(section\("?(\w+)"?,/.exec(line);
    if (start) found.push({ id: start[1], timed: false });
    else if (found.length > 0 && /\b(signalAfter|signalAfterStderr|signalAtMs|closeStdoutAfter):/.test(line)) {
      found.at(-1).timed = true;
    }
  }
  // A section this reading missed would never run, and nothing would say.
  if (found.length === 0 || found.length !== calls) {
    throw new Error(`scripts/${file}.mjs: ${calls} section(...) calls, but ${found.length} read as \`if (section(id, ...\``);
  }
  return found;
}

const LOGS = join(ROOT, ".smoke-logs");
const TIMES = join(LOGS, "times.json");

function jobs() {
  const list = [];
  for (const file of FILES) {
    const script = join(ROOT, "scripts", `${file}.mjs`);
    if (SECTIONED.has(file)) {
      for (const { id, timed } of sections(file)) {
        list.push({ name: `${file} [${id}]`, script, env: { PLL_SMOKE_ONLY: id }, timed });
      }
    } else if (file === "smoke-golden") {
      // Each shard one case at a time, so that this pool is the only one.
      const count = Math.ceil(CASES.length / GOLDEN_SHARD_CASES);
      for (let index = 0; index < count; index++) {
        list.push({
          name: `${file} [${index + 1}/${count}]`,
          script,
          env: { PLL_GOLDEN_SHARD: `${index}/${count}`, PLL_GOLDEN_PARALLEL: "1" },
        });
      }
    } else {
      list.push({ name: file, script, env: {}, timed: TIMED_FILES.has(file) });
    }
  }
  return list;
}

function runJob(job) {
  return new Promise((done) => {
    const started = Date.now();
    const child = spawn(process.execPath, [job.script], {
      cwd: ROOT,
      env: { ...process.env, ...job.env },
      stdio: ["ignore", "pipe", "pipe"],
    });
    let output = "";
    child.stdout.on("data", (b) => (output += b));
    child.stderr.on("data", (b) => (output += b));
    const timer = setTimeout(() => {
      output += `\nsmoke: killed after ${JOB_TIMEOUT_MS / 1000}s\n`;
      child.kill("SIGKILL");
    }, JOB_TIMEOUT_MS);
    child.on("close", (code, signal) => {
      clearTimeout(timer);
      const seconds = (Date.now() - started) / 1000;
      const file = join(LOGS, `${job.name.replace(/[^\w-]+/g, "_")}.log`);
      writeFileSync(file, output);
      done({ ...job, code: code ?? signal, ok: code === 0, seconds, output, file });
    });
  });
}

/** Run `list` with at most `width` at once, the longest-running first. */
async function pool(list, width, times, report) {
  const queue = [...list].sort((a, b) => (times[b.name] ?? 0) - (times[a.name] ?? 0));
  const results = [];
  await Promise.all(
    Array.from({ length: Math.min(width, queue.length) }, async () => {
      while (queue.length > 0) {
        const result = await runJob(queue.shift());
        report(result);
        results.push(result);
      }
    }),
  );
  return results;
}

async function main() {
  const args = process.argv.slice(2);
  const serial = args.includes("--serial");
  const filters = args.filter((a) => !a.startsWith("--"));
  const chosen = jobs().filter((job) => filters.length === 0 || filters.some((f) => job.name.includes(f)));
  if (chosen.length === 0) {
    console.error(`no job matches ${filters.join(" ")}`);
    process.exit(64);
  }
  mkdirSync(LOGS, { recursive: true });
  let times = {};
  try {
    times = existsSync(TIMES) ? JSON.parse(readFileSync(TIMES, "utf8")) : {};
  } catch {
    times = {};
  }

  const asked = Number(/^--jobs=(\d+)$/.exec(args.find((a) => a.startsWith("--jobs=")) ?? "")?.[1]);
  const width = serial ? 1 : asked > 0 ? asked : WIDTH;
  const started = Date.now();
  let finished = 0;
  const report = (r) => {
    finished += 1;
    const mark = r.ok ? "ok  " : "FAIL";
    console.log(`${mark} ${r.seconds.toFixed(1).padStart(6)}s  ${r.name}  (${finished}/${chosen.length})`);
  };
  const results = [
    ...(await pool(chosen.filter((job) => !job.timed), width, times, report)),
    // The timed jobs, on a machine with nothing else to do.
    ...(await pool(chosen.filter((job) => job.timed), serial ? 1 : TIMED_WIDTH, times, report)),
  ];
  const wall = (Date.now() - started) / 1000;

  for (const r of results) times[r.name] = r.seconds;
  writeFileSync(TIMES, JSON.stringify(times, null, 2) + "\n");

  const failed = results.filter((r) => !r.ok);
  for (const r of failed) {
    console.log(`\n===== ${r.name} (exit ${r.code}) - ${r.file}\n${r.output.trimEnd()}`);
  }
  const busy = results.reduce((sum, r) => sum + r.seconds, 0);
  console.log(
    `\nsmoke: ${results.length - failed.length} of ${results.length} passed in ${wall.toFixed(1)}s` +
      ` (${busy.toFixed(1)}s of tests, ${width === 1 ? "one at a time" : `up to ${width} at once`})`,
  );
  if (failed.length > 0) {
    console.log(`smoke: FAILED - ${failed.map((r) => r.name).join(", ")}`);
    process.exit(1);
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
