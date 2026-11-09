#!/usr/bin/env node
/**
 * What a contract costs as a program grows (bootstrap/contracts.py): the
 * checks a run makes are counted at the leaves, `_PllClassContract.accepts`,
 * and must grow as the program's own work does - not once more for every
 * call that a value, or a function, has already crossed.
 */
import { expect, passed, section } from "./lib/check.mjs";
import { bootPll } from "./lib/pyodide.mjs";

const pyodide = await bootPll();
const pllCall = pyodide.globals.get("_pll_call");

pyodide.runPython(`
_pll_test_checks = 0
_pll_test_accepts = _PllClassContract.accepts

def _pll_test_counted(self, value):
    global _pll_test_checks
    _pll_test_checks += 1
    return _pll_test_accepts(self, value)

_PllClassContract.accepts = _pll_test_counted

_pll_test_wraps = 0
_pll_test_wrapped = _pll_wrapped

def _pll_wrapped(function, source, blame):
    global _pll_test_wraps
    _pll_test_wraps += 1
    return _pll_test_wrapped(function, source, blame)
`);

let runs = 0;
/** Run `source` at `level`: its output, its error, the leaf checks it made and the wrappers it asked for. */
function ran(source, level = "beginner", session = `cost-${(runs += 1)}`) {
  pyodide.runPython("_pll_test_checks = 0\n_pll_test_wraps = 0");
  const result = JSON.parse(pllCall("_pll_run_file", JSON.stringify([source, "lab.py", session, level, false])));
  return {
    stdout: result.stdout,
    error: result.error ?? null,
    checks: pyodide.runPython("_pll_test_checks"),
    wraps: pyodide.runPython("_pll_test_wraps"),
  };
}

const lines = (...rows) => rows.join("\n") + "\n";
const NODE = ["@dataclass", "class Node[T]:", "    first: T", '    rest: "Node[T] | None"', ""];
const BUILD = ["def build(k):", "    return None if k == 0 else Node(k, build(k - 1))", ""];
const LENGTH = ["def length(l: Node[int] | None) -> int:", "    return 0 if l is None else 1 + length(l.rest)", ""];

/** Whether the checks `program(n)` makes grow no faster than n. */
function linear(what, program, small, large, level) {
  const a = ran(program(small), level);
  const b = ran(program(large), level);
  expect(a.error === null && b.error === null, `${what}: ${a.error?.message ?? ""} ${b.error?.message ?? ""}`);
  expect(b.checks <= (large / small) * a.checks + 8, `${what}: ${a.checks} checks at ${small}, ${b.checks} at ${large}`);
  return [a, b];
}

if (section(1, "a recursive generic dataclass is checked by one contract, however deep the value")) {
  const contracts = (n) => {
    ran(lines(...NODE, ...BUILD, ...LENGTH, `print(length(build(${n})))`), "beginner", "cost-depth");
    return pyodide.runPython(
      "import gc\nnode = _pll_get_session('cost-depth')['Node']\nsum(1 for o in gc.get_objects() if isinstance(o, _PllDataContract) and o.cls is node)",
    );
  };
  const few = contracts(3);
  const many = contracts(150);
  expect(many <= few, `contracts for Node: ${few} after 3 cells, ${many} after 150`);
  // A type alias that names itself, given an ordinary value.
  const nested = ran(lines("type Nested = list[Nested] | int", "", "def depth(x: Nested) -> int:", "    return 0", "", "print(depth([[1], 2]))"), "advanced");
  expect(nested.stdout === "0\n" && nested.error === null, `type Nested = list[Nested] | int: ${nested.stdout} ${nested.error?.errorType}`);
  // A file run again reads its names in quotes in the new run.
  const PLAIN = ["@dataclass", "class Cell:", "    first: int", '    rest: "Cell | None"', "", "print(Cell(1, Cell(2, None)).rest.first)"];
  for (const run of ["first", "again"]) {
    const rerun = ran(lines(...PLAIN), "beginner", "cost-rerun");
    expect(rerun.stdout === "2\n" && rerun.error === null, `a rerun, ${run}: ${rerun.stdout} ${rerun.error?.message}`);
  }
  console.log("    the same contracts after a long value as after a short one; an alias that names itself; a rerun");
}

if (section(2, "a value is checked to its end however deep it is, and a failure found in one pass")) {
  const LONG = (n, last) => [
    ...NODE,
    "def build(n):",
    `    l = Node(${last}, None)`,
    "    for k in range(n - 1):",
    "        l = Node(k, l)",
    "    return l",
    "",
    "def head(l: Node[int] | None) -> int:",
    "    return l.first",
    "",
    `print(head(build(${n})))`,
  ];
  const deep = ran(lines(...LONG(1000, 0)), "intermediate");
  expect(deep.stdout === "998\n" && deep.error === null, `1000 cells: ${deep.stdout} ${deep.error?.errorType} ${deep.error?.message}`);
  const broken = (n) => ran(lines(...LONG(n, '"x"')), "intermediate");
  const [a, b] = [broken(100), broken(200)];
  for (const [n, run] of [[100, a], [200, b]]) {
    expect(
      run.error?.errorType === "TypeMismatch" && run.error?.facts?.check?.value === '"x"' && run.error?.facts?.check?.path?.length === n + 1,
      `the last of ${n} cells: ${run.error?.errorType} ${run.error?.facts?.check?.value} ${run.error?.facts?.check?.path?.length}`,
    );
  }
  expect(b.checks <= 2 * a.checks + 8, `finding it: ${a.checks} checks at 100 cells, ${b.checks} at 200`);
  // A list that contains itself, under a type that names itself, is
  // taken as what it is - as a dataclass that contains itself already was.
  const cyclic = ran(
    lines("type Tree = list[Tree] | int", "", "def size(t: Tree) -> int:", "    return 1", "", "t = []", "t.append(t)", "print(size(t))"),
    "advanced",
  );
  expect(cyclic.stdout === "1\n" && cyclic.error === null, `a list in itself: ${cyclic.stdout} ${cyclic.error?.errorType}`);
  // A union's members are tried in order: a name defined further down is
  // not looked up for a value an earlier member takes.
  const later = ran(lines("from typing import Union", "", 'counts: dict[Union[int, "Later"], int] = {1: 2}', "print(len(counts))"), "advanced");
  expect(later.stdout === "1\n" && later.error === null, `a name not yet defined, after int: ${later.stdout} ${later.error?.message}`);
  // Two members shaped like the value, deeper than Python's stack.
  const nest = ran(
    lines(
      "type Nest = list[Nest] | list[int]",
      "",
      "def size(x: Nest) -> int:",
      "    return 0",
      "",
      "x = [1]",
      "for i in range(3000):",
      "    x = [x]",
      "print(size(x))",
    ),
    "advanced",
  );
  expect(nest.stdout === "0\n" && nest.error === null, `3000 lists deep, two members shaped: ${nest.stdout} ${nest.error?.errorType}`);
  console.log("    1000 cells checked; the bad one found in one pass; a list in itself accepted");
}

const LOOPED = (n, last) => [
  ...NODE,
  "def build(n):",
  `    l = Node(${last}, None)`,
  "    for k in range(n - 1):",
  "        l = Node(k, l)",
  "    return l",
  "",
];

if (section(3, "a generic function's copy of a value is made however deep the value is")) {
  const head = ran(
    lines(...LOOPED(1200, 7), "def head[T](l: Node[T] | None) -> T | None:", "    return None if l is None else l.first", "", "print(head(build(1200)))"),
    "intermediate",
  );
  expect(head.stdout === "1198\n" && head.error === null, `1200 cells: ${head.stdout} ${head.error?.errorType} ${head.error?.message}`);
  console.log("    1200 cells copied for a generic function");
}

console.log(passed() ? "\nsmoke-contracts-cost: ok" : "\nsmoke-contracts-cost: FAILED");
if (!passed()) process.exitCode = 1;
