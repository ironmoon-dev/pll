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

_pll_test_seals = 0
_pll_test_wrap = _PllSeal.wrap

def _pll_test_sealing(self, value):
    global _pll_test_seals
    _pll_test_seals += 1
    return _pll_test_wrap(self, value)

_PllSeal.wrap = _pll_test_sealing

_pll_test_calls = 0
_pll_test_call = _PllCall.__init__

def _pll_test_calling(self, *args):
    global _pll_test_calls
    _pll_test_calls += 1
    _pll_test_call(self, *args)

_PllCall.__init__ = _pll_test_calling
`);

let runs = 0;
/** Run `source` at `level`: its output, its error, the leaf checks it made, the wrappers it asked for, the values it sealed and the calls through wrappers. */
function ran(source, level = "beginner", session = `cost-${(runs += 1)}`) {
  pyodide.runPython("_pll_test_checks = 0\n_pll_test_wraps = 0\n_pll_test_seals = 0\n_pll_test_calls = 0");
  const result = JSON.parse(pllCall("_pll_run_file", JSON.stringify([source, "lab.py", session, level, false])));
  return {
    stdout: result.stdout,
    error: result.error ?? null,
    checks: pyodide.runPython("_pll_test_checks"),
    wraps: pyodide.runPython("_pll_test_wraps"),
    seals: pyodide.runPython("_pll_test_seals"),
    calls: pyodide.runPython("_pll_test_calls"),
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

if (section(4, "a value a contract accepted is not checked again")) {
  linear("a recursive function over Node[int]", (n) => lines(...NODE, ...BUILD, ...LENGTH, `print(length(build(${n})))`), 100, 200);
  linear(
    "building Node[int] by consing",
    (n) => lines(...NODE, "def build(k: int) -> Node[int] | None:", "    return None if k == 0 else Node(k, build(k - 1))", "", `print(build(${n}) is not None)`),
    100,
    200,
  );
  // A field set, or deleted, after the check is checked again.
  const changed = (change) =>
    ran(lines(...NODE, ...LENGTH, "l = Node(1, Node(2, None))", "print(length(l))", change, "print(length(l))"), "advanced");
  for (const change of ['l.rest.first = "x"', "del l.rest.first"]) {
    const after = changed(change);
    expect(after.stdout === "2\n" && after.error?.errorType === "TypeMismatch", `after \`${change}\`: ${after.stdout} ${after.error?.message}`);
  }
  // A list inside one is read again each time: it can change unseen.
  const listed = ran(
    lines(
      "@dataclass",
      "class Box[T]:",
      "    item: T",
      "",
      "def size(b: Box[list[int]]) -> int:",
      "    return len(b.item)",
      "",
      "b = Box([1])",
      "print(size(b))",
      'b.item.append("x")',
      "print(size(b))",
    ),
    "advanced",
  );
  expect(listed.stdout === "1\n" && listed.error?.errorType === "TypeMismatch", `a list changed in place: ${listed.stdout} ${listed.error?.message}`);
  // Made again by its own `__init__`, or changed through a subclass of a
  // frozen one that lets it: seen too.
  const BOX = ["@dataclass", "class Box[T]:", "    item: T", "", "    def reset(self, item):", "        self.__init__(item)", ""];
  const TAKE = ["def take(b: Box[int]) -> int:", "    return 0", ""];
  const reinit = ran(lines(...BOX, ...TAKE, "b = Box(1)", "print(take(b))", 'b.reset("s")', "print(take(b))"), "advanced");
  expect(reinit.stdout === "0\n" && reinit.error?.errorType === "TypeMismatch", `made again: ${reinit.stdout} ${reinit.error?.message}`);
  const loose = ran(
    lines(
      "@dataclass(frozen=True)",
      "class Box[T]:",
      "    item: T",
      "",
      "class Loose(Box):",
      "    def __setattr__(self, name, value):",
      "        object.__setattr__(self, name, value)",
      "",
      ...TAKE,
      "b = Loose(1)",
      "print(take(b))",
      'b.item = "s"',
      "print(take(b))",
    ),
    "advanced",
  );
  expect(loose.stdout === "0\n" && loose.error?.errorType === "TypeMismatch", `a frozen one let loose: ${loose.stdout} ${loose.error?.message}`);
  console.log("    each cell checked once; a change to one is seen");
}

if (section(5, "where nothing can change it, a list checked once is not walked again")) {
  linear(
    "a helper given the list in a loop",
    (n) =>
      lines(
        "def item(l: list[int], i: int) -> int:",
        "    return l[i]",
        "",
        "def total(l: list[int]) -> int:",
        "    s = 0",
        "    for i in range(len(l)):",
        "        s = s + item(l, i)",
        "    return s",
        "",
        `print(total(list(range(${n}))))`,
      ),
    100,
    200,
    "intermediate",
  );
  // Where a list can change, it is checked again.
  const changed = ran(
    lines("def total(l: list[int]) -> int:", "    return len(l)", "", "xs = [1, 2]", "print(total(xs))", 'xs.append("x")', "print(total(xs))"),
    "advanced",
  );
  expect(changed.stdout === "2\n" && changed.error?.errorType === "TypeMismatch", `a list changed at advanced: ${changed.stdout} ${changed.error?.message}`);
  // None is not a list that was remembered.
  const none = ran(lines("def size(l: list[int]) -> int:", "    return 0", "", "print(size([1]))", "print(size(None))"), "intermediate");
  expect(none.stdout === "0\n" && none.error?.errorType === "TypeMismatch", `None as a list: ${none.stdout} ${none.error?.errorType}`);
  // The next run lets go of an earlier run's lists.
  ran(lines("xs: list[int] = [1, 2, 3]", "print(len(xs))"), "intermediate", "cost-held");
  ran(lines("print(0)"), "intermediate", "cost-held");
  const held = pyodide.runPython("sum(len(accepted.held) for accepted in globals().get('_PLL_HOLDING', ()))");
  expect(held === 0, `values still held after the next run: ${held}`);
  // A teaching level doesn't keep a deque from changing.
  const deque = ran(
    lines("from collections import deque", "", "def size(d: deque[int]) -> int:", "    return len(d)", "", "d = deque([1])", "print(size(d))", 'd.append("x")', "print(size(d))"),
    "intermediate",
  );
  expect(deque.stdout === "1\n" && deque.error?.errorType === "TypeMismatch", `a deque changed at intermediate: ${deque.stdout} ${deque.error?.message}`);
  console.log("    each list checked once at intermediate; checked again where it can change");
}

if (section(6, "a function passed on through the same parameter is not wrapped again")) {
  const APPLY = [
    "def apply_n(f: Callable[[int], int], k: int, x: int) -> int:",
    "    return x if k == 0 else apply_n(f, k - 1, f(x))",
    "",
    "def add1(x: int) -> int:",
    "    return x + 1",
    "",
  ];
  linear("apply_n", (n) => lines(...APPLY, `print(apply_n(add1, ${n}, 0))`), 100, 200);
  // As deep as the same program goes unannotated: wrappers do not pile up
  // on the stack either.
  const deep = ran(lines(...APPLY, "print(apply_n(add1, 900, 0))"));
  expect(deep.stdout === "900\n" && deep.error === null, `900 deep: ${deep.stdout} ${deep.error?.errorType} ${deep.error?.message}`);
  // Still checked at each call, and still blamed on the caller.
  const broken = ran(
    lines(...APPLY, "def bad(x: int) -> int:", '    return "s" if x == 5 else x + 1', "", "print(apply_n(bad, 10, 0))"),
  );
  expect(
    broken.error?.errorType === "TypeMismatch" && broken.error?.facts?.check?.blamed?.name === "bad",
    `a result broken on the 6th call: ${broken.error?.errorType} ${JSON.stringify(broken.error?.facts?.check?.blamed)}`,
  );
  console.log("    one wrapper for the crossings that repeat; each call still checked");
}

if (section(7, "a method called from one line is put under its contract once")) {
  const calls = (n) =>
    ran(
      lines(
        "@dataclass",
        "class Box:",
        "    v: int",
        "",
        "    def get(self) -> int:",
        "        return self.v",
        "",
        "def total(b: Box, k: int) -> int:",
        "    s = 0",
        "    for i in range(k):",
        "        s = s + b.get()",
        "    return s",
        "",
        `print(total(Box(1), ${n}))`,
      ),
      "intermediate",
    );
  const [few, many] = [calls(10), calls(1000)];
  expect(many.stdout === "1000\n" && many.error === null, `1000 calls: ${many.stdout} ${many.error?.message}`);
  expect(many.wraps === few.wraps, `wrappers: ${few.wraps} for 10 calls, ${many.wraps} for 1000`);
  console.log("    one wrapper for the line, however many calls it makes");
}

if (section(8, "a function passed between functions with the same parameter types is not wrapped again either")) {
  const PING = (other) => [
    "def ping(f: Callable[[int], int], k: int, x: int) -> int:",
    "    return x if k == 0 else pong(f, k - 1, f(x))",
    "",
    `def pong(f: Callable[[int], ${other}], k: int, x: int) -> int:`,
    "    return x if k == 0 else ping(f, k - 1, f(x))",
    "",
    "def inc(x):",
    "    return x + 1",
    "",
  ];
  linear("ping and pong", (n) => lines(...PING("int"), `print(ping(inc, ${n}, 0))`), 100, 200);
  const deep = ran(lines(...PING("int"), "print(ping(inc, 900, 0))"));
  expect(deep.stdout === "900\n" && deep.error === null, `900 deep: ${deep.stdout} ${deep.error?.errorType} ${deep.error?.message}`);
  // pong says f gives back a str: the first result it sees is ping's to answer for.
  const broken = ran(lines(...PING("str"), "print(ping(inc, 6, 0))"));
  expect(
    broken.error?.errorType === "TypeMismatch" && broken.error?.facts?.check?.blamed?.name === "ping",
    `pong's str broken: ${broken.error?.errorType} ${JSON.stringify(broken.error?.facts?.check?.blamed)}`,
  );
  console.log("    the same checks, kept once; the same blame");
}

if (section(9, "a variable's annotation with a name in quotes is read in each run")) {
  const DOGS = ["@dataclass", "class Dog:", "    name: str", "", 'pets: list["Dog"] = [Dog("a")]', "print(len(pets))"];
  for (const [run, session] of [["first", "cost-dogs"], ["again", "cost-dogs"], ["in another file", "cost-dogs-2"]]) {
    const dogs = ran(lines(...DOGS), "beginner", session);
    expect(dogs.stdout === "1\n" && dogs.error === null, `run ${run}: ${dogs.stdout} ${dogs.error?.message}`);
  }
  // Through a type alias, after the class it names is made again.
  const key = "cost-pack";
  ran(lines("@dataclass", "class Dog:", "    name: str", "", 'type Pack = list["Dog"]', 'p: Pack = [Dog("a")]', "print(len(p))"), "advanced", key);
  pllCall("_pll_repl_eval", JSON.stringify(["@dataclass\nclass Dog:\n    name: str\n", key, "advanced"]));
  const packed = JSON.parse(pllCall("_pll_repl_eval", JSON.stringify(['q: Pack = [Dog("b")]\nprint(len(q))', key, "advanced"])));
  expect(packed.stdout === "1\n" && !packed.error, `an alias's quoted name after Dog is made again: ${packed.stdout} ${packed.error?.message}`);
  // Each annotation's own words in what it says.
  const words = ran(lines("Numbers = list[int]", "xs: Numbers = [1]", "ys: list[int] = 5"), "advanced");
  expect(words.error?.facts?.check?.expected?.[0] === "list[int]", `ys's annotation as written: ${JSON.stringify(words.error?.facts?.check?.expected)}`);
  console.log("    each run's own Dog, through an alias too; each annotation in its own words");
}

if (section(10, "a union inside a union takes a value as one of its members would")) {
  const result = ran(lines("type Opt[X] = list[X] | None", "", "def wrap[T](x: T) -> Opt[T] | int:", "    return [x]", "", "print(wrap(1))"));
  expect(result.stdout === "[1]\n" && result.error === null, `given back through an alias of a union: ${result.stdout} ${result.error?.message}`);
  const given = ran(lines("type Maybe[X] = X | None", "", "def keep[T](x: Maybe[T] | int) -> int:", "    return 0", "", 'print(keep("s"))'));
  expect(given.stdout === "0\n" && given.error === null, `given through an alias of a union: ${given.stdout} ${given.error?.message}`);
  console.log("    a generic function's T through an alias of a union, both ways");
}

if (section(11, "a generic function calling itself keeps the seals it is in")) {
  const LENGTH_T = ["def length[T](l: Node[T] | None) -> int:", "    return 0 if l is None else 1 + length(l.rest)", ""];
  const [a, b] = [100, 200].map((n) => ran(lines(...LOOPED(n, 0), ...LENGTH_T, `print(length(build(${n})))`), "intermediate"));
  expect(a.stdout === "100\n" && b.stdout === "200\n", `length: ${a.stdout} ${b.stdout} ${b.error?.message}`);
  expect(b.seals <= 2 * a.seals + 8, `seals made: ${a.seals} at 100, ${b.seals} at 200`);
  // Still parametric: what it gives back as a T, it was given as one.
  const last = ran(
    lines(...LOOPED(50, 7), "def last[T](l: Node[T]) -> T:", "    return l.first if l.rest is None else last(l.rest)", "", "print(last(build(50)))"),
    "intermediate",
  );
  expect(last.stdout === "7\n" && last.error === null, `last: ${last.stdout} ${last.error?.message}`);
  // A value can reach it past its type variables (`object`): not kept.
  const past = ran(lines("def f[T](x: T, y: object, k: int) -> T:", "    return y if k == 0 else f(x, x, k - 1)", "", "print(f(1, 2, 3))"), "intermediate");
  expect(past.error?.errorType === "TypeMismatch", `given past T: ${past.stdout} ${past.error?.errorType}`);
  // A U given back as a T is still refused.
  const swapped = ran(lines("def g[T, U](x: T, y: U, k: int) -> T:", "    return x if k == 0 else g(y, x, k - 1)", "", 'print(g(1, "a", 1))'), "intermediate");
  expect(swapped.error?.errorType === "TypeMismatch", `T and U swapped: ${swapped.stdout} ${swapped.error?.errorType}`);
  // None given to itself as a list is refused.
  const none = ran(lines("def f[T](l: list[T], k: int) -> int:", "    return 0 if k == 0 else f(None, k - 1)", "", "print(f([1], 1))"), "intermediate");
  expect(none.error?.errorType === "TypeMismatch", `None as a list[T]: ${none.stdout} ${none.error?.errorType}`);
  // What a call it made sealed, and kept past its end, is not its own.
  const stashed = ran(
    lines(
      "stash = None",
      "",
      "def f[T](x: T, k: int) -> T:",
      "    global stash",
      "    if k == 0:",
      "        stash = x",
      "        return x",
      "    ignored = f(0, k - 1)",
      "    return stash",
      "",
      "print(f(1, 1))",
    ),
    "intermediate",
  );
  expect(stashed.error?.errorType === "TypeMismatch", `an inner call's seal given back: ${stashed.stdout} ${stashed.error?.errorType} ${stashed.error?.message}`);
  console.log("    one seal per value along the recursion; still only what it was given");
}

if (section(12, "a generic function's copy of a dataclass fills in a field only when it is read")) {
  const IS_EMPTY = ["def is_empty[T](l: Node[T] | None) -> bool:", "    return l is None", ""];
  const COUNT = ["def length(l: Node[int] | None) -> int:", "    return 0 if is_empty(l) else 1 + length(l.rest)", ""];
  const [a, b] = [100, 200].map((n) => ran(lines(...LOOPED(n, 0), ...IS_EMPTY, ...COUNT, `print(length(build(${n})))`), "intermediate"));
  expect(a.stdout === "100\n" && b.stdout === "200\n", `length: ${a.stdout} ${b.stdout} ${b.error?.message}`);
  expect(b.seals <= 2 * a.seals + 8, `seals made: ${a.seals} at 100, ${b.seals} at 200`);
  const second = ran(lines(...LOOPED(5, 7), "def second[T](l: Node[T]) -> T:", "    return l.rest.first", "", "print(second(build(5)))"), "intermediate");
  expect(second.stdout === "2\n" && second.error === null, `second: ${second.stdout} ${second.error?.message}`);
  const BOX = ["@dataclass", "class Box[T]:", "    item: T", ""];
  // What it copies changes after the call: the copy holds what it held.
  const later = ran(
    lines(...BOX, "def later[T](b: Box[T]) -> Callable[[], T]:", "    return lambda: b.item", "", "b = Box(5)", "get = later(b)", "del b.item", "print(get())"),
    "intermediate",
  );
  expect(later.stdout === "5\n" && later.error === null, `read after a change: ${later.stdout} ${later.error?.message}`);
  const copied = ran(lines("import copy", "", ...BOX, "def dup[T](b: Box[T]) -> Box[T]:", "    return copy.copy(b)", "", "print(dup(Box(5)).item)"), "intermediate");
  expect(copied.stdout === "5\n" && copied.error === null, `a copy of the copy: ${copied.stdout} ${copied.error?.message}`);
  // A field with a default, which the class holds too.
  const OPT = ["@dataclass", "class Opt[T]:", "    item: T", "    count: int = 0", ""];
  const counted = ran(lines(...OPT, "def count[T](o: Opt[T]) -> int:", "    return o.count", "", "print(count(Opt(1, 5)))"), "intermediate");
  expect(counted.stdout === "5\n" && counted.error === null, `a field with a default: ${counted.stdout} ${counted.error?.message}`);
  const SIZE = ["    n = 0", "    m = l", "    while m is not None:", "        n = n + 1", "        m = m.rest", "    return n", ""];
  // A field that names the class again and has a default is filled at once: by a walk, however long the list.
  const DNODE = ["@dataclass", "class DNode[T]:", "    first: T", '    rest: "DNode[T] | None" = None', ""];
  const defaulted = ran(
    lines(...DNODE, "def size[T](l: DNode[T] | None) -> int:", ...SIZE, "l = None", "for i in range(1000):", "    l = DNode(i, l)", "print(size(l))"),
    "intermediate",
  );
  expect(defaulted.stdout === "1000\n" && defaulted.error === null, `a default that names the class: ${defaulted.stdout} ${defaulted.error?.errorType}`);
  // What the function's own contract says decides, not what the value's class says.
  const LOOSER = ["@dataclass", "class Tag[T]:", "    item: T", "    count: int", "", "@dataclass", "class Looser[T](Tag[T]):", "    count: object", ""];
  const looser = ran(lines(...LOOSER, "def g[T](t: Tag[T]) -> int:", "    return 0", "", 'print(g(Looser(1, "x")))'), "intermediate");
  expect(looser.error?.errorType === "TypeMismatch", `a subclass's looser field: ${looser.stdout} ${looser.error?.errorType}`);
  // A part whose changes PLL can't see: each call copies the value whole, once. Building such a
  // list checks the rest of it at each cell, so one call's checks are two calls' less one's.
  const ODD = ["@dataclass", "class Odd[T]:", "    v: T", "", "    def __setattr__(self, name, value):", "        object.__setattr__(self, name, value)", ""];
  const TAGGED = ["@dataclass", "class Tagged[T]:", "    first: T", "    tag: Odd[int]", '    rest: "Tagged[T] | None"', ""];
  const sized = (n, calls) =>
    ran(
      lines(...ODD, ...TAGGED, "def size[T](l: Tagged[T] | None) -> int:", ...SIZE, "l = None", `for i in range(${n}):`, "    l = Tagged(i, Odd(i), l)", ...Array(calls).fill("print(size(l))")),
      "intermediate",
    ).checks;
  const [once100, once200] = [100, 200].map((n) => sized(n, 2) - sized(n, 1));
  expect(once200 <= 2 * once100 + 8, `a part PLL can't watch: ${once100} checks for one call at 100, ${once200} at 200`);
  console.log("    no seal for a field never read; what is read is what a whole copy holds");
}

if (section(13, "a generic function calling itself passes its results back, and its function arguments down, as they are")) {
  const DOUBLE = ["def double(x):", "    return 2 * x", ""];
  const MAPPED = ["def mapped[T, U](f: Callable[[T], U], l: Node[T] | None) -> Node[U] | None:", "    return None if l is None else Node(f(l.first), mapped(f, l.rest))", ""];
  const [a, b] = [100, 200].map((n) => ran(lines(...LOOPED(n, 0), ...DOUBLE, ...MAPPED, `print(mapped(double, build(${n})).first)`), "intermediate"));
  expect(a.stdout === "196\n" && b.stdout === "396\n", `mapped: ${a.stdout} ${b.stdout} ${b.error?.message}`);
  // A call of f at depth d went through d wrappers.
  expect(b.calls <= 2 * a.calls + 8, `calls through wrappers: ${a.calls} at 100, ${b.calls} at 200`);
  expect(b.checks <= 2 * a.checks + 8 && b.seals <= 2 * a.seals + 8, `checks ${a.checks}, ${b.checks}; seals ${a.seals}, ${b.seals}`);
  // Still parametric at any depth, and blamed as before.
  const AT = (k, base, step) => [
    "def mapped[T, U](f: Callable[[T], U], l: Node[T] | None, k: int) -> Node[U] | None:",
    "    if l is None:",
    "        return None",
    "    if k == 0:",
    `        return ${base}`,
    `    return Node(f(l.first), mapped(f, ${step}, k - 1))`,
    "",
    `print(mapped(double, build(8), ${k}))`,
  ];
  const back = ran(lines(...LOOPED(8, 0), ...DOUBLE, ...AT(5, "Node(l.first, None)", "l.rest")), "intermediate");
  expect(back.error?.message === "the first of a Node of the return value of mapped is T (Node), not U", `a T given back as U at depth 5: ${back.error?.message}`);
  const given = ran(lines(...LOOPED(8, 0), ...DOUBLE, ...AT(3, "Node(f(l.first), None)", "Node(0, l.rest) if k == 1 else l.rest")), "intermediate");
  expect(given.error?.message === "argument f of mapped is 0 (int), not T", `a non-T given to f at depth 3: ${given.error?.message}`);
  // A function given down the chain, kept past the call that took it.
  const INC = ["def inc(x):", "    return x + 1", ""];
  const kept = ran(
    lines(...INC, "def repeat[T](f: Callable[[T], T], n: int) -> Callable[[T], T]:", "    if n == 0:", "        return lambda x: x", "    g = repeat(f, n - 1)", "    return lambda x: f(g(x))", "", "print(repeat(inc, 3)(0))"),
    "intermediate",
  );
  expect(kept.stdout === "3\n" && kept.error === null, `f kept past its call: ${kept.stdout} ${kept.error?.message}`);
  // A function f gives back whose argument is a union with T in it: its layers are all kept.
  const UNION = ["def mk(x):", "    return lambda y: x", "", "def walk[T](f: Callable[[T], Callable[[T | int], T]], x: T, y: T, k: int) -> T:", "    if k == 0:", "        return f(x)(y)", "    return walk(f, x, 5 if k == 2 else y, k - 1)", ""];
  const union = ran(lines(...UNION, "print(walk(mk, 1, 0, 3))"), "intermediate");
  expect(union.stdout === "1\n" && union.error === null, `a union in what f gives back: ${union.stdout} ${union.error?.message}`);
  // A function f gives back has T in it: its layers are all kept, and it works past the calls.
  const MK = ["def mk(v):", "    return lambda y: y", ""];
  const returned = ran(
    lines(...MK, "def app[T](f: Callable[[T], Callable[[T], T]], x: T, k: int) -> Callable[[T], T]:", "    if k == 0:", "        return f(x)", "    return app(f, x, k - 1)", "", "print(app(mk, 1, 2)(7))"),
    "intermediate",
  );
  expect(returned.stdout === "7\n" && returned.error === null, `a function f gives back: ${returned.stdout} ${returned.error?.message}`);
  // A result a call changed in place, where PLL can't see it, is checked again.
  const DEQUE = ["from collections import deque", ""];
  const changed = ran(
    lines(...DEQUE, "def f[T](n: int) -> deque[T]:", "    if n == 0:", "        return deque()", "    d = f(n - 1)", "    d.append(5)", "    return d", "", "print(f(1))"),
    "intermediate",
  );
  expect(changed.error?.message === "item 0 of the return value of f is 5 (deque), not T", `a result changed in place: ${changed.stdout} ${changed.error?.message}`);
  // So is an argument: the call that changed it is blamed, at its own return, as LSL blames it.
  const argument = ran(
    lines(...DEQUE, "def f[T](d: deque[T], n: int) -> T:", "    if n == 0:", "        return d[-1]", "    d.append(5)", "    return f(d, n - 1)", "", "print(f(deque([1]), 1))"),
    "intermediate",
  );
  expect(
    argument.error?.message === "the return value of f is 5 (int), not T" && argument.error?.facts?.check?.returned_at === 7,
    `an argument changed in place: ${argument.error?.message} at line ${argument.error?.facts?.check?.returned_at}`,
  );
  // A result's part that is shared, not copied, changed in place: checked again.
  const shared = ran(
    lines(...DEQUE, "def push(d, v):", "    d.append(v)", "", "def f[T](n: int) -> tuple[list[T], deque[int]]:", "    if n == 0:", "        return ([], deque([1]))", "    r = f(n - 1)", '    push(r[1], "x")', "    return r", "", "print(f(1))"),
    "intermediate",
  );
  expect(shared.error?.message === 'item 1 of item 1 of the return value of f is "x" (tuple), not int', `a shared part changed in place: ${shared.stdout} ${shared.error?.message}`);
  // f given two arguments: a layer checks both before the next, so the one refused is the one the layers it stands for refuse.
  const order = ran(
    lines("def first(a, b):", "    return a", "", "def app[T](g: Callable[[T, T], T], x: T, k: int) -> T:", "    if k == 0:", "        return g(x, 7)", "    return app(g, 5 if k == 1 else x, k - 1)", "", "print(app(first, 1, 2))"),
    "intermediate",
  );
  expect(order.error?.message === "argument g of app is 7 (int), not T", `two arguments, each refused at its own layer: ${order.error?.message}`);
  // An argument of f with no type variable in it, refused where the layers it stands for refuse it, as precisely.
  const precise = ran(
    lines("def first(a, b):", "    return a", "", "def app[T](g: Callable[[T, int | None], T], x: T, k: int) -> T:", "    if k == 0:", "        return g(x, True)", "    return app(g, x, k - 1)", "", "print(app(first, 1, 2))"),
    "intermediate",
  );
  expect(precise.error?.message === "argument g of app is True (bool), not int", `a union argument refused at depth 2: ${precise.error?.message}`);
  // A deque is copied again for each call to itself, as LSL copies it: what one call adds, the other doesn't see.
  const own = ran(
    lines(...DEQUE, "def f[T](d: deque[T], k: int) -> int:", "    if k == 0:", "        d.append(d[0])", "        return 0", "    n = f(d, k - 1)", "    return len(d) + n", "", "print(f(deque([1]), 1))"),
    "intermediate",
  );
  expect(own.stdout === "1\n" && own.error === null, `each call's own copy of a deque: ${own.stdout} ${own.error?.message}`);
  // A value an inner call sealed, reaching an outer call's wrapper past its annotations: as before.
  const inner = ran(
    lines("stash = None", "", "def get(v):", "    return stash", "", "def app[T](g: Callable[[T], T], a: T, b: T, k: int) -> T:", "    global stash", "    if k == 0:", "        stash = b", "        return g(a)", "    return app(g, a, 5, k - 1)", "", "r = app(get, 1, 2, 1)"),
    "intermediate",
  );
  expect(inner.error?.message === "the return value of app is T (T), not T", `an inner call's value through a global: ${inner.error?.message}`);
  // Where it is not LSL's: a call can give back as T what a call it is
  // inside holds as T, reached past its annotations - here, a global, for a
  // value and for a function.
  const stashedG = ran(
    lines("stash = None", "", "def ident(v):", "    return v", "", "def app[T](g: Callable[[T], T], x: T, k: int) -> T:", "    global stash", "    if k == 0:", "        return stash(x)", "    stash = g", "    ignored = app(g, 5, k - 1)", "    return x", "", "print(app(ident, 1, 1))"),
    "intermediate",
  );
  expect(stashedG.stdout === "1\n" && stashedG.error === null, `an outer call's g, given an inner call's T: ${stashedG.stdout} ${stashedG.error?.message}`);
  const stashed = ran(
    lines("stash = None", "", "def f[T](x: T, k: int) -> T:", "    global stash", "    if k == 1:", "        stash = x", "        return f(x, 0)", "    return stash", "", "print(f(1, 1))"),
    "intermediate",
  );
  expect(stashed.stdout === "1\n" && stashed.error === null, `an outer call's T, through a global: ${stashed.stdout} ${stashed.error?.message}`);
  console.log("    one wrapper on f however deep; linear checks; the same blame at depth; the one way it differs from LSL");
}

console.log(passed() ? "\nsmoke-contracts-cost: ok" : "\nsmoke-contracts-cost: FAILED");
if (!passed()) process.exitCode = 1;
