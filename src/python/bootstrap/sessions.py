# Sessions and output.
#
# Each Python file gets its own session, keyed by an opaque string the host
# chooses (typically the document URI). Sessions hold their own globals
# dict, so file A's `data = ...` doesn't leak into file B's REPL prompt.
# `_pll_run_file` resets the addressed session's globals to the baseline
# template before executing; `_pll_repl_eval` does NOT reset, so REPL
# input keeps the names defined by the most recent Run File of the same
# session. The host ends a session, with `_pll_end_session`, when its file
# is closed.
#
# Output - text, images, tables - goes through `_pll_push`, live to the host
# during a file run and collected otherwise, so it arrives in the order the
# program produced it.

import contextlib
import json as _pll_json
import keyword as _pll_keyword
import re as _pll_re
import sys as _sys
import types as _pll_types

# Must match PLL_WORK_DIR in pyodide/workspace.ts. Sibling files are mounted
# here and it is cwd, so open("cars.csv") works. It must not sit first on
# sys.path or a neighboring pandas.py wins over the real package.
_PLL_WORK_DIR = "/home/pyodide/pll_workspace"

def _pll_protect_import_path():
    """Keep sibling .py files from shadowing installed packages.

    Python puts '' (cwd) first on sys.path. After chdir to the work dir,
    import pandas would load a mounted pandas.py. Drop the empty entry,
    append the work dir so unique sibling modules still import, and evict
    anything already loaded from that folder (a failed pandas.py import
    leaves a poisoned sys.modules entry).
    """
    while "" in _sys.path:
        _sys.path.remove("")
    while _PLL_WORK_DIR in _sys.path:
        _sys.path.remove(_PLL_WORK_DIR)
    _sys.path.append(_PLL_WORK_DIR)
    prefix = _PLL_WORK_DIR + "/"
    for name, mod in list(_sys.modules.items()):
        filename = getattr(mod, "__file__", None)
        if isinstance(filename, str) and filename.startswith(prefix):
            _sys.modules.pop(name, None)

# Per-session modules, keyed by session_key (e.g. document URI): a session's
# globals are its module's `__dict__`. Created lazily; initialized from
# `_pll_initial_globals`.
_pll_sessions = {}

# The "template" globals used to seed each new session and to reset a
# session at the start of every Run File. Populated by `install.py`
# at the end of bootstrap so the template includes the PLL image
# library + the auto-display helper.
_pll_initial_globals = {"__name__": "__main__", "__builtins__": __builtins__}

# The modules a session's next Run File gives its program, by the names its
# `#bundle` lines give them: made by `_pll_bundle_load` (bundle.py) just
# before the run, and taken by `_pll_run_file`.
_pll_session_bundles = {}

# A `#bundle <name> <url>` line, as `bundles.ts` reads it: a whole line,
# whose address has a scheme, so a comment that only uses the word is not
# one.
_PLL_BUNDLE_LINE_RE = _pll_re.compile(r"^#\s*bundle\s+(\S+)\s+(\S+://\S*)\s*$")
_PLL_BUNDLE_NAME_RE = _pll_re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _pll_bundle_lines(code):
    """The names `code`'s `#bundle` lines give it, each with its 1-based
    line. Only a name a program can use counts: the host refuses a line
    with any other before the program runs."""
    names = {}
    for number, line in enumerate(code.splitlines(), 1):
        found = _PLL_BUNDLE_LINE_RE.match(line.strip())
        if found is None:
            continue
        name = found.group(1)
        if _PLL_BUNDLE_NAME_RE.fullmatch(name) and not _pll_keyword.iskeyword(name):
            names.setdefault(name, number)
    return names

# Display emissions captured during the most recent `_pll_run_file` /
# `_pll_repl_eval` call. The host drains this list after the call.
# Each entry is the event the host shows (`{"kind": "stdout"|"stderr", "text":
# ...}`, `{"kind": "image", ...}`, or `{"kind": "table", ...}`) so the host can
# dispatch by kind while preserving the *exact* order in which the user's
# code produced them - that way a `print()` followed by a top-level table
# shows up as text-then-table in the interactions view, even though
# stdout and image/table emissions take different paths inside Python.
# Pyodide is single-threaded, so a single shared list is fine.
_pll_displays = []

# When set (by either host during a file run), this is a JS callback taking
# one JSON string. Every display payload — each stdout/stderr write, image,
# and table — is emitted through it as it is produced, so the interactions
# view updates *during* the run instead of only at the end. This is what
# lets an interactive program print a prompt before input() blocks.
# Left as None during REPL/tests, where output is delivered in one batch.
_pll_live_emit = None
#: Posts what `_pll_live_emit` is holding back, set beside it.
_pll_live_flush = None


def _pll_push(payload):
    """Emit a display payload live, or record it for the end of the run.

    Exactly one of the two: when a live hook is installed the host streams
    each payload as it happens (`withLiveEmit` in pyodide/worker.ts), and
    the result does not carry it again - which would show it twice, and
    cost a list as long as a print loop's output.
    """
    emit = _pll_live_emit
    if emit is None:
        _pll_displays.append(payload)
        return
    try:
        emit(_pll_json.dumps(payload))
    except Exception:
        pass


class _PllStream:
    """Drop-in replacement for `sys.stdout` / `sys.stderr` during a run.

    Each `write` pushes a typed entry onto `_pll_displays` so text
    output interleaves with image/table emissions. We also keep the
    aggregate string so `result["stdout"]` / `result["stderr"]` can
    still be inspected by smoke tests and any caller that just wants
    "what did the program print?".
    """

    __slots__ = ("_kind", "_chunks", "_warned")

    def __init__(self, kind):
        self._kind = kind  # "stdout" or "stderr"
        self._chunks = []
        self._warned = set()  # the warnings said on it, so each is said once

    def write(self, s):
        if not isinstance(s, str):
            s = str(s)
        if s:
            _pll_push({"kind": self._kind, "text": s})
            self._chunks.append(s)
        return len(s)

    def writelines(self, lines):
        for line in lines:
            self.write(line)

    def flush(self):
        # `print(..., flush=True)` and `sys.stdout.flush()`: a partial line,
        # a progress dot, is shown now rather than with the next line.
        flush = _pll_live_flush
        if flush is not None:
            try:
                flush()
            except Exception:
                pass

    def isatty(self):
        return False

    def getvalue(self):
        return "".join(self._chunks)


def _pll_extract_display(value):
    """Try every known display protocol on `value`.

    Returns the display (`{"kind": "image"|"table", ...}`) or None if
    `value` doesn't know how to display itself.
    """
    for protocol in ("_pll_table_data", "_pll_image_data"):
        if hasattr(value, protocol):
            try:
                data = getattr(value, protocol)()
            except Exception:
                return None
            return data if isinstance(data, dict) else None
    return None


def _pll_matplotlib_figure(value):
    """The figure a matplotlib Figure or Axes is, or None.

    Looked up in `sys.modules`, so a program that never imports matplotlib
    never loads it.
    """
    figures = _sys.modules.get("matplotlib.figure")
    if figures is not None and isinstance(value, figures.Figure):
        return value
    axes = _sys.modules.get("matplotlib.axes")
    if axes is not None and isinstance(value, axes.Axes):
        return value.figure
    return None


def _pll_is_matplotlib(value):
    """Whether `value` is one of matplotlib's objects, or holds one: what
    `plt.title(...)` or `plt.plot(...)` returns, which says nothing to read."""
    if isinstance(value, (list, tuple)):
        return any(_pll_is_matplotlib(item) for item in value[:20])
    return type(value).__module__.split(".")[0] == "matplotlib"


def _pll_display_of(value):
    """How `value` is shown in the panel rather than as text - a function
    that shows it - or None: a picture, a table, or a matplotlib figure."""
    if type(value) in _PLL_TEXT_TYPES:
        return None
    figure = _pll_matplotlib_figure(value)
    if figure is not None:
        return lambda: globals()["_pll_show_figure"](figure)
    payload = _pll_extract_display(value)
    if payload is not None:
        return lambda: _pll_push(payload)
    return None


#: Types that are never shown as anything but text, and need no looking at.
_PLL_TEXT_TYPES = frozenset((str, int, float, bool, type(None), list, tuple, dict, set))


def _pll_show_top_level(value):
    """Emit a value produced by a top-level expression statement.

    Mirrors the behavior of Python's interactive shell: `None` is suppressed,
    PLL images and tables are captured for the host to render, anything
    else is printed via `repr` so bare expressions like `1 + 2` still display.
    A matplotlib figure is shown as a picture; the lines and labels
    matplotlib's functions return are not printed.
    """
    if value is None:
        return
    # A reactor pushed its own card when it was started; printing its repr
    # as well would be noise. Duck-typed like the display protocols, so the
    # bootstrap still knows nothing about the reactor library.
    if getattr(value, "_pll_already_displayed", False):
        return
    show = _pll_display_of(value)
    if show is not None:
        show()
        return
    if _pll_is_matplotlib(value):
        return
    print(repr(value))
    _pll_warn_iterators((value,), _sys._getframe(1).f_lineno)


#: The iterators a student meets, by type, and the function that makes each
#: (None for a generator).
_PLL_ITERATOR_MAKERS = {
    map: "map",
    filter: "filter",
    zip: "zip",
    enumerate: "enumerate",
    reversed: "reversed",
    type(reversed([])): "reversed",
    type(reversed({})): "reversed",
    type(reversed({}.values())): "reversed",
    type(reversed({}.items())): "reversed",
    _pll_types.GeneratorType: None,
}


def _pll_warn_iterators(values, line):
    """Say what an iterator is when one is shown, at `line`: `<zip object at
    0x...>` looks like a value of its own, and nothing it shows says that
    reading it once uses it up. Said once for each line and kind, on the
    run's own `stderr`, after what Python shows."""
    stream = _sys.stderr
    if not isinstance(stream, _PllStream):
        return
    for value in values:
        if type(value) not in _PLL_ITERATOR_MAKERS:
            continue
        maker = _PLL_ITERATOR_MAKERS[type(value)]
        if (line, maker) in stream._warned:
            continue
        stream._warned.add((line, maker))
        if maker is None:
            said = "This generator is an iterator, not a list", "`list(...)` of it"
        else:
            said = "`%s(...)` gives an iterator, not a list" % maker, "`list(%s(...))`" % maker
        stream.write(
            "warning: line %d: %s: its items are worked out as they are read, and can be read only once. "
            "%s makes a list of them.\n" % (line, said[0], said[1])
        )


#: Python's own `print`, which `_pll_print` prints text with.
_pll_python_print = print


def _pll_print(*values, sep=" ", end="\n", file=None, flush=False):
    """`print` at the student levels: Python's, except that a picture, a table
    or a figure is shown as a top-level expression shows one - so a function
    can show one too, which a value on a line of its own there cannot.

    Each is shown as a block: text printed before it ends its line, and the
    line it would have ended is not left empty after it. Anywhere but the
    panel's own output - `file=` another stream, output redirected, a test's
    captured output - it is Python's `print`, which has only text.
    """
    stream = _sys.stdout
    shows = [_pll_display_of(value) for value in values]
    to_panel = (file is None or file is stream) and isinstance(stream, _PllStream)
    if (
        not any(shows)
        or not to_panel
        or not isinstance(sep if sep is not None else " ", str)
        or not isinstance(end if end is not None else "\n", str)
    ):
        _pll_python_print(*values, sep=sep, end=end, file=file, flush=flush)
        if to_panel:
            _pll_warn_iterators(values, _sys._getframe(1).f_lineno)
        return
    text = []
    for value, show in zip(values, shows):
        if show is None:
            text.append(value)
            continue
        if text:
            _pll_python_print(*text, sep=sep, file=stream)
            text = []
        show()
    if text:
        _pll_python_print(*text, sep=sep, end=end, file=stream)
    if flush:
        stream.flush()


_pll_print.__name__ = _pll_print.__qualname__ = "print"
_pll_print.__doc__ = _pll_python_print.__doc__


# Called by the code `_PllTopLevelExprWrapper` adds.
_pll_hidden("show_top_level", _pll_show_top_level)


def _pll_session_module(session_key):
    """Get-or-create the module for `session_key`.

    A new session starts with `_pll_initial_globals`, so all baseline names
    like the image primitives are present.
    """
    module = _pll_sessions.get(session_key)
    if module is None:
        module = _pll_types.ModuleType("__main__")
        module.__dict__.update(_pll_initial_globals)
        _pll_sessions[session_key] = module
    return module


def _pll_get_session(session_key):
    """The globals of `session_key`'s module."""
    return _pll_session_module(session_key).__dict__


@contextlib.contextmanager
def _pll_as_main(module):
    """Make `module` `__main__` while the student's code runs in it.

    A file runs as `__main__`, and whatever looks a class's module up -
    `typing.get_type_hints`, a dataclass's string annotations, `pickle`,
    `import __main__` - looks in `sys.modules`. Otherwise it finds PLL's
    own namespace, not the student's.
    """
    previous = _sys.modules.get("__main__")
    _sys.modules["__main__"] = module
    try:
        yield
    finally:
        _sys.modules["__main__"] = previous


def _pll_end_session(session_key):
    """Forget `session_key` and everything its runs defined: its file is closed."""
    _pll_sessions.pop(session_key, None)


def _pll_reset_session(session_key, level):
    """Reset the globals for `session_key` to the baseline template.

    Mutates the existing dict in place (`clear` + `update`) so any cached
    reference to it (e.g. from `_pll_show_top_level`'s closure or from
    Pyodide's `globals.get(...)`) remains valid. `__pll_level__` records the
    file's level, for the checks made while its code runs, whenever that is.
    """
    _pll_let_go()
    g = _pll_get_session(session_key)
    g.clear()
    g.update(_pll_initial_globals)
    g.update(_pll_level_names(level))
    g["__pll_level__"] = level
    return g
