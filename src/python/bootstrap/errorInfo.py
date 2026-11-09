# Describing an exception for the host: the message as Python would display
# it, the line and column, the student's own frames, and the facts the
# explanations need (a name, a sequence and its length, ...) - as data, so
# no explanation ever has to parse Python's wording back out of a message.

import traceback as _tb_mod
import linecache as _pll_linecache
import ast as _ast
import re as _pll_src_re
import inspect as _pll_inspect
import weakref as _pll_weakref

#: The functions of PLL's dataclass checks, whose frames are the checks'
#: own, like a contract's (compile.py).
_PLL_FIELD_CHECKS = ("__init__", "_pll_checked_setattr", "_pll_check_field")


def _pll_is_checks_frame(filename, name=None):
    """Whether a frame is the checks' own rather than code that was checked:
    a contract's (bootstrap/contracts.py), or a dataclass field check's."""
    if not isinstance(filename, str):
        return False
    return filename == "<pll:bootstrap/contracts>" or (
        filename == "<pll:bootstrap/compile>" and name in _PLL_FIELD_CHECKS
    )


def _pll_course_type_name(name):
    """`Image` for any of the image library's own classes - `_Ellipse`, a
    chart - which a student has never seen; any other name as it is."""
    found = globals().get(name.rsplit(".", 1)[-1])
    image = globals().get("Image")
    if isinstance(found, type) and isinstance(image, type) and issubclass(found, image):
        return "Image"
    return name


def _pll_add_facts(exc, **facts):
    """Record what was learned about `exc` for the host's explanations.

    Facts travel beside the message, never in it: the message stays the one
    Python wrote, and the host reads a fact by name rather than by pattern.
    """
    try:
        known = getattr(exc, "_pll_facts", None) or {}
        known.update(facts)
        exc._pll_facts = known
    except Exception:
        pass


def _pll_student_frames(exc):
    """The live frames of `exc`'s traceback that run the student's code."""
    frames = []
    tb = exc.__traceback__
    while tb is not None:
        if _pll_is_students(tb.tb_frame.f_code.co_filename):
            frames.append((tb.tb_frame, tb.tb_lineno))
        tb = tb.tb_next
    return frames


#: The input each prompt line's code was compiled from. Every prompt line
#: is `<repl>`, so the name cannot say which one a frame is in: a function
#: defined at an earlier prompt line runs code from that line's input.
_pll_prompt_sources = _pll_weakref.WeakKeyDictionary()


def _pll_remember_prompt_source(code, source):
    """Record `source` for `code` and every function compiled inside it."""
    _pll_prompt_sources[code] = source
    for const in code.co_consts:
        if isinstance(const, type(code)):
            _pll_remember_prompt_source(const, source)


def _pll_source_of(code, run):
    """The source `code` was compiled from, as it ran.

    A prompt line's own input; the run's code for the file that was run -
    `run` is `(filename, code)`, and the file need not be on disk; and any
    other file as it is on disk.
    """
    prompt = _pll_prompt_sources.get(code)
    if prompt is not None:
        return prompt
    filename = code.co_filename
    if run is not None and filename == run[0]:
        return run[1]
    _pll_linecache.checkcache(filename)
    return "".join(_pll_linecache.getlines(filename))


def _pll_source_line(code, lineno, run):
    """Line `lineno` of the source `code` was compiled from."""
    lines = _pll_source_of(code, run).split("\n")
    return lines[lineno - 1].rstrip("\r") if 0 < lineno <= len(lines) else ""


def _pll_enrich_index_error(exc, run):
    """Record how long the list really is, for an `IndexError`.

    "list index out of range" says nothing about the list, and the
    explanation was left to illustrate with a made-up list of 3. The frame
    the error was raised in holds the real one, and the line says which
    name was subscripted.
    """
    if type(exc) is not IndexError or "out of range" not in str(exc):
        return
    tb = exc.__traceback__
    while tb is not None and tb.tb_next is not None:
        tb = tb.tb_next
    # Raised in a bundle's code, or a library's, the subscript is not on
    # the student's line.
    if tb is None or not _pll_is_students(tb.tb_frame.f_code.co_filename):
        return
    frame, lineno = tb.tb_frame, tb.tb_lineno
    text = _pll_source_line(frame.f_code, lineno, run)
    for name in _pll_src_re.findall(r"([A-Za-z_]\w*)\s*\[", text):
        value = frame.f_locals.get(name, frame.f_globals.get(name))
        if isinstance(value, (list, tuple, str)):
            _pll_add_facts(exc, sequence=name, length=len(value))
            return


#: How Python words a call of a value that is not a function.
_PLL_NOT_CALLABLE_RE = _pll_src_re.compile(r"^'([\w.]+)' object is not callable")


def _pll_enrich_not_callable(exc, run):
    """Record what was called, for `'int' object is not callable`: the name
    as written, how many arguments it was given, and whether it hides one
    of Python's own functions (`called`) - or, for a number written before
    brackets, the multiplication it stands for (`multiplication`).

    The message names only the type. The name counts only when its call is
    the one that failed, in the student's own frame, and its value there is
    of that type: a built-in raises the same error at its own call when it
    is given the value, as `list(map(5, xs))` is.
    """
    found = _PLL_NOT_CALLABLE_RE.match(str(exc)) if type(exc) is TypeError else None
    if found is None or not str(_pll_failed_instruction(exc.__traceback__) or "").startswith("CALL"):
        return
    tb = exc.__traceback__
    while tb.tb_next is not None:
        tb = tb.tb_next
    frame = tb.tb_frame
    # The failing instruction spans the call, and no two calls end at the
    # same `)`.
    where = _tb_mod.extract_tb(tb)[-1]
    source = _pll_source_of(frame.f_code, run)
    try:
        with _pll_without_syntax_warnings():
            tree = _ast.parse(source)
    except (SyntaxError, ValueError):
        return
    call = next(
        (
            node
            for node in _ast.walk(tree)
            if isinstance(node, _ast.Call)
            and (node.end_lineno, node.end_col_offset) == (where.end_lineno, where.end_colno)
        ),
        None,
    )
    if call is None:
        return
    meant = _pll_multiplication_meant(call, source)
    if meant is not None:
        _pll_add_facts(exc, multiplication=meant)
        return
    attributes, called = [], call.func
    while isinstance(called, _ast.Attribute):
        attributes.insert(0, called.attr)
        called = called.value
    if not isinstance(called, _ast.Name):
        return
    missing = object()
    value = missing
    for scope in (frame.f_locals, frame.f_globals, frame.f_builtins):
        value = scope.get(called.id, missing)
        if value is not missing:
            break
    for attribute in attributes:
        # As stored: reading it would run a property's code a second time.
        value = _pll_inspect.getattr_static(value, attribute, missing)
    if value is missing or type(value).__name__ != found.group(1).rsplit(".", 1)[-1]:
        return
    name = ".".join([called.id] + attributes)
    _pll_add_facts(
        exc,
        called={
            "name": name,
            "arguments": len(call.args) + len(call.keywords),
            "hides": callable(frame.f_builtins.get(name)),
        },
    )


#: What can follow a `*` as it is written: a single value - a name, a
#: literal, or what an attribute, a subscript or a call gives - which no
#: operator beside it can take a part of.
_PLL_SINGLE_VALUES = (
    _ast.Name, _ast.Constant, _ast.JoinedStr, _ast.Attribute, _ast.Subscript, _ast.Call,
    _ast.List, _ast.Tuple, _ast.Set, _ast.Dict, _ast.ListComp, _ast.SetComp, _ast.DictComp, _ast.GeneratorExp,
)


def _pll_multiplication_meant(call, source):
    """The multiplication a number written before brackets stands for:
    `{"number": "2", "product": "2 * (3 + 4)", "written": "2(3 + 4)"}` for
    the call `2(3 + 4)` in `source`.

    The brackets stay unless they hold a single value: without them,
    `2 * 3 + 4` is 10. None for a call of anything but a number; for brackets
    that hold no one expression, as `3(4, 5)`'s do, since those are not a
    multiplication; and for a call over several lines, which a message
    cannot quote.
    """
    number = call.func
    if not (isinstance(number, _ast.Constant) and type(number.value) in (int, float)):
        return None
    if call.keywords or len(call.args) > 1 or call.lineno != call.end_lineno:
        return None
    if call.args and isinstance(call.args[0], _ast.Starred):
        return None
    shown = _ast.get_source_segment(source, number)
    written = _ast.get_source_segment(source, call)
    operand = _ast.get_source_segment(source, call.args[0]) if call.args else "..."
    if shown is None or written is None or operand is None:
        return None
    if call.args and not isinstance(call.args[0], _PLL_SINGLE_VALUES):
        operand = "(%s)" % operand
    return {"number": shown, "product": "%s * %s" % (shown, operand), "written": written}


def _pll_innermost_tb(tb, count):
    """`tb` from its innermost `count` frames on, and how many it skips.

    A `RecursionError` under a raised `sys.setrecursionlimit` has tens of
    thousands of frames, and reading each one's line takes seconds.
    """
    nodes = []
    while tb is not None:
        nodes.append(tb)
        tb = tb.tb_next
    if len(nodes) <= count:
        return (nodes[0] if nodes else None), 0
    return nodes[-count], len(nodes) - count


#: Files that are not the student's: the standard library, installed
#: packages, and pytest.
_PLL_NOT_STUDENT = ("site-packages", "/lib/python", "_pytest", "pluggy")


def _pll_failed_instruction(tb):
    """What the student's code was doing when it failed, as the name of the
    instruction - `CALL` when a function it called raised with no frame of
    its own (a built-in), `GET_ITER` when a `for` started on a value - or
    None when the innermost frame is not theirs. The two can fail at the
    same place: `for n in max(xs)` and `max(5)` both point at the call."""
    if tb is None:
        return None
    while tb.tb_next is not None:
        tb = tb.tb_next
    code = tb.tb_frame.f_code
    if not _pll_is_students(code.co_filename):
        return None
    try:
        import dis as _pll_dis

        for instruction in _pll_dis.get_instructions(code):
            if instruction.offset == tb.tb_lasti:
                return instruction.opname
    except Exception:
        pass
    return None


def _pll_is_students(filename):
    """Whether a frame in `filename` runs the student's code: one of their
    files, or a prompt line (`<repl>`). Any other `<...>` is code no file
    holds - PLL's own (`<pll:...>`), or code Python made from a string
    (`<string>`, as `typing` and `dataclasses` do, and `<frozen ...>`).
    """
    if filename == "<repl>":
        return True
    if filename.startswith("<"):
        return False
    return not any(token in filename for token in _PLL_NOT_STUDENT)

#: How Python words a name used before it has a value.
_PLL_UNBOUND_RE = _pll_src_re.compile(r"cannot access (?:free|local) variable '(\w+)'")

#: Innermost frames sent with an error. A `RecursionError` has a thousand,
#: and the rules that read frames want only the last few.
_PLL_MAX_FRAMES = 100


def _pll_shown_file(filename):
    """A file as the student knows it: one next to their program by its own
    name, rather than the work directory's path."""
    prefix = _PLL_WORK_DIR + "/"
    if isinstance(filename, str) and filename.startswith(prefix):
        return filename[len(prefix) :]
    return filename


def _pll_parameters(code):
    """The parameters of the function `code` runs, or None at module level."""
    if code.co_name == "<module>":
        return None
    count = code.co_argcount + code.co_kwonlyargcount
    count += bool(code.co_flags & _pll_inspect.CO_VARARGS)
    count += bool(code.co_flags & _pll_inspect.CO_VARKEYWORDS)
    return list(code.co_varnames[:count])


def _pll_frame_text(summary, code, run):
    """The student's line a frame is at, as written, or None."""
    return _pll_source_line(code, summary.lineno, run) or None


def _pll_frame_column(summary, code, run):
    """The 0-based column `summary`'s frame failed at, or None.

    None where Python's own traceback draws no caret: when it has no source
    for the line, or when the failing expression is the whole line.
    """
    if summary.colno is None or summary.end_colno is None:
        return None
    text = _pll_source_line(code, summary.lineno, run)
    if not text:
        return None
    # Python counts these in UTF-8 bytes; a column counts characters.
    encoded = text.encode("utf-8")
    start = len(encoded[: summary.colno].decode("utf-8", "replace"))
    if summary.end_lineno == summary.lineno:
        end = len(encoded[: summary.end_colno].decode("utf-8", "replace"))
        if text[:start].strip() == "" and text[end:].strip() == "":
            return None
    return start


#: Linux's number for each error name: what CPython says in `[Errno 2]`.
#: Pyodide's are Emscripten's, so the same missing file is `[Errno 44]`.
_PLL_LINUX_ERRNO = {
    "EPERM": 1, "ENOENT": 2, "EINTR": 4, "EIO": 5, "EBADF": 9, "EAGAIN": 11, "ENOMEM": 12,
    "EACCES": 13, "EBUSY": 16, "EEXIST": 17, "EXDEV": 18, "ENOTDIR": 20, "EISDIR": 21,
    "EINVAL": 22, "EMFILE": 24, "EFBIG": 27, "ENOSPC": 28, "ESPIPE": 29, "EROFS": 30,
    "EPIPE": 32, "ERANGE": 34, "ENAMETOOLONG": 36, "ENOTEMPTY": 39, "ELOOP": 40,
    "ECONNREFUSED": 111, "ETIMEDOUT": 110, "EHOSTUNREACH": 113,
}


def _pll_linux_errno(message, exc):
    """`message` with an `OSError`'s `[Errno 44]` as CPython on Linux says it."""
    number = getattr(exc, "errno", None)
    if not isinstance(exc, OSError) or not isinstance(number, int):
        return message
    try:
        import errno as _pll_errno

        linux = _PLL_LINUX_ERRNO.get(_pll_errno.errorcode.get(number))
    except Exception:
        linux = None
    if linux is None or linux == number:
        return message
    return message.replace("[Errno %d]" % number, "[Errno %d]" % linux, 1)


def _pll_displayed_message(exc):
    """The message as Python's traceback shows it - as CPython would.

    Not always `str(exc)`: Python adds its suggestion ("Did you mean:
    'total'?") to a `NameError` or `AttributeError` only when it displays
    one, and a `SyntaxError`'s `str` carries the file and line, which the
    display puts elsewhere. An `OSError`'s number is CPython's on Linux.
    """
    return _pll_linux_errno(_pll_displayed_message_as_raised(exc), exc)


def _pll_displayed_message_as_raised(exc):
    exc_type = type(exc)
    shown = exc_type.__qualname__
    if exc_type.__module__ not in ("__main__", "builtins"):
        shown = "%s.%s" % (exc_type.__module__, shown)
    try:
        lines = _tb_mod.TracebackException(
            exc_type, exc, exc.__traceback__, limit=0, compact=True
        ).format_exception_only()
        for text in lines:
            if text.startswith(shown + ": "):
                return text[len(shown) + 2 :].rstrip("\n")
            if text.rstrip("\n") == shown:
                return ""
    except Exception:
        pass
    return exc.msg if isinstance(exc, SyntaxError) else str(exc)


def _pll_error_info(exc, run=None, level=None):
    """`exc` described, and explained: the `error` of a result.

    The one place an exception becomes a result, for a file run, a prompt
    line, a test and a reactor alike. `run` is `(filename, code)` for what
    was run, which the lines of its frames are read from (see
    `_pll_source_of`), and `level` its level.

    - `finding`: what the student is told, and where (`explain/finding.py`) -
      all the host reads, with `errorType` and `message`, Python's own words.
    - `frames`: outermost first, each `{file, line, column, function, user,
      text, parameters}`, where `user` says whether the frame runs the
      student's code, and `text` and `parameters` are their line there and
      the parameters of their function.
    - `facts`: what was learned from the live frames - the name a
      `NameError` is about, a sequence's real length, the value that failed
      its annotation, a swapped field, the name a value that is not a
      function was called by - and from the code (`_pll_code_facts`).
    """
    _pll_fill_lazy(quietly=True)
    _pll_enrich_index_error(exc, run)
    _pll_enrich_not_callable(exc, run)
    _pll_enrich_module_not_found(exc)
    # The same frames twice over: summaries for their lines, and the live
    # ones for the code they run.
    # Read from far enough in that the checks' frames left out still leave
    # `_PLL_MAX_FRAMES` of the rest.
    tb, _skipped = _pll_innermost_tb(exc.__traceback__, _PLL_MAX_FRAMES * 3)
    entries = [
        (s, live.f_code)
        for s, (live, _line) in zip(_tb_mod.extract_tb(tb), _tb_mod.walk_tb(tb))
        if not _pll_is_checks_frame(s.filename, s.name)
    ][-_PLL_MAX_FRAMES:]
    frames = []
    for s, code in entries:
        user = _pll_is_students(s.filename)
        frames.append({
            "file": _pll_shown_file(s.filename),
            "line": s.lineno,
            "column": _pll_frame_column(s, code, run),
            "function": None if s.name == "<module>" else s.name,
            "user": user,
            # The line itself, so the host never reads it out of the wrong
            # file: a frame can be in any of the student's files.
            "text": _pll_frame_text(s, code, run) if user else None,
            "parameters": _pll_parameters(code) if user else None,
        })
    facts = dict(getattr(exc, "_pll_facts", None) or {})
    try:
        facts.update(_pll_code_facts(exc, run))
    except Exception:
        # Facts only add to an explanation; the error itself still has to
        # be reported if reading them fails.
        pass
    instruction = _pll_failed_instruction(exc.__traceback__)
    if instruction is not None:
        facts["instruction"] = instruction
    if isinstance(exc, NameError):
        # Python sets `name` for most of these, but not for a local read
        # before it is assigned; its message names it either way.
        name = getattr(exc, "name", None)
        if not isinstance(name, str):
            found = _PLL_UNBOUND_RE.search(str(exc))
            name = found.group(1) if found else None
        if name is not None:
            facts["name"] = name
    if isinstance(exc, SyntaxError):
        where = {
            "file": _pll_shown_file(exc.filename),
            "line": exc.lineno,
            "column": exc.offset - 1 if exc.offset else None,
            "text": exc.text.rstrip("\n") if exc.text else None,
        }
    elif frames:
        where = frames[-1]
    else:
        where = {"file": None, "line": None, "column": None, "text": None}
    error = {
        "errorType": type(exc).__name__,
        "message": _pll_displayed_message(exc),
        "fileName": where["file"],
        "lineNumber": where["line"],
        "column": where["column"],
        "text": where.get("text"),
        "frames": frames,
        "facts": facts,
    }
    try:
        error["finding"] = _pll_explain_error(error, run, level)
    except Exception:
        # An explanation that fails leaves Python's own words: the error
        # itself is reported either way.
        error["finding"] = _pll_unexplained(error, run)
    return error
