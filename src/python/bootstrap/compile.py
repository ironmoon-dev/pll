# Compiling the student's code: the AST passes that put annotations in force
# as contracts (bootstrap/contracts.py), check dataclass fields, show
# top-level expression values, and turn Python's compile-time warnings into
# something a beginner can act on.

import ast as _ast
import copy as _pll_copy
import contextlib
import dataclasses as _pll_dataclasses
import sys as _sys
import warnings as _pll_warnings
import weakref as _pll_weakref
import re as _pll_src_re

def _pll_has_annotations(node):
    """Whether a `def` annotates anything: then it has a contract."""
    return node.returns is not None or any(arg.annotation is not None for arg in _pll_all_args(node.args))


def _pll_is_quoted(annotation):
    """An annotation written as a string: a name, looked up when needed."""
    return isinstance(annotation, _ast.Constant) and isinstance(annotation.value, str)


def _pll_bound_names(target):
    """The names an assignment's target binds: `a`, or each of `a, (b, c)`."""
    if isinstance(target, _ast.Name):
        return [target.id]
    if isinstance(target, (_ast.Tuple, _ast.List)):
        return [name for element in target.elts for name in _pll_bound_names(element)]
    if isinstance(target, _ast.Starred):
        return _pll_bound_names(target.value)
    return []


#: Packages a program imports that are not the student's: none of their
#: functions has a contract of PLL's to carry.
_PLL_NOT_STUDENTS = frozenset(("pll", "pandas", "numpy", "matplotlib", "pytest", "_pytest", "requests", "PIL", "scipy"))


def _pll_may_be_students(module, level):
    """Whether `module` may be one of the student's own files, whose
    functions have contracts: anything but the standard library and the
    packages PLL knows. pytest's assertion rewriting imports its helpers
    under names no program can write (`@py_builtins`)."""
    if level:
        return True
    top = module.split(".")[0]
    return bool(top) and not top.startswith("@") and top not in _sys.stdlib_module_names and top not in _PLL_NOT_STUDENTS


class _PllContractScope:
    """A scope of the program, as far as contracts need one: the names it
    binds; which of those may be contracted functions (`contracted`: an
    annotated `def`, or a name imported from another file) or modules;
    its annotated variables; and the party a reference made in it belongs
    to (`party`, as bootstrap/contracts.py reads it). A function's scope
    says whether its own `def` is contracted."""

    __slots__ = (
        "kind", "parent", "party", "qualname", "bound", "globals", "nonlocals",
        "contracted", "modules", "annotations", "contracted_def",
    )

    def __init__(self, kind, parent, party, qualname):
        self.kind = kind
        self.parent = parent
        self.party = party
        self.qualname = qualname
        self.bound = set()
        self.globals = set()
        self.nonlocals = set()
        self.contracted = set()
        self.modules = set()
        self.annotations = {}
        self.contracted_def = False


class _PllContractScopes(_ast.NodeVisitor):
    """The scopes of a program, by node, and which one a name refers to -
    by Python's own rules - for `_PllContracts`."""

    def __init__(self, filename):
        self.filename = filename
        self.by_node = {}
        self.current = None
        self.module = None
        # A prompt line runs among the names the file and earlier lines
        # defined: any name it does not bind may be a contracted function.
        self.prompt = filename == "<repl>"

    def build(self, tree):
        self.module = self.current = _PllContractScope(
            "module", None, ("main", None, "<module>", self.filename, None), ""
        )
        self.by_node[id(tree)] = self.module
        for statement in tree.body:
            self.visit(statement)
        return self

    def scope_of(self, node):
        return self.by_node[id(node)]

    def binder(self, scope, name):
        """The scope `name`, used in `scope`, refers to - or None, for a
        built-in."""
        if name in scope.globals:
            return self.module if name in self.module.bound else None
        if name in scope.bound and name not in scope.nonlocals:
            return scope
        candidate = scope.parent
        while candidate is not None:
            if candidate.kind == "class":
                candidate = candidate.parent
                continue
            if candidate.kind == "module":
                return candidate if name in candidate.bound else None
            if name in candidate.globals:
                return self.module if name in self.module.bound else None
            if name in candidate.bound and name not in candidate.nonlocals:
                return candidate
            candidate = candidate.parent
        return None

    def _enter(self, node, kind, party, qualname):
        scope = _PllContractScope(kind, self.current, party, qualname)
        self.by_node[id(node)] = scope
        return scope

    def _inside(self, scope, nodes):
        outer, self.current = self.current, scope
        for node in nodes:
            self.visit(node)
        self.current = outer

    def _qualname(self, name):
        scope = self.current
        if scope.kind == "module":
            return name
        if scope.kind == "class":
            return scope.qualname + "." + name
        return scope.qualname + ".<locals>." + name

    def _defaults(self, arguments):
        for default in list(arguments.defaults) + [d for d in arguments.kw_defaults if d is not None]:
            self.visit(default)

    def visit_FunctionDef(self, node):
        self.current.bound.add(node.name)
        contracted = isinstance(node, _ast.FunctionDef) and _pll_has_annotations(node)
        if contracted and self.current.kind != "class":
            self.current.contracted.add(node.name)
        for decorator in node.decorator_list:
            self.visit(decorator)
        self._defaults(node.args)
        qualname = self._qualname(node.name)
        party = ("function", qualname.replace(".<locals>.", "."), qualname, self.filename, node.lineno)
        scope = self._enter(node, "function", party, qualname)
        scope.contracted_def = contracted
        scope.bound.update(arg.arg for arg in _pll_all_args(node.args))
        # A parameter's annotation is its variable's, for what the body
        # assigns it: `ac = ac.balance + amt` gives an `Account` a number.
        scope.annotations.update(
            (arg.arg, arg.annotation) for arg in _pll_all_args(node.args) if arg.annotation is not None
        )
        self._inside(scope, node.body)

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_Lambda(self, node):
        self._defaults(node.args)
        scope = self._enter(node, "lambda", self.current.party, self.current.qualname)
        scope.bound.update(arg.arg for arg in _pll_all_args(node.args))
        self._inside(scope, [node.body])

    def visit_ClassDef(self, node):
        self.current.bound.add(node.name)
        for part in node.decorator_list + node.bases + [keyword.value for keyword in node.keywords]:
            self.visit(part)
        scope = self._enter(node, "class", self.current.party, self._qualname(node.name))
        self._inside(scope, node.body)

    def _comprehension(self, node, parts):
        self.visit(node.generators[0].iter)
        scope = self._enter(node, "comprehension", self.current.party, self.current.qualname)
        outer, self.current = self.current, scope
        for index, generator in enumerate(node.generators):
            if index:
                self.visit(generator.iter)
            self.visit(generator.target)
            for condition in generator.ifs:
                self.visit(condition)
        for part in parts:
            self.visit(part)
        self.current = outer

    def visit_ListComp(self, node):
        self._comprehension(node, [node.elt])

    visit_SetComp = visit_GeneratorExp = visit_ListComp

    def visit_DictComp(self, node):
        self._comprehension(node, [node.key, node.value])

    def visit_Name(self, node):
        if not isinstance(node.ctx, _ast.Load):
            self.current.bound.add(node.id)

    def visit_NamedExpr(self, node):
        self.visit(node.value)
        scope = self.current
        while scope.kind == "comprehension":
            scope = scope.parent
        scope.bound.add(node.target.id)

    def visit_Import(self, node):
        for alias in node.names:
            name = alias.asname or alias.name.split(".")[0]
            self.current.bound.add(name)
            if _pll_may_be_students(alias.name, 0):
                self.current.modules.add(name)

    def visit_ImportFrom(self, node):
        for alias in node.names:
            if alias.name != "*":
                name = alias.asname or alias.name
                self.current.bound.add(name)
                if _pll_may_be_students(node.module or "", node.level):
                    self.current.contracted.add(name)

    def visit_Global(self, node):
        self.current.globals.update(node.names)

    def visit_Nonlocal(self, node):
        self.current.nonlocals.update(node.names)

    def visit_AnnAssign(self, node):
        if isinstance(node.target, _ast.Name) and self.current.kind in ("module", "function"):
            self.current.annotations[node.target.id] = node.annotation
            if node.value is not None:
                self.current.bound.add(node.target.id)
        else:
            self.visit(node.target)
        if node.value is not None:
            self.visit(node.value)

    def visit_ExceptHandler(self, node):
        if node.name:
            self.current.bound.add(node.name)
        self.generic_visit(node)

    def visit_MatchAs(self, node):
        if node.name:
            self.current.bound.add(node.name)
        self.generic_visit(node)

    def visit_MatchStar(self, node):
        if node.name:
            self.current.bound.add(node.name)

    def visit_MatchMapping(self, node):
        if node.rest:
            self.current.bound.add(node.rest)
        self.generic_visit(node)

    def visit_TypeAlias(self, node):
        self.current.bound.add(node.name.id)


def _pll_only_ellipsis(body):
    """Whether `body` is `...`, after a docstring if it has one."""
    if body and isinstance(body[0], _ast.Expr) and isinstance(body[0].value, _ast.Constant) and isinstance(
        body[0].value.value, str
    ):
        body = body[1:]
    return (
        len(body) == 1
        and isinstance(body[0], _ast.Expr)
        and isinstance(body[0].value, _ast.Constant)
        and body[0].value.value is Ellipsis
    )


def _pll_is_unwritten(node):
    """Whether the function `node` is still to be written: its body is `...`
    - a design recipe's signature and purpose, whose tests come before its
    body."""
    return _pll_only_ellipsis(node.body)


class _PllPlaceholders(_ast.NodeTransformer):
    """At the student levels, a `...` the program reaches stops it
    (`pll:not_written`): there it holds the place of code still to be
    written, which Python would go on past - a value that does nothing.

    Not one in an annotation or a type alias, nor one among a subscript's
    keys (`tuple[int, ...]`, `Callable[..., str]`), each a part of a type -
    and Python evaluates an annotation when its `def` runs. Nor a class
    body that is only `...`, Python's way to write a class with nothing in
    it.
    """

    def __init__(self):
        # The `def` each `...` is in, innermost last.
        self.functions = []

    def visit_Constant(self, node):
        if node.value is not Ellipsis:
            return node
        function = self.functions[-1] if self.functions else None
        call = _ast.Call(
            func=_ast.copy_location(_ast.Name(id="pll:not_written", ctx=_ast.Load()), node),
            args=[_ast.copy_location(_ast.Constant(value=function), node)],
            keywords=[],
        )
        return _ast.copy_location(call, node)

    def visit_FunctionDef(self, node):
        annotated = [(arg, arg.annotation) for arg in _pll_all_args(node.args)]
        returns, type_params = node.returns, getattr(node, "type_params", [])
        for arg, _ in annotated:
            arg.annotation = None
        node.returns, node.type_params = None, []
        self.functions.append(node.name)
        self.generic_visit(node)
        self.functions.pop()
        for arg, annotation in annotated:
            arg.annotation = annotation
        node.returns, node.type_params = returns, type_params
        return node

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_ClassDef(self, node):
        if not _pll_only_ellipsis(node.body):
            self.generic_visit(node)
            return node
        node.decorator_list = [self.visit(d) for d in node.decorator_list]
        node.bases = [self.visit(b) for b in node.bases]
        node.keywords = [self.visit(k) for k in node.keywords]
        return node

    def visit_AnnAssign(self, node):
        node.target = self.visit(node.target)
        if node.value is not None:
            node.value = self.visit(node.value)
        return node

    def visit_TypeAlias(self, node):
        return node

    def visit_Subscript(self, node):
        node.value = self.visit(node.value)
        if isinstance(node.slice, _ast.Tuple):
            node.slice.elts = [
                elt if isinstance(elt, _ast.Constant) and elt.value is Ellipsis else self.visit(elt)
                for elt in node.slice.elts
            ]
        else:
            node.slice = self.visit(node.slice)
        return node


class _PllContracts(_ast.NodeTransformer):
    """Put a program's annotations in force as contracts
    (bootstrap/contracts.py):

    - an annotated `def` gets its contract, from the decorator
      `pll:contract_def` innermost of its decorators, and each `return` in
      it notes its line (`pll:returning`);
    - each reference to what may be a contracted function becomes the
      obligation for it (`pll:ref`), made by the definition it is in;
    - an annotated variable's value is checked each time it is given one
      (`pll:assigned`).

    Annotations are left as they are: the `def` records them, and a name in
    one is not a reference.
    """

    def __init__(self, scopes, source, filename):
        self.scopes = scopes
        self.source = source
        self.filename = filename
        self.current = None
        self.all_quoted = False

    def _call(self, name, args, at):
        call = _ast.Call(func=_ast.Name(id=name, ctx=_ast.Load()), args=args, keywords=[])
        _ast.copy_location(call, at)
        return call

    def _text(self, node):
        return _ast.get_source_segment(self.source, node) or _ast.unparse(node)

    def _statements(self, statements):
        kept = []
        for statement in statements:
            result = self.visit(statement)
            if isinstance(result, list):
                kept.extend(result)
            elif result is not None:
                kept.append(result)
        return kept

    def _in(self, node, work):
        outer, self.current = self.current, self.scopes.scope_of(node)
        try:
            return work()
        finally:
            self.current = outer

    def _defaults(self, arguments):
        arguments.defaults = [self.visit(default) for default in arguments.defaults]
        arguments.kw_defaults = [None if d is None else self.visit(d) for d in arguments.kw_defaults]

    def visit_Module(self, node):
        self.current = self.scopes.scope_of(node)
        self.all_quoted = any(
            isinstance(statement, _ast.ImportFrom)
            and statement.module == "__future__"
            and any(alias.name == "annotations" for alias in statement.names)
            for statement in node.body
        )
        node.body = self._statements(node.body)
        return node

    def visit_FunctionDef(self, node):
        node.decorator_list = [self.visit(decorator) for decorator in node.decorator_list]
        self._defaults(node.args)
        scope = self.scopes.scope_of(node)
        node.body = self._in(node, lambda: self._statements(node.body))
        if scope.contracted_def:
            node.decorator_list.append(self._contract(node, scope))
        return node

    visit_AsyncFunctionDef = visit_FunctionDef

    def _contract(self, node, scope):
        """`pll:contract_def(party, written, quoted)` for `node`."""
        written, quoted = [], []
        annotated = [(arg.arg, arg.annotation) for arg in _pll_all_args(node.args) if arg.annotation is not None]
        if node.returns is not None:
            annotated.append(("return", node.returns))
        for name, annotation in annotated:
            written.append((name, self._text(annotation)))
            if self.all_quoted or _pll_is_quoted(annotation):
                quoted.append(name)
        decorator = self._call(
            _PLL_CONTRACT_DEF,
            [
                _ast.Constant(value=scope.party),
                _ast.Constant(value=tuple(written)),
                _ast.Constant(value=tuple(quoted)),
            ],
            node,
        )
        _ast.fix_missing_locations(decorator)
        return decorator

    def visit_Return(self, node):
        if node.value is not None:
            node.value = self.visit(node.value)
        if self.current.kind == "function" and self.current.contracted_def:
            value = node.value if node.value is not None else _ast.copy_location(_ast.Constant(value=None), node)
            node.value = self._call(_PLL_RETURNING, [value, _ast.Constant(value=node.lineno)], value)
        return node

    def visit_ClassDef(self, node):
        node.decorator_list = [self.visit(decorator) for decorator in node.decorator_list]
        node.bases = [self.visit(base) for base in node.bases]
        for keyword in node.keywords:
            keyword.value = self.visit(keyword.value)
        node.body = self._in(node, lambda: self._statements(node.body))
        return node

    def visit_Lambda(self, node):
        self._defaults(node.args)
        node.body = self._in(node, lambda: self.visit(node.body))
        return node

    def _comprehension(self, node, parts):
        first = node.generators[0]
        first.iter = self.visit(first.iter)

        def inside():
            for index, generator in enumerate(node.generators):
                if index:
                    generator.iter = self.visit(generator.iter)
                generator.ifs = [self.visit(condition) for condition in generator.ifs]
            for part in parts:
                setattr(node, part, self.visit(getattr(node, part)))

        self._in(node, inside)
        return node

    def visit_ListComp(self, node):
        return self._comprehension(node, ["elt"])

    visit_SetComp = visit_GeneratorExp = visit_ListComp

    def visit_DictComp(self, node):
        return self._comprehension(node, ["key", "value"])

    def _reference(self, node):
        """`node` as the obligation its value may carry, made here."""
        return self._call(
            _PLL_REF,
            [node, _ast.Constant(value=self.current.party), _ast.Constant(value=node.lineno),
             _ast.Constant(value=node.col_offset)],
            node,
        )

    def visit_Name(self, node):
        if isinstance(node.ctx, _ast.Load):
            binder = self.scopes.binder(self.current, node.id)
            if binder is not None and node.id in binder.contracted:
                return self._reference(node)
            if binder is None and self.scopes.prompt and not hasattr(_pll_builtins, node.id):
                return self._reference(node)
        return node

    def visit_Attribute(self, node):
        node.value = self.visit(node.value)
        if isinstance(node.ctx, _ast.Load) and isinstance(node.value, _ast.Name):
            binder = self.scopes.binder(self.current, node.value.id)
            if binder is not None and node.value.id in binder.modules:
                return self._reference(node)
        return node

    # -- annotated variables --

    def _annotation(self, name):
        """The annotation of the variable `name` here, if it has one."""
        scope = self.current
        while scope.kind == "comprehension":
            scope = scope.parent
        if scope.kind not in ("module", "function") or name in scope.globals:
            return None
        return scope.annotations.get(name)

    def _assigned(self, value, name, annotation, at):
        return self._call(
            _PLL_ASSIGNED,
            [
                value,
                _pll_copy.deepcopy(annotation),
                _ast.Constant(value=self._text(annotation)),
                _ast.Constant(value=name),
                _ast.Constant(value=self.current.party),
                _ast.Constant(value=at.lineno),
                _ast.Constant(value=self.all_quoted or _pll_is_quoted(annotation)),
            ],
            at,
        )

    def _rechecked(self, name, annotation, at):
        """`name = pll:assigned(name, ...)`, after a statement that gave
        `name` a value some other way."""
        check = _ast.Assign(
            targets=[_ast.Name(id=name, ctx=_ast.Store())],
            value=self._assigned(_ast.Name(id=name, ctx=_ast.Load()), name, annotation, at),
        )
        _ast.copy_location(check, at)
        _ast.fix_missing_locations(check)
        return check

    def visit_AnnAssign(self, node):
        if node.value is None:
            return node
        node.value = self.visit(node.value)
        if isinstance(node.target, _ast.Name) and self._annotation(node.target.id) is not None:
            node.value = self._assigned(node.value, node.target.id, node.annotation, node)
        else:
            node.target = self.visit(node.target)
        return node

    def visit_Assign(self, node):
        node.value = self.visit(node.value)
        node.targets = [self.visit(target) for target in node.targets]
        names = [
            name for target in node.targets for name in _pll_bound_names(target) if self._annotation(name) is not None
        ]
        if not names:
            return node
        if len(node.targets) == 1 and isinstance(node.targets[0], _ast.Name):
            node.value = self._assigned(node.value, names[0], self._annotation(names[0]), node)
            return node
        return [node] + [self._rechecked(name, self._annotation(name), node) for name in names]

    def visit_AugAssign(self, node):
        node.value = self.visit(node.value)
        node.target = self.visit(node.target)
        if isinstance(node.target, _ast.Name) and self._annotation(node.target.id) is not None:
            return [node, self._rechecked(node.target.id, self._annotation(node.target.id), node)]
        return node

    def visit_NamedExpr(self, node):
        node.value = self.visit(node.value)
        annotation = self._annotation(node.target.id)
        if annotation is not None:
            node.value = self._assigned(node.value, node.target.id, annotation, node)
        return node


#: The bitwise operators, by their node, as they are written.
_PLL_BITWISE_SYMBOLS = {_ast.BitOr: "|", _ast.BitAnd: "&", _ast.BitXor: "^", _ast.LShift: "<<", _ast.RShift: ">>"}

#: Every operator `x op= y` can have, as it is written.
_PLL_OPERATOR_SYMBOLS = {
    **_PLL_BITWISE_SYMBOLS,
    _ast.Add: "+", _ast.Sub: "-", _ast.Mult: "*", _ast.Div: "/", _ast.FloorDiv: "//", _ast.Mod: "%",
    _ast.Pow: "**", _ast.MatMult: "@",
}


class _PllTeachingChecks(_ast.NodeTransformer):
    """What `beginner` and `intermediate` refuse as the code runs
    (typeChecking.py), each only when the value it meets is one it is about:

    - a bitwise operator between two numbers (`pll:bitwise`): `^` is no
      power, and between types or sets `|` is not bitwise at all;
    - changing a list, a dictionary or a set in place - a method that does
      (`pll:attribute`, as it is fetched, off the value or its class), a
      library function that does (`random.shuffle`; `pll:named` for one
      named on its own), `xs[i] = v` and `del xs[i]` (`pll:setitem`,
      `pll:delitem`, and `pll:setitem_check` for an item among several
      targets), a loop whose target is an item (`pll:iterating_into`),
      `xs += ys` (`pll:in_place`), `xs[i] += v` (`pll:setitem_in_place`)
      and `x.a += v` (`pll:attribute_in_place`) - where aliasing would make
      one change show up through another name;
    - `a is b` with a value a generic function was given as a type variable
      (`pll:identical`), which can only be passed along (contracts.py) and
      whose `is` Python would answer of its seal, not of the value.

    Annotations are left as they are: under `from __future__ import
    annotations` Python keeps them as their text, which a call in place of
    `|` would garble.
    """

    def __init__(self, source):
        self.source = source

    def _text(self, node):
        return _ast.get_source_segment(self.source, node) or _ast.unparse(node)

    def _call(self, name, operands, texts, at):
        """`name(*operands, *texts)`: the operands as they are, and what is
        written of them for a message."""
        call = _ast.Call(
            func=_ast.Name(id=name, ctx=_ast.Load()),
            args=[*operands, *(_ast.Constant(value=text) for text in texts)],
            keywords=[],
        )
        _ast.copy_location(call, at)
        return call

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) != 1 or not isinstance(node.ops[0], (_ast.Is, _ast.IsNot)):
            return node
        negated = _ast.Constant(value=isinstance(node.ops[0], _ast.IsNot))
        call = self._call("pll:identical", [node.left, node.comparators[0], negated], [], node)
        return _ast.copy_location(call, node)

    def _statement(self, call, at):
        statement = _ast.Expr(value=call)
        _ast.copy_location(statement, at)
        return statement

    def _key(self, node):
        """A subscript's key as an expression a call can be given: a slice
        written `a:b` is `slice(a, b, None)`."""
        if isinstance(node, _ast.Slice):
            parts = [part if part is not None else _ast.Constant(value=None) for part in (node.lower, node.upper, node.step)]
            return _ast.copy_location(
                _ast.Call(func=_ast.Name(id="pll:slice", ctx=_ast.Load()), args=parts, keywords=[]), node
            )
        if isinstance(node, _ast.Tuple):
            return _ast.copy_location(_ast.Tuple(elts=[self._key(elt) for elt in node.elts], ctx=_ast.Load()), node)
        return node

    def visit_BinOp(self, node):
        self.generic_visit(node)
        symbol = _PLL_BITWISE_SYMBOLS.get(type(node.op))
        if symbol is None:
            return node
        return self._call(
            "pll:bitwise",
            [_ast.Constant(value=symbol), node.left, node.right],
            [self._text(node), self._text(node.left), self._text(node.right)],
            node,
        )

    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        if not isinstance(node.op, _ast.Invert):
            return node
        return self._call("pll:bitwise_not", [node.operand], [self._text(node), self._text(node.operand)], node)

    def visit_AugAssign(self, node):
        written = self._text(node)
        symbol = _PLL_OPERATOR_SYMBOLS.get(type(node.op))
        node.value = self.visit(node.value)
        target = node.target
        if isinstance(target, _ast.Name):
            value = self._call(
                "pll:in_place",
                [_ast.Constant(value=symbol), _ast.Name(id=target.id, ctx=_ast.Load()), node.value],
                [written, target.id, self._text(node.value)],
                node,
            )
            assign = _ast.Assign(targets=[_ast.Name(id=target.id, ctx=_ast.Store())], value=value)
            return _ast.copy_location(assign, node)
        if isinstance(target, _ast.Subscript):
            key_text = self._text(target.slice)
            target.value = self.visit(target.value)
            key = self._key(self.visit(target.slice))
            return self._statement(self._call(
                "pll:setitem_in_place",
                [target.value, key, _ast.Constant(value=symbol), node.value],
                [written, self._text(target.value), key_text, self._text(node.value)],
                node,
            ), node)
        # An attribute: `x.a = pll:attribute_in_place(x, "a", ...)`, so that
        # the assignment is the program's own, which a dataclass's own check
        # sees (`_pll_checked_setattr`).
        call = self._call(
            "pll:attribute_in_place",
            [self.visit(_pll_copy.deepcopy(target.value)), _ast.Constant(value=target.attr), _ast.Constant(value=symbol),
             node.value],
            [written, self._text(target.value), self._text(node.value)],
            node,
        )
        target.value = self.visit(target.value)
        return _ast.copy_location(_ast.Assign(targets=[target], value=call), node)

    def _fetched(self, node, written, arguments):
        """`node.attr`, fetched through `pll:attribute`."""
        value = self.visit(node.value)
        return self._call(
            "pll:attribute",
            [value, _ast.Constant(value=node.attr)],
            [written, self._text(node.value), arguments],
            node,
        )

    def _arguments(self, node):
        """A call's arguments, as written: `x`, `key=len`, `**options`."""
        return tuple(self._text(arg) for arg in node.args) + tuple(
            ("%s=%s" % (k.arg, self._text(k.value))) if k.arg else "**" + self._text(k.value) for k in node.keywords
        )

    def visit_Call(self, node):
        func = node.func
        if isinstance(func, _ast.Attribute) and isinstance(func.ctx, _ast.Load) and func.attr in _PLL_MUTATOR_NAMES:
            node.func = self._fetched(func, self._text(node), self._arguments(node))
        elif isinstance(func, _ast.Name) and func.id in _PLL_LIBRARY_MUTATOR_NAMES:
            node.func = self._call("pll:named", [func], [self._text(node), self._arguments(node)], func)
        else:
            self.generic_visit(node)
            return node
        node.args = [self.visit(arg) for arg in node.args]
        for keyword in node.keywords:
            keyword.value = self.visit(keyword.value)
        return node

    def visit_Name(self, node):
        if isinstance(node.ctx, _ast.Load) and node.id in _PLL_LIBRARY_MUTATOR_NAMES:
            return self._call("pll:named", [node], [node.id, None], node)
        return node

    def _item_targets(self, node):
        """For a loop whose target sets items - `for xs[i] in ...` - a copy
        of each item's container, with what is written of it, taken before
        the loop's own parts are visited."""
        written = "for %s in %s" % (self._text(node.target), self._text(node.iter))
        return [
            (_pll_copy.deepcopy(item.value), written, self._text(item.value), self._text(item.slice))
            for item in _ast.walk(node.target)
            if isinstance(item, _ast.Subscript) and isinstance(item.ctx, _ast.Store)
        ]

    def _into_items(self, node, items):
        """`node.iter`, checked first for each item its target sets."""
        iterable = node.iter
        for container, written, container_text, key_text in items:
            iterable = self._call(
                "pll:iterating_into", [iterable, self.visit(container)], [written, container_text, key_text], node.iter
            )
        return iterable

    def visit_For(self, node):
        items = self._item_targets(node)
        self.generic_visit(node)
        node.iter = self._into_items(node, items)
        return node

    visit_AsyncFor = visit_For

    def visit_comprehension(self, node):
        items = self._item_targets(node)
        self.generic_visit(node)
        node.iter = self._into_items(node, items)
        return node

    def visit_Attribute(self, node):
        if isinstance(node.ctx, _ast.Load) and node.attr in _PLL_MUTATOR_NAMES:
            return self._fetched(node, self._text(node), None)
        self.generic_visit(node)
        return node

    def visit_Assign(self, node):
        if len(node.targets) == 1 and isinstance(node.targets[0], _ast.Subscript):
            target = node.targets[0]
            written, key_text = self._text(node), self._text(target.slice)
            node.value = self.visit(node.value)
            target.value = self.visit(target.value)
            key = self._key(self.visit(target.slice))
            return self._statement(self._call(
                "pll:setitem",
                [target.value, key, node.value],
                [written, self._text(target.value), key_text, self._text(node.value)],
                node,
            ), node)
        # `xs[i], xs[j] = xs[j], xs[i]` and `a = xs[0] = 0`: each item's
        # container is checked before the assignment, which is Python's.
        items = [
            item for target in node.targets for item in _ast.walk(target)
            if isinstance(item, _ast.Subscript) and isinstance(item.ctx, _ast.Store)
        ]
        checks = [
            self._statement(self._call(
                "pll:setitem_check",
                [self.visit(_pll_copy.deepcopy(item.value))],
                [self._text(node), self._text(item.value), self._text(item.slice)],
                node,
            ), node)
            for item in items
        ]
        self.generic_visit(node)
        return checks + [node] if checks else node

    def visit_Delete(self, node):
        kept, checked = [], []
        for target in node.targets:
            if isinstance(target, _ast.Subscript):
                key_text = self._text(target.slice)
                value = self.visit(target.value)
                checked.append(self._statement(self._call(
                    "pll:delitem",
                    [value, self._key(self.visit(target.slice))],
                    ["del " + self._text(target), self._text(target.value), key_text],
                    node,
                ), node))
            else:
                kept.append(self.visit(target))
        if not checked:
            node.targets = kept
            return node
        if kept:
            node.targets = kept
            return [node] + checked
        return checked

    # Annotations: not checked.
    def visit_arg(self, node):
        return node

    def visit_FunctionDef(self, node):
        returns, node.returns = node.returns, None
        self.generic_visit(node)
        node.returns = returns
        return node

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_AnnAssign(self, node):
        if node.value is not None:
            node.value = self.visit(node.value)
        return node


def _pll_is_dataclass_decorator(node):
    """True for `@dataclass`, `@dataclasses.dataclass` and calls to either."""
    if isinstance(node, _ast.Call):
        node = node.func
    if isinstance(node, _ast.Name):
        return node.id == "dataclass"
    if isinstance(node, _ast.Attribute):
        return node.attr == "dataclass"
    return False


class _PllDataclassChecks(_ast.NodeTransformer):
    """Have every `@dataclass` check its fields (`_pll_check_dataclass_fields`).

    `@dataclass` writes `__init__` itself, from the class's annotations, so
    there is no `def` in the source to put a contract on. The checker goes
    on the front of the decorator list, which makes it the outermost one and
    therefore the last to run, so it sees the `__init__` that `@dataclass`
    generated rather than the class before it existed.
    """

    def visit_ClassDef(self, node):
        self.generic_visit(node)
        if any(_pll_is_dataclass_decorator(d) for d in node.decorator_list):
            node.decorator_list.insert(
                0, _ast.Name(id=_PLL_CHECK_DATACLASS_FIELDS, ctx=_ast.Load())
            )
        return node


#: Instances whose `__init__` is running: their fields are checked once it
#: has finished, not one by one as it sets them.
_PLL_CONSTRUCTING = set()

#: The contracts of each checked dataclass's fields, by class: a function
#: that makes them when first asked.
_PLL_DATACLASS_FIELDS = _pll_weakref.WeakKeyDictionary()


def _pll_swapped_field(instance, contracts, field_name):
    """Another field whose value fits here, while this value fits there.

    `ITunesSong("Yesterday", 2015, "The Beatles")` gives `singer` a number
    and `year` a string. Advising `str(...)` for the singer would make the
    error go away and the song wrong; what happened is that two values were
    written in each other's places.
    """
    mine = getattr(instance, field_name)
    for other, contract in contracts.items():
        if other == field_name or not hasattr(instance, other) or isinstance(contract, _PllAnyContract):
            continue
        try:
            if contract.accepts(mine) and contracts[field_name].accepts(getattr(instance, other)):
                return other
        except _PllUnresolved:
            continue
    return None


def _pll_check_field(instance, cls, name, value, contract, frame, contracts, assigned=False):
    """Check one field's value. The code running in `frame` - that made the
    instance, or assigned the field - is the party that answers for it."""
    try:
        if contract.accepts(value):
            return
    except _PllUnresolved:
        # A name in quotes the file has not defined yet: checked once it is.
        return
    party = _pll_party_of_code(frame.f_code)
    step = ("field", name, cls.__name__, contract.written)
    level = (_PLL_CLASS_NAMESPACES.get(cls) or {}).get("__pll_level__")
    blame = _PllBlame(party, party, None, (step,), (frame.f_code.co_filename, frame.f_lineno, None), level)
    try:
        contract.check_now(value, blame)
    except _PllTypeMismatch as error:
        error._pll_facts["check"]["assigned"] = assigned
        swapped = None if assigned else _pll_swapped_field(instance, contracts, name)
        if swapped is not None:
            _pll_add_facts(error, swapped_with=swapped)
        raise error from None


def _pll_field_contracts_of(cls):
    """The field contracts of `cls` or the nearest class it comes from that
    PLL checks - None if there is none."""
    for klass in type.mro(cls):
        made = _PLL_DATACLASS_FIELDS.get(klass)
        if made is not None:
            return made()
    return None


def _pll_checked_setattr(self, name, value):
    """A checked dataclass's `__setattr__`: a field is given a value of its
    annotation, or the assignment is refused - and at `beginner` and
    `intermediate`, whose code makes new values rather than change old ones,
    it is refused once the instance is made, whatever the value."""
    if id(self) not in _PLL_CONSTRUCTING:
        frame = _sys._getframe(1)
        level = frame.f_globals.get("__pll_level__")
        contracts = _pll_field_contracts_of(type(self))
        if level in _PLL_TEACHING_LEVELS and contracts is not None and name in contracts:
            _pll_refuse_field(self, name, level)
        contract = contracts.get(name) if contracts else None
        if contract is not None:
            _pll_check_field(self, type(self), name, value, contract, frame, contracts, assigned=True)
        _pll_field_written()
    object.__setattr__(self, name, value)


def _pll_checked_delattr(self, name):
    _pll_field_written()
    object.__delattr__(self, name)


def _pll_refuse_field(instance, name, level):
    """Refuse setting the field `name` of `instance`, at `level`."""
    kind = type(instance).__name__
    _pll_refuse_mutation("field", kind, "the %s field of a %s" % (name, kind), level, name=name)


def _pll_attribute_in_place(instance, name, symbol, value, written, instance_text, value_text):
    """The new value of `instance.name symbol= value`, which the program
    then assigns, at `beginner` and `intermediate`. A list, a dictionary or
    a set there would be changed in place before that assignment, so it is
    refused here - as setting the field is, for a dataclass's field - and
    so is a bitwise operator between numbers."""
    current = getattr(instance, name)
    kind = _pll_mutable_kind(current)
    if kind is not None:
        level = _pll_level_of_caller()
        contracts = _pll_field_contracts_of(type(instance))
        if contracts is not None and name in contracts:
            _pll_refuse_field(instance, name, level)
        _pll_refuse_mutation("in_place", kind, written, level, symbol=symbol, target="%s.%s" % (instance_text, name),
                             value=value_text)
    if symbol in _PLL_BITWISE and isinstance(current, int) and isinstance(value, int):
        _pll_refuse_bitwise(symbol, written, "%s.%s" % (instance_text, name), value_text, current, value)
    return _PLL_IN_PLACE[symbol](current, value)


_pll_hidden("attribute_in_place", _pll_attribute_in_place)


def _pll_check_dataclass_fields(cls):
    """Check a dataclass's fields against their annotations: all of them once
    its `__init__` has run - defaults, `field(default_factory=...)` and
    `__post_init__` have had their say, and the values checked are the ones
    the instance holds - and each one assigned afterwards.

    A field's annotation is read in the globals the class was defined in, the
    student's, taken from the frame that applied the decorator - not from
    `sys.modules[cls.__module__]`, which is Pyodide's `__main__`, a different
    dict from the session's. It is read when first needed: a recursive
    definition names a class that does not exist yet (`rest: "NumList"`). A
    generic class's own type parameters (`value: T`) stand for any type.
    """
    try:
        namespace = _sys._getframe(1).f_globals
    except Exception:
        namespace = getattr(_sys.modules.get(cls.__module__), "__dict__", {})
    _PLL_CLASS_NAMESPACES[cls] = namespace
    level = namespace.get("__pll_level__")
    typevars = {param: _PllAnyContract(param.__name__) for param in getattr(cls, "__type_params__", ())}
    made, table = {}, {}

    def contracts():
        if not made:
            for field in _pll_dataclasses.fields(cls):
                made[field.name] = _pll_compile(field.type, None, namespace, level, typevars, table=table)
        return made

    _PLL_DATACLASS_FIELDS[cls] = contracts
    original = cls.__init__

    def __init__(self, *args, **kwargs):
        if getattr(self, "__dict__", None) or any(hasattr(self, slot) for slot in getattr(cls, "__slots__", ())):
            # Made before: this changes its fields.
            _pll_field_written()
        _PLL_CONSTRUCTING.add(id(self))
        try:
            original(self, *args, **kwargs)
        finally:
            _PLL_CONSTRUCTING.discard(id(self))
        frame = _sys._getframe(1)
        fields = contracts()
        for name, contract in fields.items():
            if hasattr(self, name):
                _pll_check_field(self, cls, name, getattr(self, name), contract, frame, fields)

    __init__.__name__ = "__init__"
    __init__.__qualname__ = "%s.__init__" % cls.__qualname__
    # So `inspect.signature` gives the fields, not `*args, **kwargs`.
    __init__.__wrapped__ = original
    cls.__init__ = __init__
    params = getattr(cls, "__dataclass_params__", None)
    if cls.__setattr__ is object.__setattr__ and not (params is not None and params.frozen):
        cls.__setattr__ = _pll_checked_setattr
    if cls.__delattr__ is object.__delattr__:
        cls.__delattr__ = _pll_checked_delattr
    if getattr(cls, "__getattr__", None) is None and _pll_can_be_lazy(cls):
        cls.__getattr__ = _pll_lazy_field
        if cls.__getstate__ is object.__getstate__:
            cls.__getstate__ = _pll_whole_state
    return cls


_pll_hidden("check_dataclass_fields", _pll_check_dataclass_fields)


#: Compile-time warnings for the current file: `(line, message)`, each once.
_pll_compile_warnings = []


@contextlib.contextmanager
def _pll_recording_compile_warnings():
    """Record `SyntaxWarning`s from PLL's own parses and compiles instead
    of printing them.

    A run parses and compiles the file more than once - the type-check
    instrumentation is validated by compiling it, then the real compile
    follows - and so does importing one of the student's files, and Python
    prints a `SyntaxWarning` on every one.

    Recorded here, by file and line, and said once, after the run, by
    `_pll_say_compile_warnings`. Any other kind of warning is not PLL's to
    swallow, and is issued again exactly as it was.
    """
    caught = []
    try:
        with _pll_warnings.catch_warnings(record=True) as log:
            _pll_warnings.simplefilter("always", SyntaxWarning)
            try:
                yield
            finally:
                # Copied before `catch_warnings` restores the filters, so a
                # compile that raises still has its warnings kept.
                caught.extend(log)
    finally:
        for warning in caught:
            if issubclass(warning.category, SyntaxWarning):
                entry = (warning.filename, warning.lineno, str(warning.message))
                if entry not in _pll_compile_warnings:
                    _pll_compile_warnings.append(entry)
            else:
                _pll_warnings.warn_explicit(
                    warning.message, warning.category, warning.filename, warning.lineno
                )


@contextlib.contextmanager
def _pll_without_syntax_warnings():
    """For a parse of a file that a run parses too - the static checks',
    the test finder's - which the run's own warnings already cover."""
    with _pll_warnings.catch_warnings():
        _pll_warnings.simplefilter("ignore", SyntaxWarning)
        yield


def _pll_say_compile_warnings(stream, error_message, source="", filename=None):
    """Say each recorded warning once - unless the run's error already did.

    A warning that predicts the error the run then raised (`'int' object is
    not callable; perhaps you missed a comma?` before `TypeError: 'int'
    object is not callable`) is covered by the finding for that error, and
    printing it beside the finding says the same thing worse. One whose
    line never ran is the only sign of the mistake, so that one is said.

    `source` is the text of `filename`, the file run; a warning about a
    file it imported names that file.
    """
    for where, lineno, message in _pll_compile_warnings:
        if error_message and message.startswith(error_message):
            continue
        if filename is None or where == filename:
            stream.write("warning: line %s: %s\n" % (lineno, _pll_reword_warning(message, source, lineno)))
        else:
            stream.write(
                "warning: %s, line %s: %s\n" % (_pll_shown_file(where), lineno, _pll_reword_warning(message))
            )
    del _pll_compile_warnings[:]


def _pll_reword_warning(message, source="", lineno=None):
    """Python's wording, except where it points the wrong way.

    "'int' object is not callable; perhaps you missed a comma?" is Python's
    guess for `3(width)`, and for a number the guess is wrong: what is
    missing is a `*`. For a string or a tuple the comma guess is usually
    right - a list of rows with one comma left out - so those stay.

    The example is the student's own call, from line `lineno` of `source`,
    rather than one fixed example shown whatever they wrote.
    """
    if not _pll_src_re.match(
        r"'(int|float)' object is not callable; perhaps you missed a comma\?", message
    ):
        return message
    meant = _pll_multiplication_on_line(source, lineno)
    if meant is None:
        return (
            "brackets after a number are a function call, not multiplication. "
            "To multiply, write a `*` between them."
        )
    return (
        "brackets after a number are a function call, not multiplication. "
        "To multiply, write the `*`: `%s`, not `%s`." % (meant["product"], meant["written"])
    )


def _pll_multiplication_on_line(source, lineno):
    """The multiplication the first number written before brackets on line
    `lineno` of `source` stands for (`_pll_multiplication_meant`), or None."""
    try:
        with _pll_without_syntax_warnings():
            tree = _ast.parse(source)
    except (SyntaxError, ValueError):
        return None
    calls = sorted(
        (node for node in _ast.walk(tree) if isinstance(node, _ast.Call) and node.lineno == lineno),
        key=lambda node: node.col_offset,
    )
    for call in calls:
        meant = _pll_multiplication_meant(call, source)
        if meant is not None:
            return meant
    return None


def _pll_parse_and_instrument(code, filename, level):
    """Parse `code`, with its `level`'s contracts in force."""
    with _pll_recording_compile_warnings():
        tree = _ast.parse(code, filename=filename, mode="exec")
    return _pll_with_contracts(tree, code, filename, level)


def _pll_with_contracts(tree, code, filename, level):
    """`tree`, with its annotations in force as contracts, at every level but
    `raw`, and what `beginner` and `intermediate` refuse as it runs checked
    - done after any other rewriting, so that the assertion rewriting of a
    test explains a call by the name it was written with.

    Done on a copy, and validated by compiling it: a program PLL cannot
    instrument still runs, unchecked.
    """
    if not _pll_checks_annotations(level):
        return tree
    with _pll_recording_compile_warnings():
        try:
            instrumented = _pll_copy.deepcopy(tree)
            # Before the contracts, so the decorators it looks for are as
            # they were written.
            _PllDataclassChecks().visit(instrumented)
            _PllPlaceholders().visit(instrumented)
            if level in _PLL_TEACHING_LEVELS:
                _PllTeachingChecks(code).visit(instrumented)
            scopes = _PllContractScopes(filename).build(instrumented)
            _PllContracts(scopes, code, filename).visit(instrumented)
            _ast.fix_missing_locations(instrumented)
            # That copies a parent's place onto the nodes pytest's assertion
            # rewriting adds, which can leave a range ending before it starts.
            _pll_fix_ast_ranges(instrumented)
            compile(instrumented, filename, "exec")
            return instrumented
        except Exception as error:
            # PLL's own failure, and never to be silent: a student who
            # annotated the file should know nothing is checking it.
            _pll_compile_warnings.append((
                filename, 1,
                "the annotations in this file are not checked: PLL could not add its checks (%s: %s)"
                % (type(error).__name__, error),
            ))
            return tree


class _PllTopLevelExprWrapper(_ast.NodeTransformer):
    """Wrap module-level expression statements so they auto-display.

    Skips the conventional module docstring (a string literal as the first
    statement) and bare `None` / `...` constants which are usually noise.
    """

    def visit_Module(self, node):
        new_body = []
        for i, stmt in enumerate(node.body):
            if isinstance(stmt, _ast.Expr) and not _pll_should_skip_expr(stmt, i):
                call = _ast.Call(
                    func=_ast.Name(id=_PLL_SHOW_TOP_LEVEL, ctx=_ast.Load()),
                    args=[stmt.value],
                    keywords=[],
                )
                wrapped = _ast.Expr(value=call)
                _ast.copy_location(wrapped, stmt)
                _ast.fix_missing_locations(wrapped)
                new_body.append(wrapped)
            else:
                new_body.append(stmt)
        node.body = new_body
        return node


def _pll_should_skip_expr(stmt, index):
    value = stmt.value
    if isinstance(value, _ast.Constant):
        if index == 0 and isinstance(value.value, str):
            return True  # module docstring
        if value.value is None or value.value is Ellipsis:
            return True
    return False
