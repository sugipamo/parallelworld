"""Tiny propositional formula language over atom ids.

Syntax:  !a   a & b   a | b   a -> b   a <-> b   ( ... )
Atom ids match [A-Za-z_][A-Za-z0-9_.:~]* (e.g. H:ab12, G:ab12~cd34).
"""
import re
import numpy as np

_TOK = re.compile(r"\s*(<->|->|[!&|()]|[A-Za-z_][A-Za-z0-9_.:~]*)")


def _tokens(s):
    pos, out = 0, []
    s = s.rstrip()
    while pos < len(s):
        m = _TOK.match(s, pos)
        if not m:
            raise ValueError(f"bad formula at {pos}: {s[pos:pos+20]!r}")
        out.append(m.group(1))
        pos = m.end()
    return out


def parse(s):
    toks = _tokens(s)
    i = 0

    def peek():
        return toks[i] if i < len(toks) else None

    def eat(t=None):
        nonlocal i
        tok = peek()
        if tok is None or (t and tok != t):
            raise ValueError(f"expected {t or 'token'}, got {tok!r}")
        i += 1
        return tok

    def iff():
        left = imp()
        while peek() == "<->":
            eat()
            left = ("iff", left, imp())
        return left

    def imp():
        left = or_()
        if peek() == "->":
            eat()
            return ("imp", left, imp())
        return left

    def or_():
        left = and_()
        while peek() == "|":
            eat()
            left = ("or", left, and_())
        return left

    def and_():
        left = unary()
        while peek() == "&":
            eat()
            left = ("and", left, unary())
        return left

    def unary():
        tok = peek()
        if tok == "!":
            eat()
            return ("not", unary())
        if tok == "(":
            eat()
            e = iff()
            eat(")")
            return e
        if tok is None or tok in ("&", "|", "->", "<->", ")"):
            raise ValueError(f"unexpected {tok!r}")
        return ("atom", eat())

    e = iff()
    if i != len(toks):
        raise ValueError(f"trailing tokens: {toks[i:]}")
    return e


def atoms(e):
    if e[0] == "atom":
        return {e[1]}
    return set().union(*(atoms(x) for x in e[1:]))


def rename(e, f):
    if e[0] == "atom":
        return ("atom", f(e[1]))
    return (e[0],) + tuple(rename(x, f) for x in e[1:])


def evaluate(e, env):
    """env maps atom id -> bool or numpy bool array."""
    op = e[0]
    if op == "atom":
        return env[e[1]]
    if op == "not":
        return np.logical_not(evaluate(e[1], env))
    a, b = evaluate(e[1], env), evaluate(e[2], env)
    if op == "and":
        return np.logical_and(a, b)
    if op == "or":
        return np.logical_or(a, b)
    if op == "imp":
        return np.logical_or(np.logical_not(a), b)
    if op == "iff":
        return np.equal(a, b)
    raise ValueError(op)
