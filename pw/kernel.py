"""How places are read: the text helpers the agent tools use to decide what to show a reader and what to propose.

A project states some things in more than one place. A *fact* names such a thing and the places
that state it, and the decision is that all its places read as the same value. That decision, the
record it rests on, and the Lean gate are the Rust build's (rust/, used through pw/core.py): nothing
here judges, and nothing here writes the record.

What is here: locating a place (a Markdown section, a JSON key, a Python name), the ways of reading
one (patterns, Python syntax, TOML and JSON paths), writing a value back through a pattern, the
excerpt and the surroundings shown to a reader, the question a reader is asked, the reader's
instructions (reader.txt) and what calibration measured about readers. pw.discover and
pw.propagate try out ways of reading and edits on text with these before anything is recorded; the
Rust build reads the same way (tests/test_rust.py holds the two against each other).
"""
import ast
import textwrap
import tomllib
import hashlib
import json
import os
import re
import sys
from fractions import Fraction

from scipy.stats import beta

# How a matched piece of text becomes a Lean term.
_KINDS = {"string": "String", "nat": "Nat", "int": "Int", "permille": "Nat"}


def _term(kind, text):
    if kind == "string":
        return text, json.dumps(text, ensure_ascii=False)
    if kind == "nat" and re.fullmatch(r"\d+", text):
        return int(text), str(int(text))
    if kind == "int" and re.fullmatch(r"-?\d+", text):
        return int(text), str(int(text)) if int(text) >= 0 else f"({int(text)})"
    if kind == "permille" and re.fullmatch(r"-?\d+(\.\d+)?", text) and (Fraction(text) * 1000).denominator == 1 and Fraction(text) >= 0:
        return int(Fraction(text) * 1000), str(int(Fraction(text) * 1000))
    raise KernelError(f"{text!r} is not a {kind}")


def _plain(rx, what, groups=None):
    """Refuse what regular-expression engines do not agree on; return the number of groups."""
    if re.search(r"\(\?[=!<P]|\\[1-9]", rx):
        raise KernelError(f"look-around, back-references and named groups are not accepted in {what}")
    if re.search(r"\(\?[a-zA-Z-]+[:)]", rx):
        raise KernelError(f"inline flags such as (?m) are not accepted in {what}; ^ and $ already match at line ends")
    try:
        n = re.compile(rx).groups
    except re.error as e:
        raise KernelError(f"{what} is not a regular expression: {e}")
    if groups is not None and n != groups:
        raise KernelError(f"{what} needs exactly {groups} group: the part in ( ) is what is taken")
    return n


def pattern(find=None, find_all=None, kind="string", sort=False, unique=False, within=None, rewrite=None):
    """A declarative way to read a place: what to look for, and what kind of value it is.

      within    a regular expression with one group that must match exactly once: the search
                is confined to that group. A list of them narrows step by step. Use it to say
                "the list next to --format", when the place holds other lists too.
      find      a regular expression with one group; it must match exactly once, and the
                group is the value
      find_all  the same, but every match counts and the result is a list; it must match at
                least once
      rewrite   [pattern, replacement]: each piece found has to match the pattern as a whole
                and is replaced; the replacement may use \\1 ... \\9 for the pattern's groups
                and nothing else. Use it where a place writes the value another way
                ("py310" for "3.10").
      kind      "string", "nat", "int", or "permille" (a decimal number, as thousandths)
      sort      order the list (strings by code point, numbers by size)
      unique    drop repeated entries

    Nothing is evaluated: the same description means the same thing to any implementation.
    Patterns are limited to what common regular-expression engines agree on (no look-around,
    no back-references, no named groups); `^` and `$` match at line ends.
    """
    if (find is None) == (find_all is None):
        raise KernelError("give exactly one of find and find_all")
    rx = find if find is not None else find_all
    if kind not in _KINDS:
        raise KernelError(f"a value is one of {sorted(_KINDS)}, not {kind!r}")
    _plain(rx, "a pattern", groups=1)
    out = {"language": "pattern", "as": kind}
    out["find" if find is not None else "find_all"] = rx
    if find_all is not None:
        out.update(sort=bool(sort), unique=bool(unique))
    if within:                                   # (keys are added only when used: a reading made before they existed is the same reading)
        steps = [within] if isinstance(within, str) else list(within)
        for step in steps:
            if not isinstance(step, str):
                raise KernelError("`within` is a pattern, or a list of patterns")
            _plain(step, "`within`", groups=1)
        out["within"] = steps
    if rewrite:
        if not (isinstance(rewrite, (list, tuple)) and len(rewrite) == 2 and all(isinstance(x, str) for x in rewrite)):
            raise KernelError("`rewrite` is [pattern, replacement]")
        groups = _plain(rewrite[0], "the pattern of `rewrite`")
        used = [int(d) for d in re.findall(r"\\(.)", rewrite[1]) if d.isdigit()]
        if re.search(r"\\[^1-9\\]|\\$", rewrite[1]) or any(d > groups for d in used):
            raise KernelError("a replacement may use \\1 ... \\9 for groups the pattern has, and \\\\ for a backslash; nothing else")
        out["rewrite"] = [rewrite[0], rewrite[1]]
    return out


def _read_pattern(rd, text):
    text = text.replace("\r\n", "\n")              # a checkout with other line ends is the same text
    for step in rd.get("within", []):
        found = re.findall(step, text, re.M)
        if len(found) != 1:
            raise KernelError(f"`within` matches {len(found)} times here; it has to match exactly once")
        text = found[0]
    found = re.findall(rd.get("find") or rd["find_all"], text, re.M)
    if "rewrite" in rd:
        rx, to = rd["rewrite"]
        for i, piece in enumerate(found):
            m = re.fullmatch(rx, piece)
            if m is None:
                raise KernelError(f"`rewrite` does not match {piece!r} as a whole")
            found[i] = re.sub(r"\\(.)", lambda e: m.group(int(e.group(1))) if e.group(1).isdigit() else e.group(1), to)
    if "find" in rd:
        if len(found) != 1:
            raise KernelError(f"the pattern matches {len(found)} times here; it has to match exactly once")
        return _term(rd["as"], found[0])[1]
    if not found:
        # A list pattern that finds nothing cannot be told from one the text no longer fits
        # (other quotes, other line ends). Reading that as "the place lists nothing" would be
        # believed: an empty list is contained in every list.
        raise KernelError("the pattern matches nothing here; it has to match at least once")
    values = [_term(rd["as"], x) for x in found]
    if rd.get("unique"):
        values = list({v[1]: v for v in values}.values())
    if rd.get("sort"):
        values.sort(key=lambda v: v[0])
    return "[" + ", ".join(v[1] for v in values) + "]"


def _spell(kind, term):
    """How a value is written in a file, for a kind of pattern: the reverse of `_term`."""
    value = json.loads(term)
    if kind == "string" and isinstance(value, str):
        return value
    if kind in ("nat", "int") and isinstance(value, int) and not isinstance(value, bool):
        return str(value)
    if kind == "permille" and isinstance(value, int) and not isinstance(value, bool):
        whole, rest = divmod(value, 1000)
        return f"{whole}.{rest:03d}".rstrip("0").rstrip(".") if rest else f"{whole}.0"
    raise KernelError(f"{term} cannot be written as a {kind}")


def write_pattern(rd, text, term):
    """The text with the value a pattern reads replaced by `term`: reading in reverse.

    Only where the reverse is determined: one value found by `find` (inside `within`, if
    given), not rewritten on the way. The piece the pattern's group matched is replaced and
    nothing else. What was written is read back, and it has to read as `term`: a write that
    the pattern itself does not confirm is not made.
    """
    if rd.get("language") != "pattern" or "find" not in rd or "rewrite" in rd:
        raise KernelError("only a single value read by `find`, without `rewrite`, can be written back")
    start, piece = 0, text
    for step in [*rd.get("within", []), rd["find"]]:
        found = list(re.finditer(step, piece, re.M))
        if len(found) != 1:
            raise KernelError(f"the pattern matches {len(found)} times here; it has to match exactly once")
        a, b = found[0].span(1)
        start, piece = start + a, piece[a:b]
    new = text[:start] + _spell(rd["as"], term) + text[start + len(piece):]
    try:
        back = _read_pattern(rd, new)
    except KernelError as e:
        raise KernelError(f"after writing, the place can no longer be read: {e}")
    if json.loads(back) != json.loads(term):
        raise KernelError(f"after writing, the place reads as {back}, not {term}")
    return new


def _listed(rd, items):
    """Values taken from a parsed file, as a Lean term: one value, or a list."""
    def term(v):
        if rd["as"] == "string":
            if not isinstance(v, str):
                raise KernelError(f"{v!r} is not a string")
            return _term("string", v)
        if isinstance(v, bool) or not isinstance(v, (int, float, str)):
            raise KernelError(f"{v!r} is not a {rd['as']}")
        return _term(rd["as"], str(v))
    if not isinstance(items, list):
        return term(items)[1]
    if not items:
        raise KernelError("nothing is found here; a list has to have at least one entry")
    values = [term(v) for v in items]
    if rd.get("unique"):
        values = list({v[1]: v for v in values}.values())
    if rd.get("sort"):
        values.sort(key=lambda v: v[0])
    return "[" + ", ".join(v[1] for v in values) + "]"


def structure(python=None, data=None, kind="string", sort=False, unique=False, keys=False, public=False, decorator=None,
              call=None, with_=None, keyword=None, fmt=None):
    """A way to read a place by what it is, not by how it is spelled: the syntax of a piece of
    Python, or a path into a TOML or JSON file. Quotes, spacing, line breaks, comments and the
    order of unrelated things do not matter to it, and an entry added in another style is seen.

      python  what to take from the place (a file, or the definition `path::name` names):
                "value"    the literal a name is assigned: "x", 14, ["a", "b"]
                "strings"  every string literal in what a name is assigned: {"a", "b"}, frozenset({...})
                "keys"     the keys of the dictionary a name is assigned
                "names"    the functions defined directly in the place (a module, a class);
                           `public` leaves out names that start with an underscore, `decorator`
                           keeps those carrying that decorator ("mcp.tool")
                "keyword"  the literal passed as `keyword` to the one call of `call` that has
                           `with` among its positional arguments: the default of --model
      data    a dotted path into a .toml or .json file: "package.version". A step may be `*`
              (every entry of a table or array) or `name[key=value]` (the entries of an array of
              tables whose `key` is `value`). `keys` takes the keys found there, not the values.
      kind, sort, unique   as for `pattern`

    Nothing is evaluated: only literals are taken.
    """
    if (python is None) == (data is None):
        raise KernelError("give exactly one of python and data")
    if kind not in _KINDS:
        raise KernelError(f"a value is one of {sorted(_KINDS)}, not {kind!r}")
    out = {"as": kind, "sort": bool(sort), "unique": bool(unique)}
    if python is not None:
        if python not in ("value", "strings", "keys", "names", "keyword"):
            raise KernelError(f'"python" is one of value, strings, keys, names, keyword; not {python!r}')
        out.update(language="python", take=python)
        if python == "names":
            out.update(public=bool(public), **({"decorator": str(decorator)} if decorator else {}))
        elif public or decorator:
            raise KernelError('"public" and "decorator" go with "python": "names"')
        if python == "keyword":
            if not (isinstance(call, str) and isinstance(keyword, str)):
                raise KernelError('"python": "keyword" needs "call" and "keyword" (and "with", to say which call)')
            out.update(call=call, keyword=keyword, **({"with": with_} if with_ is not None else {}))
        elif call or keyword or with_ is not None:
            raise KernelError('"call", "with" and "keyword" go with "python": "keyword"')
    else:
        if fmt not in ("toml", "json"):
            raise KernelError('"data" reads a .toml or .json file (or a .lock file written as TOML)')
        if not isinstance(data, str) or not data or any(not re.fullmatch(r"\*|[^.\[\]=*]+(\[[^.\[\]=*]+=[^.\[\]]*\])?", step) for step in data.split(".")):
            raise KernelError(f'"data" is a dotted path such as package.version, tasks.*, package[name=x].version; not {data!r}')
        out.update(language="data", format=fmt, path=data, keys=bool(keys))
    return out


def _read_python(rd, text):
    try:
        body = ast.parse(textwrap.dedent(text)).body
    except SyntaxError as e:
        raise KernelError(f"the place is not Python that parses: {e.msg}")
    one = body[0] if len(body) == 1 else None
    assigned = one.value if isinstance(one, (ast.Assign, ast.AnnAssign)) else None
    take = rd["take"]

    def literal(node, what):
        try:
            v = ast.literal_eval(node)
        except (ValueError, TypeError, SyntaxError, MemoryError, RecursionError):
            raise KernelError(f"{what} is not written out as a literal")
        return sorted(v, key=repr) if isinstance(v, (set, frozenset)) else list(v) if isinstance(v, tuple) else v

    if take == "names":
        inside = one.body if isinstance(one, ast.ClassDef) else body
        dotted = lambda d: ast.unparse(d.func if isinstance(d, ast.Call) else d)
        return _listed(rd, [n.name for n in inside if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
                            and not (rd.get("public") and n.name.startswith("_"))
                            and (not rd.get("decorator") or any(dotted(d) == rd["decorator"] for d in n.decorator_list))])
    if take == "keyword":
        calls = [c for n in body for c in ast.walk(n) if isinstance(c, ast.Call)
                 and (getattr(c.func, "attr", None) or getattr(c.func, "id", None)) == rd["call"]
                 and ("with" not in rd or any(isinstance(a, ast.Constant) and a.value == rd["with"] for a in c.args))]
        if len(calls) != 1:
            raise KernelError(f"{len(calls)} calls of {rd['call']} fit here; it has to be exactly one")
        given = [k.value for k in calls[0].keywords if k.arg == rd["keyword"]]
        if len(given) != 1:
            raise KernelError(f"the call does not pass {rd['keyword']}")
        return _listed(rd, literal(given[0], f"{rd['keyword']} of {rd['call']}"))
    if assigned is None:
        raise KernelError('the place is not one assignment; name it as path::NAME')
    if take == "value":
        return _listed(rd, literal(assigned, "what is assigned"))
    if take == "keys":
        if not isinstance(assigned, ast.Dict) or any(k is None for k in assigned.keys):
            raise KernelError("what is assigned is not a dictionary written out")
        return _listed(rd, [literal(k, "a key") for k in assigned.keys])
    return _listed(rd, [n.value for n in ast.walk(assigned) if isinstance(n, ast.Constant) and isinstance(n.value, str)])      # strings


def _read_data(rd, text):
    try:
        nodes = [tomllib.loads(text) if rd["format"] == "toml" else json.loads(text)]
    except (ValueError, tomllib.TOMLDecodeError) as e:
        raise KernelError(f"the file does not parse as {rd['format']}: {e}")
    for step in rd["path"].split("."):
        name, _, cond = step.partition("[")
        found = []
        for n in nodes:
            if name == "*":
                found += list(n.values()) if isinstance(n, dict) else list(n) if isinstance(n, list) else []
            elif isinstance(n, dict) and name in n:
                found.append(n[name])
        if cond:
            key, _, want = cond.rstrip("]").partition("=")
            found = [x for n in found for x in (n if isinstance(n, list) else [n]) if isinstance(x, dict) and str(x.get(key)) == want]
        nodes = found
    many = "*" in rd["path"].split(".") or rd["keys"]
    if rd["keys"]:
        if not nodes or not all(isinstance(n, dict) for n in nodes):
            raise KernelError(f"{rd['path']} is not a table here")
        return _listed(rd, [k for n in nodes for k in n])
    if not nodes:
        raise KernelError(f"{rd['path']} is not in the file")
    if many:
        return _listed(rd, [x for n in nodes for x in (n if isinstance(n, list) else [n])])
    if len(nodes) != 1:
        raise KernelError(f"{rd['path']} is found {len(nodes)} times; it has to be exactly one")
    return _listed(rd, nodes[0])


# How a computed place is read, by the kind of description it carries: by a pattern over its
# text, or by its structure (the syntax of Python, a path into TOML or JSON).
READERS = {"pattern": _read_pattern, "python": _read_python, "data": _read_data}


def excerpt(rd, text, least=1500):
    """The part of a long place that a way of reading looks at, as it stands in the file: for a
    blind reader who is to say whether what is read there is the thing asked.
    None where the whole place is to be shown (it is short, or no smaller part can be told).

    A pattern with `within` is shown the lines that `within` matches. A path into TOML names
    tables: the tables it passes through are shown, each from its header to the next. Functions taken by name are shown by their headers. Whatever is shown
    is lines of the file, unchanged, so that a quote from it is a quote from the place.
    """
    if len(text) < least:
        return None
    try:
        if rd.get("language") == "pattern" and rd.get("within"):
            # the lines the first `within` matches, whole, as they stand: what the pattern reads is in them
            found = list(re.finditer(rd["within"][0], text.replace("\r\n", "\n"), re.M))
            if len(found) == 1:
                body = text.replace("\r\n", "\n")
                start = body.rfind("\n", 0, found[0].start()) + 1
                end = body.find("\n", found[0].end())
                shown = body[start:] if end < 0 else body[start:end + 1]
                if len(shown) < len(text) / 2:
                    return shown
        if rd.get("language") == "data" and rd.get("format") == "toml":
            lines = text.splitlines(keepends=True)
            starts = [0] + [i for i, line in enumerate(lines) if line.lstrip().startswith("[") and i > 0]
            pieces = ["".join(lines[a:b]) for a, b in zip(starts, starts[1:] + [len(lines)])]
            kept = []
            for piece in pieces:
                try:
                    _read_data(rd, piece)
                    kept.append(piece)
                except KernelError:
                    pass
            shown = "".join(kept)
            if kept and _read_data(rd, shown) == _read_data(rd, text) and len(shown) < len(text) / 2:
                return shown
        if rd.get("language") == "python" and rd.get("take") == "names":
            src = textwrap.dedent(text)
            if src != text:
                return None
            body = ast.parse(src).body
            cls = body[0] if len(body) == 1 and isinstance(body[0], ast.ClassDef) else None
            inside = cls.body if cls else body
            lines = text.splitlines(keepends=True)
            heads = [lines[cls.lineno - 1]] if cls else []
            for n in inside:
                if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    first = min([n.lineno] + [d.lineno for d in n.decorator_list])
                    heads.append("".join(lines[first - 1:n.body[0].lineno - 1]) or lines[n.lineno - 1])
            shown = "".join(heads)
            if heads and len(shown) < len(text) / 2:
                return shown
    except (KernelError, SyntaxError, ValueError):
        return None
    return None


def reader(read, at):
    """The way of reading a place that its declaration describes ("read" in pw-facts.json)."""
    r = dict(read)
    if "python" in r or "data" in r:
        extra = set(r) - {"python", "data", "as", "sort", "unique", "keys", "public", "decorator", "call", "with", "keyword"}
        if extra:
            raise KernelError(f"{at}: unknown keys in \"read\": {sorted(extra)}")
        ext = os.path.splitext(at.partition("::")[0])[1]
        if "python" in r and ext != ".py":
            raise KernelError(f'{at}: "python" reads a .py file')
        if "data" in r and "::" in at:
            raise KernelError(f'{at}: "data" reads a whole file; put the path into "data", not after ::')
        return structure(r.get("python"), r.get("data"), r.get("as", "string"), r.get("sort", False), r.get("unique", False),
                         r.get("keys", False), r.get("public", False), r.get("decorator"), r.get("call"), r.get("with"), r.get("keyword"),
                         {".toml": "toml", ".lock": "toml", ".json": "json"}.get(ext))
    extra = set(r) - {"find", "find_all", "as", "sort", "unique", "within", "rewrite"}
    if extra:
        raise KernelError(f"{at}: unknown keys in \"read\": {sorted(extra)}")
    return pattern(r.get("find"), r.get("find_all"), r.get("as", "string"), r.get("sort", False), r.get("unique", False), r.get("within"), r.get("rewrite"))


def compute(rd, text):
    how = READERS.get(rd.get("language"))
    if how is None:
        raise KernelError(f"no way to read a place by {rd.get('language')!r}; the record may come from another version")
    return how(rd, text)


def cli(main):
    """Run a command; say what is wrong with the declaration or the setup in a line, not a traceback.
    Exit status 2: the check could not be made (1 is for a check that was made and failed)."""
    from .core import GateError
    try:
        main()
    except (KernelError, GateError) as e:
        print(f"pw: {e}", file=sys.stderr)
        sys.exit(2)


class KernelError(Exception):
    pass


def _sha(*parts):
    return hashlib.sha256("\x00".join(parts).encode()).hexdigest()[:10]


LOG = "pw-log.jsonl"     # the record, kept in the repository it is about
RULES = "pw-rules.json"              # a project's own decision about when a reading stands
CALIBRATION = "pw-calibration.json"  # what pw.calibrate measured about the readers

# What a blind reader is told. A reader is a model together with these instructions: what was
# measured about a model under other instructions says nothing about this reader.
with open(os.path.join(os.path.dirname(__file__), "reader.txt"), encoding="utf-8") as _fh:
    READER = _fh.read()
INSTRUCTIONS = _sha(READER)


def interval(k, n, level=0.95):
    """Clopper-Pearson interval for a proportion: what the counts allow, with no prior."""
    a = (1 - level) / 2
    return (0.0 if k == 0 else float(beta.ppf(a, k, n - k + 1)), 1.0 if k == n else float(beta.ppf(1 - a, k + 1, n - k)))


def reader_measurements(cwd, instructions=INSTRUCTIONS):
    """Per reader model: every measurement made in this repository under the given instructions
    (by default the ones readers are given now), added up. Not the latest run alone: measuring
    again until a run comes out well must not help. The rates are computed here from the counts.
    With instructions=None: per (model, instructions), for every instructions measured under."""
    path = os.path.join(cwd, CALIBRATION)
    if not os.path.exists(path):
        return {}
    with open(path, encoding="utf-8") as fh:
        runs = [r for r in json.load(fh) if instructions is None or r.get("instructions") == instructions]
    out = {}
    for r in runs:
        who = r["model"] if instructions is not None else (r["model"], r.get("instructions"))
        m = out.setdefault(who, {"runs": 0, "planted": 0, "read": 0, "stuck": 0, "decoys": 0, "accepted": 0, "twice": 0, "picked": 0})
        m["runs"] += 1
        for key, src, name in (("planted", "planted", "n"), ("read", "planted", "read"), ("stuck", "planted", "stuck"),
                               ("decoys", "decoys", "n"), ("accepted", "decoys", "accepted"), ("twice", "twice", "n"), ("picked", "twice", "picked")):
            m[key] += r.get(src, {}).get(name, 0)
    for m in out.values():
        if m["planted"]:
            m["read rate"], m["stuck rate"] = interval(m["read"], m["planted"]), interval(m["stuck"], m["planted"])
        if m["decoys"]:
            m["accept rate"] = interval(m["accepted"], m["decoys"])
        if m["twice"]:
            m["pick rate"] = interval(m["picked"], m["twice"])
    return out


def _md_section(text, title):
    """The section under the heading `title`: up to the next heading of the same or a higher level."""
    lines, fenced, start, level = text.splitlines(keepends=True), False, None, 0
    for i, line in enumerate(lines):
        if line.lstrip().startswith("```"):
            fenced = not fenced
        m = None if fenced else re.match(r"(#+)\s+(.*?)\s*#*\s*$", line)
        if not m:
            continue
        if start is None and m.group(2).strip() == title.strip():
            start, level = i, len(m.group(1))
        elif start is not None and len(m.group(1)) <= level:
            return "".join(lines[start:i])
    return None if start is None else "".join(lines[start:])


def _json_part(text, keys):
    part = json.loads(text)
    for key in keys.split("."):
        part = part[int(key)] if isinstance(part, list) else part[key]
    return json.dumps(part, sort_keys=True, ensure_ascii=False)


def _py_part(text, name):
    """The source of a definition or assignment, by dotted name (Class.method)."""
    body = ast.parse(text).body
    node = None
    for part in name.split("."):
        node = next((n for n in body if getattr(n, "name", None) == part
                     or (isinstance(n, ast.Assign) and any(getattr(t, "id", None) == part for t in n.targets))), None)
        if node is None:
            return None
        body = getattr(node, "body", [])
    return ast.get_source_segment(text, node)


def locate(subject, cwd):
    """The content a subject names, as bytes; None if the file is not there.

    A subject is `path` or `path::part`. The part is a heading in Markdown, a dotted key in
    JSON, a dotted name in Python. For any other kind of file, or a part that cannot be found,
    the subject is the whole file: every file can be a subject, whatever is in it.
    """
    path, _, part = subject.partition("::")
    full = os.path.join(cwd, path)
    if not os.path.isfile(full):
        return None
    with open(full, "rb") as fh:
        raw = fh.read()
    found = None
    if part:
        try:
            text = raw.decode("utf-8")
            if path.endswith((".md", ".markdown")):
                found = _md_section(text, part)
            elif path.endswith(".json"):
                found = _json_part(text, part)
            elif path.endswith(".py"):
                found = _py_part(text, part)
        except (UnicodeDecodeError, ValueError, SyntaxError, KeyError, IndexError, TypeError):
            found = None
    return raw if found is None else found.encode("utf-8")


def _json_like(typ):
    """Is a value of this type written the same way in JSON and in Lean (a string, a number, a list of them)?"""
    return typ in ("String", "Nat", "Int", "List String", "List Nat", "List Int")


def _literal(typ, text):
    """Is `text` a plain value of a type that is written the same way in JSON and in Lean:
    a number, a string, a list of them, and nothing that Lean would have to compute?"""
    if typ.endswith("Int"):
        text = re.sub(r"\((-\d+)\)", r"\1", text)       # Lean writes a negative number in parentheses
    try:
        value = json.loads(text)
    except ValueError:
        return False
    one = {"String": lambda v: isinstance(v, str),
           "Nat": lambda v: isinstance(v, int) and not isinstance(v, bool) and v >= 0,
           "Int": lambda v: isinstance(v, int) and not isinstance(v, bool)}[typ.removeprefix("List ")]
    return isinstance(value, list) and all(map(one, value)) if typ.startswith("List ") else one(value)


def _written(typ, text):
    """The value a written-out term stands for: (True, value), or (False, None) if the term is
    not a plain value of a type that is written the same way in JSON and in Lean."""
    if not _json_like(typ) or not _literal(typ, text):
        return False, None
    return True, json.loads(re.sub(r"\((-\d+)\)", r"\1", text) if typ.endswith("Int") else text)


def unreadable(subject, cwd):
    """Why a declared place cannot be found as named, or None. `locate` falls back to the whole
    file when a part is not there; for a place someone declared, that fallback would quietly
    read something else."""
    path, _, part = subject.partition("::")
    full = os.path.join(cwd, path)
    if not os.path.isfile(full):
        return f"{path} is no longer there"
    if not part or not path.endswith((".md", ".markdown", ".json", ".py")):
        return None
    try:
        with open(full, encoding="utf-8") as fh:
            text = fh.read()
        found = (_md_section if path.endswith((".md", ".markdown")) else _json_part if path.endswith(".json") else _py_part)(text, part)
    except (UnicodeDecodeError, ValueError, SyntaxError, KeyError, IndexError, TypeError):
        found = None
    return None if found is not None else f"{path} no longer has a part named {part!r}"


def context(subject, cwd, small=300, lines=8):
    """What surrounds a place that is too small to tell what it belongs to; None otherwise.

    A JSON key's value alone ("0.85") could be an answer to many questions. Its enclosing object,
    or the lines around a short definition, show what it is. This is for a reader's orientation
    only: what the place says still has to be in the place.
    """
    path, _, part = subject.partition("::")
    content = locate(subject, cwd)
    if not part or content is None or len(content) > small:
        return None
    with open(os.path.join(cwd, path), encoding="utf-8") as fh:
        text = fh.read()
    try:
        if path.endswith(".json"):
            around = json.loads(text)
            for key in part.split(".")[:-1]:
                around = around[int(key)] if isinstance(around, list) else around[key]
            return json.dumps(around, indent=1, ensure_ascii=False)[:2500]
    except (ValueError, KeyError, IndexError, TypeError):
        return None
    at = text.find(content.decode("utf-8"))
    if at < 0:
        return None
    before, after = text[:at].splitlines(keepends=True), text[at + len(content):].splitlines(keepends=True)
    return ("".join(before[-lines:]) + content.decode("utf-8") + "".join(after[:lines + 1]))[:2500]


def _anchored(quote, subject, cwd):
    """Is the quote in the content the subject names, word for word (spacing aside)?"""
    content = locate(subject, cwd)
    return content is not None and " ".join(quote.split()) in " ".join(content.decode("utf-8", "replace").split())


def subject_id(subject, cwd):
    """The subject plus a hash of what it names. A reading holds for exactly this content:
    it dies when the content changes, and is untouched by changes elsewhere in the file."""
    content = locate(subject, cwd)
    return subject if content is None else f"{subject}@{hashlib.sha256(content).hexdigest()[:10]}"


def _norm(text):
    return " ".join(text.split())


SOME = (" This passage is only expected to mention some of them (it is an example, an excerpt, a list of highlights): "
        "give the ones it mentions, and none it does not.")


def question(fact, place):
    """What a reader of this place is asked, and the identity of that question.

    A place declared to state only some entries of a list is asked another question than one
    that states the whole list, so a reading of the one is not an answer to the other."""
    text = f'{fact["name"]}: {fact["text"]}'
    return (text + SOME, _sha(fact["asked"], "some")) if place.get("some") else (text, fact["asked"])
