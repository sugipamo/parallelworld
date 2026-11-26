"""The kernel: an append-only record, and the one decision it holds.

A project states some things in more than one place: a default in the code and in the
documentation, a version in two configuration files, a list the manual enumerates and the code
defines. A *fact* names such a thing and the places that state it. The decision is that all its
places read as the same value. Nothing else is decided here.

  how a place is read    by a declared pattern (computed afresh at every check), or by a reader:
                         an agent shown that place and nothing else, or a person
  whether places agree   an equation between the values read, settled by Lean (lean_gate.py)
  whether a reading      a table of rules the project writes (pw-rules.json), over conditions the
  stands                 kernel establishes from the record and the files; no number is computed,
                         except the bounds a reader's measurement allows, compared with a bar

The record is one JSON object per line, appended and never rewritten. What in it can be checked
again is not believed: patterns are re-run at every check, proofs with `verify`.
"""
import ast
import textwrap
import tomllib
import fcntl
import hashlib
import json
import os
import re
import time
from contextlib import contextmanager
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


class KernelError(Exception):
    pass


def _sha(*parts):
    return hashlib.sha256("\x00".join(parts).encode()).hexdigest()[:10]


LOG = "pw-log.jsonl"     # the record, kept in the repository it is about
RULES = "pw-rules.json"              # a project's own decision about when a reading stands
CALIBRATION = "pw-calibration.json"  # what pw.calibrate measured about the readers

# What can be said of a reading, and so what a rule may ask for.
CONDITIONS = {
    "computed": "the place is read by a declared pattern",
    "confirmed by a person": "a person compared the reading with the place",
    "blind": "read by a measured reader that was shown the place and nothing else",
    "words occur in the place": "the value read occurs literally in the quoted sentence (a list: in the place)",
    "agrees with a computed place": "another place of the fact, read by a pattern, has the same value",
    "agrees with another place read blind": "another place of the fact, read blind in another session, has the same value",
    "read the same by a second model": "two measured readers of different models, each blind, read this place the same",
    "read the same blind": "a computed place: a measured reader, shown the place and nothing else, read off it what the pattern computes",
    "contained in a computed place": "a place that lists only some entries: every entry it lists is in a place of the fact read by a pattern",
}


def load_rules(cwd):
    """The rules for when a reading stands: the repository's own, or the default ones."""
    own = os.path.join(cwd, RULES)
    with open(own if os.path.exists(own) else os.path.join(os.path.dirname(__file__), "rules.json"), encoding="utf-8") as fh:
        rules = json.load(fh)
    for rule in rules["a reading stands if any of"]:
        unknown = [c for c in rule if c not in CONDITIONS]
        if unknown or not rule:
            raise KernelError(f"a rule may ask for {sorted(CONDITIONS)}; not {unknown}")
    return rules


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


def measured_readers(cwd, rules):
    """The readers whose measurements in this repository, taken together, meet the rules' bar.
    A reader is a model with the instructions it was given: {(model, instructions)}."""
    bar = rules["a blind reader counts if measured"]
    limits = {"read at least": ("read rate", 0, 1), "stuck at most": ("stuck rate", 1, -1),
              "takes another thing for it at most": ("accept rate", 1, -1),
              "picks one of two values at most": ("pick rate", 1, -1)}
    unknown = set(bar) - set(limits)
    if unknown:
        raise KernelError(f"a reader can be asked for {sorted(limits)}; not {sorted(unknown)}")
    # a rate that was not measured does not meet a bar on it
    return {reader for reader, run in reader_measurements(cwd, None).items()
            if all(key in run and sign * run[key][end] >= sign * bar[name] for name, (key, end, sign) in limits.items() if name in bar)}


def _counted(info, measured):
    """The models among a reading's blind readers that count: those measured under the
    instructions they read it under. A reading recorded before instructions were noted counts
    if its model is measured under any."""
    return {m for m in info["models"]
            if any((m, i) in measured if i else any(x == m for x, _ in measured) for i in info.get("under", {}).get(m) or [None])}


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


class State:
    """What the record says, replayed from its lines."""
    def __init__(self):
        self.facts = {}          # H id -> {"name", "type", "places": [{"at", "reader"}], "instructions"?, "asked", "text",
        #                                   "readings": [(place, M)], "declined": [...], "agreed": [(guards, F)]}
        self.models = {}         # M id -> one way a place was read: {"subject", "obj", "binding", "quote", "anchor", ...}
        self.objs = {}           # O id -> {"type", "text"}: a value, as a Lean term
        self.props = {}          # F id -> the Lean proposition that some readings agree
        self.verdict = {}        # F id -> {"holds"} or {"not"}, as the recorded proofs say (both: one of them is not Lean's)
        self.proofs = []         # proof events as recorded
        self.confirmations = {}  # id -> a person's confirmation or rejection of a reading
        self.withdrawn = {}      # H id -> why the fact is no longer declared

    def apply(self, typ, p):
        if typ == "claim":
            if "fact" not in p:
                raise KeyError("a claim that is not a fact")
            was = self.facts.get(p["h"], {})
            fact = dict(p["fact"], text=p["text"], **{k: was.get(k, []) for k in ("readings", "declined", "agreed")})
            if fact.pop("value", None) is not None:      # an earlier form: one fixed value, said by nobody in particular
                raise KeyError("a fact with a fixed value; say whose instruction it is under \"instructions\"")
            if "asked" not in fact:         # recorded before descriptions were tracked: the text is the description, if one was given
                given = p["text"] != f'the same {fact["name"]} is stated in {len(fact["places"])} place(s)'
                fact["asked"] = _sha("asked", p["text"] if given else "")
            self.facts[p["h"]] = fact
            self.withdrawn.pop(p["h"], None)     # declared again
        elif typ == "reading":
            self.objs.setdefault(p["obj"]["id"], {"type": p["obj"]["type"], "text": p["obj"]["text"]})
            if p["m"] not in self.models:
                self.models[p["m"]] = {"subject": p["subject"], "obj": p["obj"]["id"], "binding": p.get("binding"),
                                       "quote": p.get("quote"), "anchor": p.get("anchor", False),
                                       "by": set(), "blind": set(), "models": set(), "under": {}, "literal": False, "asked": {}}
            # A reading answers a question: the fact's description as it was when the place was read.
            # Who read it is kept per question, so that an answer to another question is not counted.
            asked = p.get("asked") or self.facts[p["h"]]["asked"]
            for info in (self.models[p["m"]], self.models[p["m"]]["asked"].setdefault(asked, {"by": set(), "blind": set(), "models": set(), "under": {}})):
                info["by"].add(p.get("actor", "anon"))                 # who read it this way
                if p.get("blind"):
                    info["blind"].add(p.get("actor", "anon"))          # ...shown nothing but the place
                    if p.get("model"):
                        info["models"].add(p["model"])                 # ...and which model that reader was
                        info["under"].setdefault(p["model"], set()).add(p.get("instructions"))     # ...given which instructions
            info = self.models[p["m"]]
            info["literal"] = info["literal"] or bool(p.get("literal"))
            if (p["place"], p["m"]) not in self.facts[p["h"]]["readings"]:
                self.facts[p["h"]]["readings"].append((p["place"], p["m"]))
        elif typ == "decline":
            self.facts[p["h"]]["declined"].append({**{k: p.get(k) for k in ("place", "subject", "actor", "model", "blind", "why")},
                                                   "asked": p.get("asked") or self.facts[p["h"]]["asked"]})
        elif typ == "agree":
            self.props.setdefault(p["f"], p["lean"])
            self.facts[p["h"]]["agreed"].append((tuple(p["guards"]), p["f"]))
        elif typ == "proof":
            f, = p["args"]
            if p["relation"] not in ("holds", "not"):
                raise KeyError(f"a proof of {p['relation']}")
            self.proofs.append(p)
            self.verdict.setdefault(f, set()).add(p["relation"])
        elif typ == "observe":
            if p["kind"] != "sign_off":
                raise KeyError(f"evidence of kind {p['kind']}")
            self.confirmations[p["eid"]] = p
        elif typ == "withdraw":
            self.withdrawn[p["h"]] = p["justification"]
        else:
            raise KeyError(f"an event of type {typ}")


class Kernel:
    def __init__(self, db_path, gate=None, actor=None):
        self.db_path = db_path
        self.gate = gate
        self.actor = actor or os.environ.get("PW_AGENT", "anon")
        os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)

    # ---- event log -------------------------------------------------------
    # One JSON object per line, appended and never rewritten, so that it can live in the
    # repository next to what it is about: readings and confirmations travel with the commits,
    # and two branches that both appended can be merged by keeping both sets of lines.
    @contextmanager
    def _tx(self):
        """Exclusive section: replay + check + append is atomic across processes."""
        with open(self.db_path, "a+", encoding="utf-8") as fh:
            fcntl.flock(fh, fcntl.LOCK_EX)
            try:
                fh.seek(0)
                state = State()
                for n, line in enumerate(fh, 1):
                    if line.strip():
                        try:
                            event = json.loads(line)
                            state.apply(event["type"], event)
                        except (ValueError, KeyError) as e:
                            raise KernelError(f"{self.db_path}, line {n}: not a readable event ({e})")
                yield fh, state
            finally:
                fh.flush()
                fcntl.flock(fh, fcntl.LOCK_UN)

    def _append(self, fh, state, typ, payload):
        event = {"ts": round(time.time(), 3), "actor": self.actor, "type": typ, **payload}
        fh.write(json.dumps(event, ensure_ascii=False) + "\n")
        state.apply(typ, event)

    def state(self):
        with self._tx() as (_, state):
            return state

    def events(self):
        with open(self.db_path, encoding="utf-8") as fh:
            return [{"id": n, **json.loads(line)} for n, line in enumerate(fh, 1) if line.strip()]

    def verify(self, proofs=None):
        """Run every recorded proof (or just `proofs`, taken from the record) through the gate
        again; return those it does not accept.

        The log is a text file anyone can edit. Whatever in it can be checked again is not
        taken on trust: readers are re-run on every check, and proofs are re-run here.
        What cannot be re-run, a person's confirmation above all, is only as good as the
        review of the commit that added the line.
        """
        if self.gate is None:
            raise KernelError("no Lean gate configured; proofs cannot be verified")
        st = self.state()
        refused = []
        proofs = list(st.proofs if proofs is None else proofs)
        verdicts = self.gate.check_many([(p["relation"], [("Prop", st.props[p["args"][0]])], p.get("proof", "")) for p in proofs])
        for p, verdict in zip(proofs, verdicts):
            if not verdict["ok"]:
                refused.append({"relation": p["relation"], "args": p["args"], "reason": verdict["reason"][-300:]})
        return refused


    # ---- facts: one thing, said in several places -----------------------------
    def claim_fact(self, name, typ, places, gloss="", instructions=(), defined=None):
        """Declare that the listed places all state the same fact, a value of Lean type `typ`.

        Each place is `path` or `path::part`, optionally with a reader that computes the value
        from the content; a place without one has to be read by an agent or a person. The
        decision is that all places read as the same value. No place is privileged: when they
        differ, which one is right is for a person to say.

        A person may have said it already. `instructions` are what people have laid down about
        this fact: [{"is": the value as a Lean term, "by": who, "said"?: their words, "on"?: when}].
        They are axioms here: nothing in the files can show one wrong, and the places are held
        against them. Two that Lean shows to differ are both set aside until a person withdraws
        one (see `_recheck_fact`): the kernel does not choose between people.

        `defined` makes the fact a definition: {"from": [names of other facts], "as": a Lean
        function of their values}. Its value is then nothing new, only what the function gives
        for the values of those facts, and its places are held against that. A definition adds
        no claim of its own, so it cannot be at odds with an instruction; and for the same
        reason it takes none: lay down the facts it is defined from.
        """
        typ = _norm(typ)
        self._screen(typ)
        places = [{"at": p, "reader": None} if isinstance(p, str) else
                  {"at": p["at"], "reader": p.get("reader"), **({"some": True} if p.get("some") else {})} for p in places]
        if not [p for p in places if not p.get("some")]:
            raise KernelError("a fact needs at least one place that states the whole of it")
        twice = sorted({p["at"] for p in places if [q["at"] for q in places].count(p["at"]) > 1})
        if twice:
            raise KernelError(f"{name}: {', '.join(twice)} is listed more than once; a place is read one way per fact")
        if any(p.get("some") for p in places) and not typ.startswith("List "):
            raise KernelError("only a list can be stated in part: a place that states some entries needs a List type")
        said = []
        for i in instructions:
            if not isinstance(i, dict) or set(i) - {"is", "by", "said", "on"} or not str(i.get("by", "")).strip() or "is" not in i:
                raise KernelError(f'{name}: an instruction is {{"is": value, "by": who}}, optionally with "said" and "on"')
            term = _norm(i["is"])
            self._screen(term)
            self._well_typed((typ, term))
            said.append({"is": term, "by": _norm(str(i["by"])), **{k: _norm(str(i[k])) for k in ("said", "on") if i.get(k)}})
        if len({(i["is"], i["by"]) for i in said}) < len(said):
            raise KernelError(f"{name}: the same instruction by the same person is listed twice")
        # `asked` identifies the question put to whoever reads a place: the description. When it
        # changes, what was read before answered another question and has to be read again.
        if defined is not None:
            if (not isinstance(defined, dict) or set(defined) != {"from", "as"} or not isinstance(defined["as"], str)
                    or not isinstance(defined["from"], list) or not defined["from"] or not all(isinstance(x, str) for x in defined["from"])):
                raise KernelError(f'{name}: a definition is {{"from": [names of facts], "as": a Lean function of their values}}')
            if said:
                raise KernelError(f"{name}: its value comes from its definition; an instruction belongs to the facts it is defined from")
            if name in defined["from"]:
                raise KernelError(f"{name} is defined from itself")
            self._screen(defined["as"])
            defined = {"from": list(defined["from"]), "as": _norm(defined["as"])}
        fact = {"name": name, "type": typ, "places": places, "asked": _sha("asked", _norm(gloss)),
                **({"instructions": said} if said else {}), **({"defined": defined} if defined else {})}
        h = "H:" + _sha("fact", name, typ)       # the same fact, however its places come to be listed or read
        with self._tx() as (con, st):
            declared = {k: v for k, v in st.facts.get(h, {}).items() if k not in ("readings", "declined", "agreed", "text")}
            if declared != fact or h in st.withdrawn:
                self._append(con, st, "claim", {
                    "h": h, "text": _norm(gloss) or f"the same {name} is stated in {len(places)} place(s)", "fact": fact})
        return {"h": h}

    def read_place(self, h, place, obj=None, cwd=None, quote=None, blind=False, model=None):
        """Record how one place of a fact reads, for its content as it is now. Without `obj`
        the place's reader computes it.

        `quote` is the sentence (or table row) of the place that says it, word for word. The
        kernel checks that it is there. A reading of a single value stays valid for as long as
        its quote stays in the place: other edits to the same place do not call for reading it
        again. (The price: something added elsewhere in the place that says otherwise goes
        unnoticed.) A list is read off the whole place, so a quote shows one entry of it and
        any change to the place calls for reading it again.

        `blind` says the reader was shown this place and nothing else. Only then does it mean
        anything that the reading agrees with what another place says: a reader who could
        look at the other place might simply have copied it.
        """
        st = self.state()
        if h not in st.facts:
            raise KernelError(f"{h} is not a fact")
        fact = st.facts[h]
        decl = next((p for p in fact["places"] if p["at"] == place), None)
        if decl is None:
            raise KernelError(f"{place} is not a place of this fact; its places are {[p['at'] for p in fact['places']]}")
        if cwd is None or locate(place, cwd) is None:
            raise KernelError(f"{place} is not there")
        how = decl["reader"] if obj is None else None
        if obj is None:
            if how is None:
                raise KernelError(f"{place} has no reader; state what it says")
            obj = compute(how, locate(place, cwd).decode("utf-8", "replace"))
        if quote is not None and not _anchored(quote, place, cwd):
            raise KernelError("the quote is not in the place word for word")
        obj = _norm(obj)
        self._screen(obj)
        if how is None and _json_like(fact["type"]) and not _literal(fact["type"], obj):
            # What a reader says a place states is a value, not a computation. Anything else would
            # be text from outside handed to Lean to evaluate, with only a list of refused words in between.
            raise KernelError(f"state the value itself, written out: a {fact['type']} such as "
                              + {"S": '"fast"', "N": "14", "I": "-3", "L": '["a", "b"] or [1, 2]'}[fact["type"][0]])
        ob = {"id": "O:" + _sha(fact["type"], obj), "type": fact["type"], "text": obj}
        if ob["id"] not in st.objs:                  # (a value read before was put to Lean then; what rests on it is settled by a proof either way)
            self._well_typed((fact["type"], obj))
        version = subject_id(place, cwd)
        # a reading answers a question: the same place read for another fact is another hypothesis
        m = "M:" + _sha(h, version, ob["id"], json.dumps(how, sort_keys=True, ensure_ascii=False) if how else "")
        literal = False
        if how is None:                              # do the words read actually occur there?
            try:
                said = json.loads(obj)
                where = quote if quote is not None and not isinstance(said, list) else locate(place, cwd).decode("utf-8", "replace")
                literal = all(str(x) in where for x in (said if isinstance(said, list) else [said]))
            except ValueError:
                pass
        asked = question(fact, decl)[1]
        with self._tx() as (con, st):
            known = st.models.get(m, {}).get("asked", {}).get(asked, {})     # as an answer to the question as it is now
            # who read it matters only for a reading someone stated; a computed one is the same whoever runs it
            if ((place, m) not in st.facts[h]["readings"]
                    or (how is None and (self.actor not in known.get("by", ()) or (blind and self.actor not in known.get("blind", ()))
                                         or (blind and model and INSTRUCTIONS not in known.get("under", {}).get(model, ()))))):
                self._append(con, st, "reading", {
                    "h": h, "place": place, "subject": version, "m": m, "obj": ob, "binding": how, "quote": quote,
                    "asked": asked,
                    "blind": bool(blind) and how is None, "model": model if blind and how is None else None,
                    # a reader is a model with its instructions: which ones it had is kept with what it read
                    **({"instructions": INSTRUCTIONS} if blind and how is None and model else {}), "literal": literal,
                    "anchor": quote is not None and "List" not in fact["type"]})
        return {"m": m, "o": ob["id"], "read as": obj}

    def decline(self, h, place, why, cwd, blind=False, model=None):
        """Record that a reader, shown a place, found that it does not state the fact.

        This is what tells a place that is about something else from a reader that never
        answered: silence is not a decline. It holds for the place's content as it is now.
        """
        st = self.state()
        if h not in st.facts:
            raise KernelError(f"{h} is not a fact")
        decl = next((p for p in st.facts[h]["places"] if p["at"] == place), None)
        if decl is None:
            raise KernelError(f"{place} is not a place of this fact")
        if locate(place, cwd) is None:
            raise KernelError(f"{place} is not there")
        if not _norm(why):
            raise KernelError("say what the place is about instead")
        with self._tx() as (con, st):
            self._append(con, st, "decline", {"h": h, "place": place, "subject": subject_id(place, cwd), "why": _norm(why)[:400],
                                              "asked": question(st.facts[h], decl)[1],
                                              "blind": bool(blind), "model": model if blind else None})
        return {"declined": place}

    def _agreement(self, h, guards, terms):
        """The proposition that the present readings agree; stated once, then settled by Lean."""
        fact = self.state().facts[h]
        t = fact["type"]
        parts = [f"((({terms[0]}) : {t}) = (({x}) : {t}))" for x in terms[1:]]
        return self._settle(h, guards, " ∧ ".join(parts) or "True")

    def _instructions(self, h):
        """What people have laid down about a fact, and which of it can be used.

        Two instructions that Lean shows to differ cannot both be axioms: with both, anything
        would follow. Every instruction that differs from another one is set aside, the earlier
        as much as the later, the one many share as much as the lone one: which of them holds is
        for the people to settle. Where Lean can show neither that two are the same nor that
        they differ, both are set aside as well. What is left says one and the same value.
        """
        fact = self.state().facts[h]
        said, t = [dict(i) for i in fact.get("instructions", [])], fact["type"]
        for a in range(len(said)):
            for b in range(a + 1, len(said)):
                if said[a]["is"] == said[b]["is"]:
                    continue
                same, _ = self._settle(h, [], f"((({said[a]['is']}) : {t}) = (({said[b]['is']}) : {t}))")
                if same != "holds":
                    for i, other in ((a, b), (b, a)):
                        said[i].setdefault("set aside", []).append(said[other]["by"])
        return said

    def _contained(self, h, guards, part, whole):
        """The proposition that every entry a place lists is an entry of the whole list."""
        t = self.state().facts[h]["type"]
        return self._settle(h, guards, f"(∀ x ∈ (({part}) : {t}), x ∈ (({whole}) : {t}))")

    def _settle(self, h, guards, lean):
        fact = self.state().facts[h]
        f = "F:" + _sha(lean)
        new = (tuple(guards), f) not in fact["agreed"]
        if new:
            with self._tx() as (con, st):
                self._append(con, st, "agree", {"h": h, "f": f, "lean": lean, "guards": list(guards)})
        if f not in self.state().verdict:
            if not any(self.prove("holds", f, tac)["accepted"] for tac in ("rfl", "decide", "simp")):
                any(self.prove("not", f, tac)["accepted"] for tac in ("decide", "simp"))
        said = self.state().verdict.get(f, set())
        return ("contested" if len(said) > 1 else next(iter(said), None)), new

    def _recheck_fact(self, h, cwd, given=None):
        """`given`: for a definition, what its facts are settled as: [(name, type, term or None, why not)]."""
        st = self.state()
        fact = st.facts[h]
        entry = {"h": h, "fact": fact["name"], "text": fact["text"], "places": []}
        unread, reread = [], False
        asked_at = {p["at"]: question(fact, p) for p in fact["places"]}

        def view(m, at):
            """A reading as an answer to the question this place is asked now: None if it answered another one."""
            info = st.models[m]
            if info["binding"]:
                return info
            mine = info["asked"].get(asked_at[at][1])
            return None if mine is None else {**info, **mine}

        for decl in fact["places"]:
            at, now = decl["at"], subject_id(decl["at"], cwd)
            text, asked = asked_at[at]
            about = {"at": at, "question": text, **({"some": True} if decl.get("some") else {})}
            lost = unreadable(at, cwd)
            if lost:                                 # a declared place that is not where it was declared: said, not worked around
                unread.append({**about, "why": lost, "broken": True})
                continue
            rejected = {e["target"] for e in st.confirmations.values() if e["outcome"] == "rejected"}
            ever = [m for p, m in fact["readings"] if p == at and m not in rejected]
            seen = [m for m in ever if view(m, at)]
            have = [m for m in seen if st.models[m]["subject"] == now
                    or (st.models[m].get("anchor") and _anchored(st.models[m]["quote"], at, cwd))]
            said = {st.models[m]["obj"]: m for m in have if not st.models[m]["binding"]}
            if not decl["reader"] and len(said) > 1:      # two readers, two values: not for the kernel to choose
                unread.append({**about, "why": "its readers disagree: " + "; ".join(
                    f'{m} ({", ".join(sorted(st.models[m]["by"]))}) reads {st.objs[o]["text"][:60]}' for o, m in said.items())})
                continue
            if decl["reader"]:                       # computed afresh every time, never taken from the record
                try:
                    was = have
                    have = [self.read_place(h, at, cwd=cwd)["m"]]
                    reread = reread or (bool(seen) and have != was[-1:])
                except KernelError as e:             # the pattern no longer finds what it was declared to find
                    unread.append({**about, "why": str(e), "broken": True})
                    continue
            elif not have:
                no = [d for d in fact["declined"] if d["place"] == at and d["subject"] == now and d["asked"] == asked]
                unread.append({**about, "why": "it changed since it was read" if seen else
                               "the fact's description changed since it was read: what was read answered another question" if ever else
                               "nobody has read it yet",
                               **({"declined": no} if no else {})})
                continue
            st = self.state()
            entry["places"].append({**about, "reads as": st.objs[st.models[have[-1]]["obj"]]["text"], "m": have[-1],
                                    "by": "reader" if st.models[have[-1]]["binding"] else "stated"})
        whole = [p for p in entry["places"] if not p.get("some")]
        said = self._instructions(h)
        usable = [i for i in said if "set aside" not in i]
        if said:
            entry["instructions"] = said

        def outside(p, other):
            try:
                return sorted(set(json.loads(p["reads as"])) - set(json.loads(other)))
            except (ValueError, TypeError):
                return []

        target, waits = (usable[0]["is"] if usable else None), []
        if fact.get("defined"):
            # A definition says nothing new: its value is what its function gives for the facts it is
            # defined from. While one of those is not settled, there is nothing to hold the places against.
            entry["defined"] = fact["defined"]
            waits = [f"{name} {why}" for name, _, term, why in given or [] if term is None] or ([] if given else ["the facts it is defined from"])
            if not waits:
                target = f"(({fact['defined']['as']}) " + " ".join(f"(({term}) : {typ})" for _, typ, term, _ in given) + ")"
        if target is not None:
            entry["value"] = target                 # what this fact is settled as, for a definition that builds on it
        if unread:
            entry.update(state="disputed" if any("disagree" in u["why"] for u in unread) else "stale", unread=unread)
        elif waits:
            entry.update(state="waits", **{"waits for": waits})
        elif target is not None:
            # Someone has laid down what the value is, or a definition gives it. Each place is held
            # against that by itself, so that the places that differ can be named.
            t, who, new, verdicts = fact["type"], sorted({i["by"] for i in usable}), False, []
            for p in entry["places"]:
                if p.get("some"):
                    v, fresh = self._contained(h, [p["m"]], p["reads as"], target)
                    p["contained"] = v == "holds"
                    if v == "not":
                        p["not in the whole"] = outside(p, target)
                else:
                    v, fresh = self._settle(h, [p["m"]], f"((({p['reads as']}) : {t}) = (({target}) : {t}))")
                if v == "not" and usable:
                    p["against"] = who
                elif v == "not":
                    p["differs from the definition"] = True
                verdicts.append(v)
                new = new or fresh
            verdict = ("contested" if "contested" in verdicts else "not" if "not" in verdicts
                       else "holds" if all(v == "holds" for v in verdicts) else None)
            entry["state"] = {"holds": "re-established" if new and reread else "current", "not": "violated",
                              "contested": "contested"}.get(verdict, "uncovered")
            if fact.get("defined") and verdict != "holds" and self.gate is not None:
                entry["gives"] = self.gate.evaluate(t, target)       # (to show; that a place differs was settled by a proof)
        else:
            # the places that state the whole of it have to read the same; a place that states some
            # entries has to list nothing the whole does not have
            verdict, new = self._agreement(h, [p["m"] for p in whole], [p["reads as"] for p in whole])
            if verdict == "holds":
                for p in entry["places"]:
                    if p.get("some"):
                        inside, fresh = self._contained(h, [p["m"], whole[0]["m"]], p["reads as"], whole[0]["reads as"])
                        p["contained"], new = inside == "holds", new or fresh
                        if inside != "holds":
                            verdict = "contested" if "contested" in (inside, verdict) else "not" if "not" in (inside, verdict) else None
                        if inside == "not":
                            p["not in the whole"] = outside(p, whole[0]["reads as"])
            entry["state"] = {"holds": "re-established" if new and reread else "current", "not": "violated",
                              "contested": "contested"}.get(verdict, "uncovered")
            if verdict == "holds":
                entry["value"] = whole[0]["reads as"]
            else:
                for p in entry["places"]:               # nothing to hold a partial listing against yet
                    if p.get("some"):
                        p["whole undecided"] = True
        if len(usable) < len(said) and not unread:
            # Instructions that cannot both hold were set aside, and the places were judged without
            # them. That is as far as the kernel goes: the fact waits for a person, nothing else does.
            entry["without the instructions set aside"], entry["state"] = entry["state"], "conflict"
        # Whether each reading stands is decided by the project's rules, not by a number.
        st = self.state()
        fact = st.facts[h]                # with the readings this very check has just computed
        rules = load_rules(cwd)
        measured = measured_readers(cwd, rules)
        confirmed = {(e["target"], e.get("asked")) for e in st.confirmations.values() if e["outcome"] == "confirmed"}

        def value(obj):
            text = st.objs[obj]["text"]
            try:
                return json.loads(text)
            except ValueError:
                return text

        for p in entry["places"]:
            info, asked = view(p["m"], p["at"]), asked_at[p["at"]][1]
            # agreeing with another place means something between places that state the whole of it
            others = [view(q["m"], q["at"]) for q in whole if q is not p and not p.get("some") and st.models[q["m"]]["obj"] == info["obj"]]
            readers = _counted(info, measured)
            # a computed place: was the pattern ever checked against a reader who saw only the place?
            mine = [v for at, m in fact["readings"] if at == p["at"] for v in [view(m, at)] if v]
            stated = [s for s in mine if not s["binding"] and _counted(s, measured)]
            same_blind = bool(info["binding"]) and any(
                s["subject"] == c["subject"] and value(s["obj"]) == value(c["obj"])
                for s in stated for c in mine if c["binding"] == info["binding"])
            has = {
                "computed": bool(info["binding"]),
                "confirmed by a person": bool({(p["m"], None), (p["m"], asked)} & confirmed),
                "blind": bool(readers),
                "words occur in the place": info["literal"],
                "agrees with a computed place": any(o["binding"] for o in others),
                "agrees with another place read blind": any(not o["binding"] and _counted(o, measured) and o["blind"] - info["blind"] for o in others),
                "read the same by a second model": len(readers) > 1,
                "read the same blind": same_blind,
                "contained in a computed place": bool(p.get("contained")) and any(st.models[q["m"]]["binding"] for q in whole),
            }
            met = next((rule for rule in rules["a reading stands if any of"] if all(has[c] for c in rule)), None)
            p["stands"] = met is not None
            p["why"] = " + ".join(met) if met else "no rule is met"
            if not info["binding"]:
                skip = ("agrees with a computed place", "agrees with another place read blind") if p.get("some") else ("contained in a computed place",)
                p["has"] = {c: v for c, v in has.items() if c not in ("computed", "read the same blind", *skip)}
                p["unmeasured readers"] = sorted(info["models"] - readers) + (
                    ["a reader whose model was not recorded"] if info["blind"] and not info["models"] else [])
            else:
                now = subject_id(p["at"], cwd)
                p["has"] = {"read the same blind": same_blind}
                p["unmeasured readers"] = sorted({r for s in mine if not s["binding"] for r in s["models"] - _counted(s, measured)})
                p["read blind as"] = sorted({st.objs[s["obj"]]["text"] for s in stated if s["subject"] == now} - {p["reads as"]})
                p["declined"] = [d for d in fact["declined"] if d["place"] == p["at"] and d["subject"] == now and d["asked"] == asked]
        return entry

    def sync_facts(self, path):
        """Make the standing facts those declared in a file; facts no longer declared are withdrawn.

        The file is a JSON list of {"name", "type", "places", "gloss"?, "instructions"?}. A place is
        "path" or "path::part" (someone has to read it), or {"at": ..., "read": {...}} where
        "read" describes how to read it mechanically: see `pattern`. A place of a list that
        states only some of its entries (an example, an excerpt) carries "some": true; what it
        lists has to be among the entries, it need not be all of them.
        "instructions" is what people have laid down about the fact: [{"is": value, "by": who,
        "said"?: their words, "on"?: when}], the value written as JSON.
        "defined" makes the fact a definition: {"from": [names of facts], "as": a Lean function
        of their values}, e.g. {"from": ["modes"], "as": "fun ms => ms.length"}.
        """
        with open(path, encoding="utf-8") as fh:
            declared = json.load(fh)
        types = {d["name"]: _norm(d["type"]) for d in declared}
        for d in declared:                         # a definition has to make sense before anything is recorded
            how = d.get("defined")
            if how is None:
                continue
            if not isinstance(how, dict) or not isinstance(how.get("from"), list) or not isinstance(how.get("as"), str):
                raise KernelError(f'{d["name"]}: a definition is {{"from": [names of facts], "as": a Lean function of their values}}')
            missing = [x for x in how["from"] if x not in types]
            if missing:
                raise KernelError(f"{d['name']} is defined from {missing[0]!r}, which is not declared")
            seen, todo = set(), list(how["from"])
            while todo:                            # nothing may be defined, however indirectly, from itself
                x = todo.pop()
                if x == d["name"]:
                    raise KernelError(f"{d['name']} is defined in a circle")
                if x not in seen:
                    seen.add(x)
                    todo += next(e for e in declared if e["name"] == x).get("defined", {}).get("from", [])
            self._screen(how["as"])
            self._well_typed((" → ".join(f"({types[x]})" for x in how["from"]) + f" → ({types[d['name']]})", how["as"]))
        keep = set()
        for d in declared:
            places = []
            for p in d["places"]:
                if isinstance(p, str):
                    places.append(p)
                elif set(p) == {"at", "some"} and p["some"] is True:
                    places.append({"at": p["at"], "some": True})
                elif "read" in p and set(p) in ({"at", "read"}, {"at", "read", "some"}) and p.get("some", True) is True:
                    try:
                        places.append({"at": p["at"], "some": p.get("some", False), "reader": reader(p["read"], p["at"])})
                    except KernelError as e:
                        raise KernelError(f"{d['name']}: {e}")
                else:
                    raise KernelError(f"{d['name']}: a place is a string, or {{\"at\": ..., \"read\": {{...}}}}, "
                                      "either with \"some\": true if it states only some entries of a list")
            if "value" in d:
                raise KernelError(f'{d["name"]}: "value" is no longer read; say whose instruction it is: "instructions": [{{"is": ..., "by": ...}}]')
            said = d.get("instructions", [])
            if not isinstance(said, list) or not all(isinstance(i, dict) for i in said):
                raise KernelError(f'{d["name"]}: "instructions" is a list of {{"is": value, "by": who}}')
            # an instruction's value is written as JSON ("pqd", 14, ["a", "b"]) and becomes the Lean term the places are read as
            said = [{**i, "is": json.dumps(i["is"], ensure_ascii=False) if _json_like(_norm(d["type"])) else i["is"]} if "is" in i else i
                    for i in said]
            keep.add(self.claim_fact(d["name"], d["type"], places, d.get("gloss", ""), said, d.get("defined"))["h"])
        st = self.state()
        for h in st.facts:
            if h not in keep and h not in st.withdrawn:
                self.withdraw(h, f"no longer declared in {os.path.basename(path)}")
        return keep

    def adopt(self, events):
        """Take over readings that were made against a copy of this record, of text that has
        since been written into the files. A reading names the content it is of, so it holds
        here exactly if the file now has that content; otherwise it is simply never used."""
        with self._tx() as (con, st):
            for e in events:
                if e.get("type") != "reading" or e.get("h") not in st.facts or e["place"] not in [p["at"] for p in st.facts[e["h"]]["places"]]:
                    raise KernelError("only readings of declared places can be taken over")
                e = {k: v for k, v in e.items() if k != "id"}
                con.write(json.dumps(e, ensure_ascii=False) + "\n")
                st.apply("reading", e)

    def sign_off(self, m, who, confirmed=True):
        """A person has compared a reading with the place itself, and confirms or rejects it.

        The person answered the fact's question as it was then: the confirmation does not carry
        over to another description. The same person cannot say both of the same reading."""
        outcome = "confirmed" if confirmed else "rejected"
        with self._tx() as (con, st):
            asked = next((question(f, p)[1] for f in st.facts.values() for at, x in f["readings"] if x == m
                          for p in f["places"] if p["at"] == at), None)
            if asked is None:
                raise KernelError(f"{m} is not a reading of a declared place")
            eid = "E:" + _sha(m, "sign_off", f"person:{who}/{asked}")
            old = st.confirmations.get(eid)
            if old is not None:
                if old["outcome"] != outcome:
                    raise KernelError(f"{who} already recorded this reading as {old['outcome']}")
                return {"eid": eid, "duplicate": True}
            self._append(con, st, "observe", {"eid": eid, "target": m, "kind": "sign_off", "outcome": outcome,
                                              "source": f"person:{who}/{asked}", "asked": asked})
        return {"eid": eid, "duplicate": False}

    def _screen(self, text):
        if self.gate is not None:
            self.gate.screen(text)

    def _well_typed(self, *items):
        """Refuse a value Lean does not accept as a term of the fact's type, at the moment it is stated."""
        if self.gate is not None:
            v = self.gate.typecheck(list(items))
            if not v["ok"]:
                raise KernelError("Lean does not accept this under Gamma: " + v["reason"])

    def prove(self, relation, f, proof):
        """Ask the Lean gate whether proposition `f` holds, or does not (`relation`: holds | not).

        Nothing is recorded unless the gate accepts. A failed attempt is not evidence.
        """
        if relation not in ("holds", "not"):
            raise KernelError("a proposition is shown to hold, or not to hold")
        if self.gate is None:
            raise KernelError("no Lean gate configured; proofs cannot be accepted")
        st = self.state()
        if f not in st.props:
            raise KernelError(f"unknown proposition {f}")
        verdict = self.gate.check(relation, [("Prop", st.props[f])], proof)
        if not verdict["ok"]:
            return {"accepted": False, "reason": verdict["reason"]}
        with self._tx() as (con, st):
            self._append(con, st, "proof", {
                "relation": relation, "args": [f], "proof_sha": _sha(proof), "proof": proof,
                "axioms": verdict["axioms"], "gamma": verdict["gamma"],
            })
        return {"accepted": True, "axioms": verdict["axioms"], "gamma": verdict["gamma"]}

    def withdraw(self, h, justification):
        """The fact is no longer declared."""
        if not justification.strip():
            raise KernelError("withdrawing a fact needs a justification")
        with self._tx() as (con, st):
            if h not in st.facts:
                raise KernelError(f"unknown fact {h}")
            self._append(con, st, "withdraw", {"h": h, "justification": justification})
        return {"h": h}

    def recheck(self, cwd):
        """Hold every declared fact against the files as they are in `cwd`, without anyone's judgement.

        Places read by a pattern are computed afresh. A place read by an agent or a person keeps
        its reading while its content (for a single value: the quoted sentence) is unchanged and
        the fact's description is the one the reader was asked. Lean settles whether the values
        agree; the project's rules say whether each reading stands (see `_recheck_fact`).

          current         every place is read and they agree
          re-established  a computed place changed and they still agree
          violated        Lean has verified that the places do not state the same value, or that a
                          place stating some entries of a list has one the whole list does not
          stale           a place has to be read (again) before anything can be said, or can no
                          longer be read as declared (its file or part is gone, its pattern does
                          not find what it should): the declaration has to be repaired
          disputed        readers of one place disagree about what it says
          uncovered       the places are read, and Lean could settle neither that they agree nor that they differ
          contested       the record holds proofs both that they agree and that they differ: one of
                          them is not Lean's, and `verify` finds which
          conflict        people's instructions about the fact cannot both hold; they are set
                          aside, and the fact waits for a person to withdraw one
          waits           a definition whose facts are not settled: nothing to hold its places against

        Where a person has laid down what the value is (and no other instruction differs), the
        places are not compared with one another but each with that: a place that differs is
        reported as against the instruction, by name.
        """
        st = self.state()
        live = [h for h in st.facts if h not in st.withdrawn]
        by_name = {st.facts[h]["name"]: h for h in live}
        done = {}

        def entry(h, above=()):
            """A fact is held after the facts it is defined from, and with what they are settled as."""
            if h in done:
                return done[h]
            given = None
            if st.facts[h].get("defined"):
                given = []
                for name in st.facts[h]["defined"]["from"]:
                    src = by_name.get(name)
                    if src is None or src == h or src in above:
                        given.append((name, None, None, "is not declared" if src is None else "is defined in a circle"))
                        continue
                    e = entry(src, above + (h,))
                    given.append((name, st.facts[src]["type"], e.get("value"),
                                  None if "value" in e else f"is {e['state']}"))
            done[h] = self._recheck_fact(h, cwd, given)
            return done[h]

        return {"decisions": [entry(h) for h in live]}
