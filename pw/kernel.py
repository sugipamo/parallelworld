"""Knowledge kernel: append-only event log, and the model that ties the layers together.

  lindenbaum.py   formal layer: what Lean has verified, as a presented Boolean algebra
  credal.py       probabilistic layer: credal sets, generalized Bayes rule
  this file       the events, and the reliability model connecting claims to propositions

Events are of three kinds: model extension (claim / ground / independence),
evidence (observe), and verified proof. A proof shrinks the space of worlds; evidence
reweights measures on it. Nothing else changes the state.
"""
import ast
import hashlib
import itertools
import json
import os
import random
import re
import fcntl
import subprocess
import time
from contextlib import contextmanager
from fractions import Fraction

import numpy as np

from . import formula as fm
from .credal import COPULAS, CredalSet, exchangeable_agreement, joint_likelihood, stone_space
from .lindenbaum import RELATIONS, Lindenbaum

CATALOG_PATH = os.path.join(os.path.dirname(__file__), "catalog.json")


def _unit(rng, bound):
    d = rng.choice((1, 2, 3, 4, 5, 8, 10))
    return Fraction(rng.randint(0, d), d)


# A model hypothesis says more than "this term models that code". Written out, it is
#
#     M(s, a, D, call):   for every x in D,   show(call(x)) = a(x)
#
#   s     the code, by path::name and the hash of its file
#   a     the Lean term
#   D     the domain of each argument, by name (below), and the bound random draws stay within
#   call  how the code is invoked: Python statements to run first, and an expression in {0}, {1}, ...
#
# A value of a domain has two spellings, one for each side (`_lean`, `_python`); the code's result
# is written out by the kernel, not by the code (`_SHOW`); the two outputs are compared as values
# (`_values`). All of this is recorded with M and is part of what M claims.
DOMAINS = {
    "nat":   (lambda rng, b: rng.randint(0, b),
              lambda v: isinstance(v, int) and v >= 0, "natural number"),
    "int":   (lambda rng, b: rng.randint(-b, b),
              lambda v: isinstance(v, int), "integer"),
    "unit":  (_unit,
              lambda v: isinstance(v, (int, Fraction)) and 0 <= v <= 1, "rational in [0, 1]"),
    "pos":   (lambda rng, b: Fraction(rng.randint(1, 4 * b), 4),
              lambda v: isinstance(v, (int, Fraction)) and v > 0, "positive rational"),
    "units": (lambda rng, b: tuple(_unit(rng, b) for _ in range(rng.randint(1, 4))),
              lambda v: isinstance(v, tuple) and len(v) > 0 and all(isinstance(x, (int, Fraction)) and 0 <= x <= 1 for x in v),
              "non-empty list of rationals in [0, 1]"),
}
_RATIONAL = ("unit", "pos", "units")

_SHOW = """
import fractions as _f, numbers as _n
from fractions import Fraction
def _show(v):
    if isinstance(v, bool): return "true" if v else "false"
    if isinstance(v, _n.Integral): return str(int(v))
    if isinstance(v, _f.Fraction): return str(v)
    if isinstance(v, float):
        if v != v or v in (float("inf"), float("-inf")): raise TypeError("no exact value for " + repr(v))
        return str(_f.Fraction(v))
    if hasattr(v, "tolist"): v = v.tolist()
    if isinstance(v, tuple): return "(" + ", ".join(_show(x) for x in v) + ")"
    if isinstance(v, list): return "[" + ", ".join(_show(x) for x in v) + "]"
    raise TypeError("no exact rendering for " + type(v).__name__)
"""


def _value(raw, domain):
    """Read an argument given from outside (an int, "3/4", or a list of these) as a value of `domain`."""
    def one(x):
        if isinstance(x, bool) or not isinstance(x, (int, str, Fraction)):
            raise KernelError(f"{x!r} is not a number")
        try:
            return x if isinstance(x, (int, Fraction)) else (int(x) if x.lstrip("-").isdigit() else Fraction(x))
        except (ValueError, ZeroDivisionError):
            raise KernelError(f"{x!r} is not a number")
    v = tuple(one(x) for x in raw) if isinstance(raw, (list, tuple)) else one(raw)
    if not DOMAINS[domain][1](v):
        raise KernelError(f"{raw!r} is not a {DOMAINS[domain][2]}")
    return v


def _lean(v, domain):
    if isinstance(v, tuple):
        return "([" + ", ".join(_lean(x, "unit") for x in v) + "] : List ℚ)"
    if domain in _RATIONAL:
        v = Fraction(v)
        return f"({v.numerator}/{v.denominator} : ℚ)"
    return str(v) if v >= 0 else f"({v})"


def _python(v, domain):
    if isinstance(v, tuple):
        return "[" + ", ".join(_python(x, "unit") for x in v) + "]"
    if domain in _RATIONAL:
        v = Fraction(v)
        return f"Fraction({v.numerator}, {v.denominator})"
    return str(v)


def _values(text):
    """What an output says, apart from how it is written: numbers as exact rationals
    (3/4, 0.75 and Fraction(3, 4) are the same value; 0.0 is 0), list brackets, and words.
    Round brackets are dropped, because the two sides nest tuples differently."""
    text = re.sub(r"fraction\((-?\d+),\s*(\d+)\)", r"\1/\2", text.lower())
    out = []
    for tok in re.findall(r"-?\d+(?:\.\d+(?:e-?\d+)?|/\d+)?|[a-z_!]+|[\[\]]", text):
        try:
            out.append(Fraction(tok))
        except (ValueError, ZeroDivisionError):
            out.append(tok)
    return out


def binding(call, setup="", domains=(), bound=15):
    """The recorded way a piece of code is invoked and its arguments drawn (see above)."""
    domains = list(domains)
    if not call.strip() or not domains:
        raise KernelError("a binding needs a call expression and a domain for each argument")
    if any(d not in DOMAINS for d in domains):
        raise KernelError(f"domains must be among {sorted(DOMAINS)}")
    if any("{%d}" % i not in call for i in range(len(domains))):
        raise KernelError("the call must use every argument: {0}, {1}, ...")
    return {"language": "python", "setup": setup.strip(), "call": call.strip(), "domains": domains, "bound": int(bound)}


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


def pattern(find=None, find_all=None, kind="string", sort=False, unique=False):
    """A declarative way to read a place: what to look for, and what kind of value it is.

      find      a regular expression with one group; it must match exactly once, and the
                group is the value
      find_all  the same, but every match counts and the result is a list
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
    if re.search(r"\(\?[=!<P]|\\[1-9]", rx):
        raise KernelError("look-around, back-references and named groups are not accepted in a pattern")
    try:
        if re.compile(rx).groups != 1:
            raise KernelError("the pattern needs exactly one group: the part in ( ) is the value")
    except re.error as e:
        raise KernelError(f"not a regular expression: {e}")
    out = {"language": "pattern", "as": kind}
    out["find" if find is not None else "find_all"] = rx
    if find_all is not None:
        out.update(sort=bool(sort), unique=bool(unique))
    return out


def _read_pattern(rd, text):
    found = re.findall(rd.get("find") or rd["find_all"], text, re.M)
    if "find" in rd:
        if len(found) != 1:
            raise KernelError(f"the pattern matches {len(found)} times here; it has to match exactly once")
        return _term(rd["as"], found[0])[1]
    values = [_term(rd["as"], x) for x in found]
    if rd.get("unique"):
        values = list({v[1]: v for v in values}.values())
    if rd.get("sort"):
        values.sort(key=lambda v: v[0])
    return "[" + ", ".join(v[1] for v in values) + "]"


def reader(expr, fmt="json"):
    """A recorded, mechanical way to read a file as a Lean term, as a Python expression.

    For callers of this module only. It ties the record to this implementation and runs code,
    so a project's list of facts cannot use it: there, places are read with `pattern`.

    `expr` is a Python expression that evaluates to the Lean term as a string. It can use
    `data` (the whole file: parsed JSON, or the text), `part` (the text of the part the subject
    names), `re`, `permille(x)` (a number as a whole number of thousandths; fails if it is not
    one) and `lean_string(s)` (a string literal).
    With a reader nobody has to be believed about what the file says: the term is recomputed
    whenever the file changes.
    """
    if fmt not in ("json", "text") or not expr.strip():
        raise KernelError("a reader needs an expression and a format: json or text")
    return {"language": "reader", "format": fmt, "expr": expr.strip()}


_READ = """
import json, re, sys
from fractions import Fraction
part = sys.stdin.read()
def permille(x):
    v = Fraction(str(x)) * 1000
    if v.denominator != 1: raise ValueError(f"{x} is not a whole number of thousandths")
    return int(v)
def lean_string(s): return json.dumps(s, ensure_ascii=False)
with open(sys.argv[1], encoding="utf-8") as fh:
    data = json.load(fh) if sys.argv[2] == "json" else fh.read()
print(eval(sys.argv[3]))
"""


class KernelError(Exception):
    pass


class Conflict(KernelError):
    """Priors / evidence are jointly impossible given the verified proofs."""


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


def measured_readers(cwd, rules):
    """The reader models whose latest measurement in this repository meets the rules' bar."""
    path = os.path.join(cwd, CALIBRATION)
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8") as fh:
        latest = {run["model"]: run for run in json.load(fh)}
    bar = rules["a blind reader counts if measured"]
    limits = {"read at least": ("read rate", 0, 1), "stuck at most": ("stuck rate", 1, -1),
              "takes another thing for it at most": ("accept rate", 1, -1)}
    unknown = set(bar) - set(limits)
    if unknown:
        raise KernelError(f"a reader can be asked for {sorted(limits)}; not {sorted(unknown)}")
    # a rate that was not measured does not meet a bar on it
    return {m for m, run in latest.items()
            if all(key in run and sign * run[key][end] >= sign * bar[name] for name, (key, end, sign) in limits.items() if name in bar)}


def _tree(cwd):
    """Identifies the content of the working tree a check ran against: every tracked file's
    content plus whatever is modified or new. The record itself is left out, so that writing to
    it, or committing it, does not make earlier check runs look like runs on another tree."""
    def git(*args):
        r = subprocess.run(["git", *args, "--", ".", f":(exclude){LOG}"], cwd=cwd, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else f"nogit:{time.time()}"
    return "tree:" + _sha(git("ls-files", "-s"), git("status", "--porcelain"), git("diff", "HEAD"))


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


class State:
    def __init__(self):
        self.atoms = {}      # world atoms: id -> {"kind": H|F|G, "text": str}
        self.prior = {}      # base rates
        self.links = []      # (guards, h, f): if every guard holds, claim h is true iff proposition f is
        self.models = {}     # M id -> {"subject", "obj"}
        self.retracted = {}  # eid -> justification
        self.formal = {}     # H id -> {"subject", "pred"} for claims stated as a predicate
        self.authors = {}    # G id -> actors who stated that connection
        self.withdrawn = {}  # H id -> why the decision no longer stands
        self.facts = {}      # H id -> {"name", "type", "places": [{"at", "reader"}], "value", "readings": [(place, M)]}
        self.notes = {}      # G id -> what its author says the formalization leaves out and adds
        self.evidence = {}   # eid -> dict
        self.proofs = []     # proof events as recorded
        self.algebra = Lindenbaum()

    def rep(self, a):
        return self.algebra.find(a)

    def apply(self, typ, p):
        if typ == "claim":
            self.atoms[p["h"]] = {"kind": "H", "text": p["text"]}
            self.prior[p["h"]] = p["prior"]
            if p.get("fact"):                    # declared, or declared again with other places or readers
                was = self.facts.get(p["h"], {})
                self.facts[p["h"]] = dict(p["fact"], readings=was.get("readings", []), declined=was.get("declined", []))
            if p.get("pred"):
                self.formal[p["h"]] = {"subject": p["subject"], "pred": p["pred"]["id"]}
                self.algebra.add_pred(p["pred"]["id"], p["pred"]["type"], p["pred"]["text"])
        elif typ == "object":
            self.algebra.add_obj(p["id"], p["lean_type"], p["text"])
        elif typ == "reading":
            self.algebra.add_obj(p["obj"]["id"], p["obj"]["type"], p["obj"]["text"])
            if p["m"] not in self.atoms:
                self.atoms[p["m"]] = {"kind": "M", "text": f'{p["subject"]} reads as {p["obj"]["id"]}'}
                self.prior[p["m"]] = p["model_prior"]
                self.models[p["m"]] = {"subject": p["subject"], "obj": p["obj"]["id"], "binding": p.get("binding"),
                                       "quote": p.get("quote"), "anchor": p.get("anchor", False),
                                       "by": set(), "blind": set(), "models": set(), "literal": False}
            info = self.models[p["m"]]
            info["by"].add(p.get("actor", "anon"))                 # who read it this way
            if p.get("blind"):
                info["blind"].add(p.get("actor", "anon"))          # ...shown nothing but the place
                if p.get("model"):
                    info["models"].add(p["model"])                 # ...and which model that reader was
            info["literal"] = info["literal"] or bool(p.get("literal"))
            if (p["place"], p["m"]) not in self.facts[p["h"]]["readings"]:
                self.facts[p["h"]]["readings"].append((p["place"], p["m"]))
        elif typ == "decline":
            self.facts[p["h"]]["declined"].append({k: p.get(k) for k in ("place", "subject", "actor", "model", "blind", "why")})
        elif typ == "agree":
            if p["f"] not in self.atoms:
                self.atoms[p["f"]] = {"kind": "F", "text": p["lean"]}
                self.prior[p["f"]] = self.prior[p["h"]]
            self.algebra.add_prop(p["f"], p["lean"])
            self.links.append((tuple(p["guards"]), p["h"], p["f"]))
        elif typ == "withdraw":
            self.withdrawn[p["h"]] = p["justification"]
        elif typ == "concur":
            self.authors.setdefault(p["g"], set()).add(p["by"])
        elif typ == "ground":
            pred, obj = p.get("pred"), p.get("obj")
            if pred:
                self.algebra.add_pred(pred["id"], pred["type"], pred["text"])
                self.algebra.add_obj(obj["id"], obj["type"], obj["text"])
            if p["f"] not in self.atoms:
                self.atoms[p["f"]] = {"kind": "F", "text": p["lean"]}
                self.prior[p["f"]] = self.prior[p["h"]]
            self.algebra.add_prop(p["f"], p["lean"], pred and pred["id"], obj and obj["id"])
            guards = ()
            if p.get("g"):
                self.atoms[p["g"]] = {"kind": "G", "text": f'{p["h"]} means {p["f"]}'}
                self.prior[p["g"]] = p["prior"]
                self.authors.setdefault(p["g"], set()).add(p.get("by", "anon"))
                if p.get("left_out") or p.get("added"):
                    self.notes[p["g"]] = {"left_out": p.get("left_out", ""), "added": p.get("added", "")}
                guards = (p["g"],)
            if p.get("m"):
                if p["m"] not in self.atoms:
                    self.atoms[p["m"]] = {"kind": "M", "text": f'{obj["id"]} models {p["subject"]}'}
                    self.prior[p["m"]] = p["model_prior"]
                    self.models[p["m"]] = {"subject": p["subject"], "obj": obj["id"], "binding": p.get("binding")}
                guards += (p["m"],)
            self.links.append((guards, p["h"], p["f"]))
        elif typ == "observe":
            self.evidence[p["eid"]] = dict(p, block="shared")
        elif typ == "retract":
            self.evidence.pop(p["eid"], None)
            self.retracted[p["eid"]] = p["justification"]
        elif typ == "independence":
            self.evidence[p["eid"]]["block"] = p["eid"]
        elif typ == "proof":
            self.proofs.append(p)
            self.algebra.relate(p["relation"], p["args"])


class Kernel:
    def __init__(self, db_path, gate=None, catalog=None, actor=None, max_atoms=14, dependence="pqd"):
        if dependence not in COPULAS:
            raise KernelError(f"dependence must be one of {sorted(COPULAS)}")
        self.dependence = dependence   # copula class for evidence on one target not declared independent
        self.db_path = db_path
        self.gate = gate
        self.actor = actor or os.environ.get("PW_AGENT", "anon")
        self.max_atoms = max_atoms     # the largest connected component, in atoms, that infer still solves
        if catalog is None:
            with open(CATALOG_PATH) as fh:
                catalog = json.load(fh)
        self.catalog = catalog
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

    def verify(self):
        """Run every recorded proof through the gate again; return those it does not accept.

        The log is a text file anyone can edit. Whatever in it can be checked again is not
        taken on trust: readers are re-run on every check, and proofs are re-run here.
        What cannot be re-run, a person's confirmation above all, is only as good as the
        review of the commit that added the line.
        """
        if self.gate is None:
            raise KernelError("no Lean gate configured; proofs cannot be verified")
        st = self.state()
        refused = []
        for p in st.proofs:
            verdict = self.gate.check(p["relation"], self._items(p["relation"], p["args"], st.algebra), p.get("proof", ""))
            if not verdict["ok"]:
                refused.append({"relation": p["relation"], "args": p["args"], "reason": verdict["reason"][-300:]})
        return refused

    # ---- operations ------------------------------------------------------
    def claim(self, text, prior=None):
        """Register knowledge proposition H. Identical text => identical H."""
        text = _norm(text)
        h = "H:" + _sha(text)
        with self._tx() as (con, st):
            if h not in st.atoms:
                prior = self.catalog["priors"]["claim"] if prior is None else prior
                self._append(con, st, "claim", {"h": h, "text": text, "prior": prior})
        return {"h": h}

    def claim_formal(self, subject, typ, predicate, gloss="", prior=None):
        """Register a claim that is *defined* as: the code `subject` satisfies `predicate : typ -> Prop`.

        Nothing is translated, so there is no specification hypothesis to doubt. What the
        predicate means is settled by Gamma, where its definitions were reviewed. The only
        uncertain link left is whether a Lean object models the code (attach_model).
        """
        typ, predicate = _norm(typ), _norm(predicate)
        self._screen(typ)
        self._screen(predicate)
        self._well_typed((f"({typ}) → Prop", predicate))
        pred = {"id": "P:" + _sha(typ, predicate), "type": typ, "text": predicate}
        h = "H:" + _sha("formal", subject, pred["id"])
        with self._tx() as (con, st):
            if h not in st.atoms:
                self._append(con, st, "claim", {
                    "h": h, "text": _norm(gloss) or f"{subject} satisfies {predicate}",
                    "prior": self.catalog["priors"]["claim"] if prior is None else prior,
                    "subject": subject, "pred": pred,
                })
        return {"h": h, "p": pred["id"]}

    def attach_model(self, h, obj, subject_version=None, model_prior=None, binding=None, cwd=None):
        """For a formal claim: state that Lean object `obj` models the claim's code.
        Introduces only the model hypothesis M; if M holds, the claim is true iff predicate(obj) is.

        `binding` (see `binding()`) says how the code is called and where its arguments come
        from. It is part of what M claims; without it M cannot be checked against the code.
        """
        st = self.state()
        if h not in st.formal:
            raise KernelError(f"{h} is not a formal claim; use ground_at")
        pred = dict(st.algebra.preds[st.formal[h]["pred"]], id=st.formal[h]["pred"])
        obj = _norm(obj)
        self._screen(obj)
        self._well_typed((pred["type"], obj))
        subject = subject_version or st.formal[h]["subject"]
        ob = {"id": "O:" + _sha(pred["type"], obj), "type": pred["type"], "text": obj}
        lean = f"((({pred['text']}) : ({pred['type']}) → Prop) (({obj}) : ({pred['type']})))"
        f, m = "F:" + _sha(lean), self._model_id(subject, ob, binding, cwd)
        with self._tx() as (con, st):
            if not any(l == ((m,), h, f) for l in st.links):
                self._append(con, st, "ground", {
                    "h": h, "f": f, "lean": lean, "pred": pred, "obj": ob, "subject": subject, "m": m,
                    "binding": binding,
                    "model_prior": self.catalog["priors"]["model"] if model_prior is None else model_prior,
                })
        return {"m": m, "f": f, "p": pred["id"], "o": ob["id"]}

    def read(self, subject, rd, cwd):
        """The Lean term a reader gives for the file as it is now."""
        subject = subject.split("@")[0]
        content = locate(subject, cwd)
        if content is None:
            raise KernelError(f"{subject} is not there")
        if rd["language"] == "pattern":
            return _read_pattern(rd, content.decode("utf-8", "replace"))
        r = subprocess.run(["python3", "-c", _READ, os.path.join(cwd, subject.split("::")[0]), rd["format"], rd["expr"]],
                           input=content.decode("utf-8", "replace"), capture_output=True, text=True, timeout=120)
        if r.returncode != 0:
            raise KernelError("the reader failed on this file: " + (r.stdout + r.stderr)[-400:])
        return _norm(r.stdout)

    def attach_derived(self, h, rd, cwd):
        """For a formal claim about a file: compute the Lean term with a reader instead of
        having someone state it. The model hypothesis is then only that the reader is right."""
        st = self.state()
        if h not in st.formal:
            raise KernelError(f"{h} is not a formal claim")
        subject = st.formal[h]["subject"]
        return self.attach_model(h, self.read(subject, rd, cwd), subject_version=subject_id(subject, cwd),
                                 binding=rd, model_prior=self.catalog["priors"]["derived"])

    # ---- facts: one thing, said in several places -----------------------------
    def claim_fact(self, name, typ, places, value=None, gloss=""):
        """Declare that the listed places all state the same fact, a value of Lean type `typ`.

        Each place is `path` or `path::part`, optionally with a reader that computes the value
        from the content; a place without one has to be read by an agent or a person. The
        decision is that all places read as the same value (and as `value`, if one is given).
        No place is privileged: when they differ, which one is right is for a person to say.
        """
        typ = _norm(typ)
        self._screen(typ)
        places = [{"at": p, "reader": None} if isinstance(p, str) else {"at": p["at"], "reader": p.get("reader")} for p in places]
        if not places:
            raise KernelError("a fact needs at least one place")
        if value is not None:
            value = _norm(value)
            self._screen(value)
            self._well_typed((typ, value))
        fact = {"name": name, "type": typ, "places": places, "value": value}
        h = "H:" + _sha("fact", name, typ)       # the same fact, however its places come to be listed or read
        with self._tx() as (con, st):
            declared = {k: v for k, v in st.facts.get(h, {}).items() if k != "readings"}
            if declared != fact:
                self._append(con, st, "claim", {
                    "h": h, "text": _norm(gloss) or f"the same {name} is stated in {len(places)} place(s)",
                    "prior": self.catalog["priors"]["claim"], "fact": fact})
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
            obj = self.read(place, how, cwd)
        if quote is not None and not _anchored(quote, place, cwd):
            raise KernelError("the quote is not in the place word for word")
        obj = _norm(obj)
        self._screen(obj)
        self._well_typed((fact["type"], obj))
        version = subject_id(place, cwd)
        ob = {"id": "O:" + _sha(fact["type"], obj), "type": fact["type"], "text": obj}
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
        with self._tx() as (con, st):
            known = st.models.get(m, {})
            # who read it matters only for a reading someone stated; a computed one is the same whoever runs it
            if ((place, m) not in st.facts[h]["readings"]
                    or (how is None and (self.actor not in known.get("by", ()) or (blind and self.actor not in known.get("blind", ()))
                                         or (blind and model and model not in known.get("models", ()))))):
                self._append(con, st, "reading", {
                    "h": h, "place": place, "subject": version, "m": m, "obj": ob, "binding": how, "quote": quote,
                    "blind": bool(blind) and how is None, "model": model if blind and how is None else None, "literal": literal,
                    "anchor": quote is not None and "List" not in fact["type"],
                    "model_prior": self.catalog["priors"]["derived" if how else "model"]})
        return {"m": m, "o": ob["id"], "read as": obj}

    def decline(self, h, place, why, cwd, blind=False, model=None):
        """Record that a reader, shown a place, found that it does not state the fact.

        This is what tells a place that is about something else from a reader that never
        answered: silence is not a decline. It holds for the place's content as it is now.
        """
        st = self.state()
        if h not in st.facts:
            raise KernelError(f"{h} is not a fact")
        if place not in [p["at"] for p in st.facts[h]["places"]]:
            raise KernelError(f"{place} is not a place of this fact")
        if locate(place, cwd) is None:
            raise KernelError(f"{place} is not there")
        if not _norm(why):
            raise KernelError("say what the place is about instead")
        with self._tx() as (con, st):
            self._append(con, st, "decline", {"h": h, "place": place, "subject": subject_id(place, cwd), "why": _norm(why)[:400],
                                              "blind": bool(blind), "model": model if blind else None})
        return {"declined": place}

    def _agreement(self, h, guards, terms):
        """The proposition that the present readings agree; stated once, then settled by Lean."""
        st = self.state()
        fact = st.facts[h]
        t = fact["type"]
        parts = [f"((({terms[0]}) : {t}) = (({x}) : {t}))" for x in terms[1:]]
        if fact["value"] is not None:
            parts.append(f"((({terms[0]}) : {t}) = (({fact['value']}) : {t}))")
        lean = " ∧ ".join(parts) or "True"
        f = "F:" + _sha(lean)
        new = (tuple(guards), h, f) not in st.links
        if new:
            with self._tx() as (con, st):
                self._append(con, st, "agree", {"h": h, "f": f, "lean": lean, "guards": list(guards)})
        st = self.state()
        if st.rep(f) not in st.algebra.decided():
            if not any(self.prove("holds", [f], tac)["accepted"] for tac in ("rfl", "decide", "simp")):
                any(self.prove("not", [f], tac)["accepted"] for tac in ("decide", "simp"))
        st = self.state()
        verdict = next((rel for rel, ids in st.algebra.order() if rel in ("holds", "not") and ids[0] == st.rep(f)), None)
        return verdict, new

    def _recheck_fact(self, h, cwd, current):
        st = self.state()
        fact = st.facts[h]
        entry = {"h": h, "fact": fact["name"], "text": st.atoms[h]["text"], "places": []}
        guards, unread, reread = [], [], False
        for decl in fact["places"]:
            at, now = decl["at"], subject_id(decl["at"], cwd)
            rejected = {e["target"] for e in st.evidence.values() if e["kind"] == "sign_off" and e["outcome"] == "rejected"}
            seen = [m for p, m in fact["readings"] if p == at and m not in rejected]
            have = [m for m in seen if st.models[m]["subject"] == now
                    or (st.models[m].get("anchor") and _anchored(st.models[m]["quote"], at, cwd))]
            said = {st.models[m]["obj"]: m for m in have if not st.models[m]["binding"]}
            if not decl["reader"] and len(said) > 1:      # two readers, two values: not for the kernel to choose
                unread.append({"at": at, "why": "its readers disagree: " + "; ".join(
                    f'{m} ({", ".join(sorted(st.models[m]["by"]))}) reads {st.algebra.objs[o]["text"][:60]}' for o, m in said.items())})
                continue
            if decl["reader"]:                       # computed afresh every time, never taken from the record
                try:
                    was = have
                    have = [self.read_place(h, at, cwd=cwd)["m"]]
                    reread = reread or (bool(seen) and have != was[-1:])
                except KernelError as e:
                    unread.append({"at": at, "why": str(e)})
                    continue
            elif not have:
                no = [d for d in fact["declined"] if d["place"] == at and d["subject"] == now]
                unread.append({"at": at, "why": "it changed since it was read" if seen else "nobody has read it yet",
                               **({"declined": no} if no else {})})
                continue
            guards.append(have[-1])
            st = self.state()
            current = {**current, at: st.models[have[-1]]["subject"]}      # a quoted reading outlives other edits to its place
            entry["places"].append({"at": at, "reads as": st.algebra.objs[st.models[have[-1]]["obj"]]["text"], "m": have[-1],
                                    "by": "reader" if st.models[have[-1]]["binding"] else "stated"})
        if unread:
            entry.update(state="disputed" if any("disagree" in u["why"] for u in unread) else "stale", unread=unread)
        else:
            verdict, new = self._agreement(h, guards, [p["reads as"] for p in entry["places"]])
            entry["state"] = {"holds": "re-established" if new and reread else "current", "not": "violated"}.get(verdict, "uncovered")
        # Whether each reading stands is decided by the project's rules, not by a number.
        st = self.state()
        rules = load_rules(cwd)
        measured = measured_readers(cwd, rules)
        confirmed = {e["target"] for e in st.evidence.values() if e["kind"] == "sign_off" and e["outcome"] == "confirmed"}
        def value(obj):
            text = st.algebra.objs[obj]["text"]
            try:
                return json.loads(text)
            except ValueError:
                return text

        for p in entry["places"]:
            info = st.models[p["m"]]
            others = [st.models[q["m"]] for q in entry["places"] if q is not p and st.models[q["m"]]["obj"] == info["obj"]]
            readers = info["models"] & measured
            # a computed place: was the pattern ever checked against a reader who saw only the place?
            mine = [st.models[m] for at, m in fact["readings"] if at == p["at"]]
            stated = [s for s in mine if not s["binding"] and s["models"] & measured]
            same_blind = bool(info["binding"]) and any(
                s["subject"] == c["subject"] and value(s["obj"]) == value(c["obj"])
                for s in stated for c in mine if c["binding"] == info["binding"])
            has = {
                "computed": bool(info["binding"]),
                "confirmed by a person": p["m"] in confirmed,
                "blind": bool(readers),
                "words occur in the place": info["literal"],
                "agrees with a computed place": any(o["binding"] for o in others),
                "agrees with another place read blind": any(not o["binding"] and o["models"] & measured and o["blind"] - info["blind"] for o in others),
                "read the same by a second model": len(readers) > 1,
                "read the same blind": same_blind,
            }
            met = next((rule for rule in rules["a reading stands if any of"] if all(has[c] for c in rule)), None)
            p["stands"] = met is not None
            p["why"] = " + ".join(met) if met else "no rule is met"
            if not info["binding"]:
                p["has"] = {c: v for c, v in has.items() if c not in ("computed", "read the same blind")}
                p["unmeasured readers"] = sorted(info["models"] - measured) + (
                    ["a reader whose model was not recorded"] if info["blind"] and not info["models"] else [])
            else:
                now = subject_id(p["at"], cwd)
                p["has"] = {"read the same blind": same_blind}
                p["unmeasured readers"] = sorted({r for s in mine if not s["binding"] for r in s["models"]} - measured)
                p["read blind as"] = sorted({st.algebra.objs[s["obj"]]["text"] for s in stated if s["subject"] == now} - {p["reads as"]})
                p["declined"] = [d for d in fact["declined"] if d["place"] == p["at"] and d["subject"] == now]
        return entry

    def sync_facts(self, path):
        """Make the standing facts those declared in a file; facts no longer declared are withdrawn.

        The file is a JSON list of {"name", "type", "places", "value"?, "gloss"?}. A place is
        "path" or "path::part" (someone has to read it), or {"at": ..., "read": {...}} where
        "read" describes how to read it mechanically: see `pattern`.
        """
        with open(path, encoding="utf-8") as fh:
            declared = json.load(fh)
        keep = set()
        for d in declared:
            places = []
            for p in d["places"]:
                if isinstance(p, str):
                    places.append(p)
                elif "read" in p and set(p) == {"at", "read"}:
                    r = p["read"]
                    extra = set(r) - {"find", "find_all", "as", "sort", "unique"}
                    if extra:
                        raise KernelError(f"{d['name']}, {p['at']}: unknown keys in \"read\": {sorted(extra)}")
                    places.append({"at": p["at"], "reader": pattern(r.get("find"), r.get("find_all"), r.get("as", "string"),
                                                                    r.get("sort", False), r.get("unique", False))})
                else:
                    raise KernelError(f"{d['name']}: a place is a string or {{\"at\": ..., \"read\": {{...}}}}; "
                                      "expressions are not accepted in a list of facts")
            keep.add(self.claim_fact(d["name"], d["type"], places, d.get("value"), d.get("gloss", ""))["h"])
        st = self.state()
        for h in st.facts:
            if h not in keep and h not in st.withdrawn:
                self.withdraw(h, f"no longer declared in {os.path.basename(path)}")
        return keep

    def sign_off(self, m, who, confirmed=True):
        """A person has compared a stated reading (a model or a connection) with the thing itself."""
        return self.observe(m, "sign_off", "confirmed" if confirmed else "rejected", f"person:{who}")

    def reject_object(self, p, obj, proof):
        """Show a specification is not vacuous: Lean verifies that `obj` does NOT satisfy predicate `p`."""
        st = self.state()
        if st.algebra.kind(p) != "P":
            raise KernelError(f"unknown specification {p}")
        typ, obj = st.algebra.preds[p]["type"], _norm(obj)
        self._screen(obj)
        o = "O:" + _sha(typ, obj)
        with self._tx() as (con, st):
            if st.algebra.kind(o) is None:
                self._append(con, st, "object", {"id": o, "lean_type": typ, "text": obj})
        return {**self.prove("pred_rejects", [p, o], proof), "o": o}

    def ground(self, h, lean, prior=None, left_out="", added=""):
        """One connection hypothesis G: claim `h` means the closed Lean proposition `lean`.

        `left_out` and `added` record, in the author's words, what the sentence says that the
        formalization does not, and what the formalization fixes that the sentence leaves open.
        They change no number; they are what a person reviewing the connection needs to read.
        """
        lean = _norm(lean)
        self._screen(lean)
        self._well_typed(("Prop", lean))
        return self._ground(h, lean, {"prior": self.catalog["priors"]["grounding"] if prior is None else prior,
                                      "left_out": left_out, "added": added})

    def ground_at(self, h, subject, typ, predicate, obj, prior=None, model_prior=None, left_out="", added="",
                  binding=None, cwd=None):
        """Claim `h` says: the thing `subject` satisfies a property. Two separate hypotheses:

          G  `predicate : typ -> Prop` expresses the property the claim talks about
          M  `obj : typ` models `subject`     (shared by every claim about that subject and object)

        If both hold, the claim is true iff predicate(obj) is. Keeping specification and
        object apart also lets Lean say "same specification" and "same object" separately.
        """
        typ, predicate, obj = _norm(typ), _norm(predicate), _norm(obj)
        for text in (typ, predicate, obj):
            self._screen(text)
        self._well_typed((f"({typ}) → Prop", predicate), (typ, obj))
        pred = {"id": "P:" + _sha(typ, predicate), "type": typ, "text": predicate}
        ob = {"id": "O:" + _sha(typ, obj), "type": typ, "text": obj}
        priors = self.catalog["priors"]
        return self._ground(h, f"((({predicate}) : ({typ}) → Prop) (({obj}) : ({typ})))", {
            "prior": priors["specification"] if prior is None else prior,
            "pred": pred, "obj": ob, "subject": subject, "m": self._model_id(subject, ob, binding, cwd),
            "binding": binding,
            "model_prior": priors["model"] if model_prior is None else model_prior,
            "left_out": left_out, "added": added,
        })

    def _screen(self, text):
        if self.gate is not None:
            self.gate.screen(text)

    def _well_typed(self, *items):
        """Refuse a formalization Lean does not accept, at the moment it is stated."""
        if self.gate is not None:
            v = self.gate.typecheck(list(items))
            if not v["ok"]:
                raise KernelError("Lean does not accept this under Gamma: " + v["reason"])

    def _ground(self, h, lean, extra):
        f = "F:" + _sha(lean)
        g = f"G:{h[2:]}~{f[2:]}"
        with self._tx() as (con, st):
            if h not in st.atoms:
                raise KernelError(f"unknown claim {h}")
            if h in st.formal:
                raise KernelError(f"{h} is a formal claim: its meaning is fixed; use attach_model")
            if g not in st.atoms:
                self._append(con, st, "ground", {"g": g, "h": h, "f": f, "lean": lean, "by": self.actor, **extra})
            elif self.actor not in st.authors[g]:
                self._append(con, st, "concur", {"g": g, "by": self.actor})
        out = {"g": g, "f": f}
        if "m" in extra:
            out.update(m=extra["m"], p=extra["pred"]["id"], o=extra["obj"]["id"])
        return out

    def observe(self, target, kind, outcome, source):
        """Bayesian evidence. Likelihood comes from the catalog, never from the caller.

        `source` identifies where the evidence physically came from. The same
        (target, kind, source) is the same evidence no matter how many agents saw it.
        """
        spec = self.catalog["evidence"].get(kind)
        if spec is None or outcome not in spec["outcomes"]:
            raise KernelError(f"unknown evidence {kind}/{outcome}; see catalog")
        if target[0] not in spec["targets"]:
            raise KernelError(f"evidence kind {kind} cannot target {target[0]} atoms")
        return self._record(target, kind, outcome, source, {"likelihood": spec["outcomes"][outcome]})

    def _record(self, target, kind, outcome, source, extra):
        eid = "E:" + _sha(target, kind, source)
        with self._tx() as (con, st):
            if target not in st.atoms:
                raise KernelError(f"unknown atom {target}")
            if eid in st.retracted:
                raise KernelError(f"{eid} was retracted: {st.retracted[eid]}")
            old = st.evidence.get(eid)
            if old is not None:
                if old["outcome"] != outcome:
                    raise KernelError(f"{eid}: same source already recorded with outcome {old['outcome']}")
                return {"eid": eid, "duplicate": True}
            self._append(con, st, "observe", {
                "eid": eid, "target": target, "kind": kind, "outcome": outcome, "source": source, **extra,
            })
        return {"eid": eid, "duplicate": False}

    def retract(self, eid, justification):
        """Void a piece of evidence that turned out not to be what it claimed (a harness fault,
        a wrong command). Kept in the log; the same source cannot be recorded again."""
        if not justification.strip():
            raise KernelError("retraction needs a justification")
        with self._tx() as (con, st):
            if eid not in st.evidence:
                raise KernelError(f"unknown evidence {eid}")
            self._append(con, st, "retract", {"eid": eid, "justification": justification})
        return {"eid": eid}

    def observe_command(self, target, kind, command, cwd, timeout=900):
        """Run a check ourselves and record its result, so evidence is not self-reported."""
        r = subprocess.run(["bash", "-c", command], cwd=cwd, capture_output=True, text=True, timeout=timeout)
        outcome = "pass" if r.returncode == 0 else "fail"
        spec = self.catalog["evidence"].get(kind)
        if spec is None or outcome not in spec["outcomes"] or target[0] not in spec["targets"]:
            raise KernelError(f"evidence kind {kind} cannot be recorded for {target} by a command")
        tree = _tree(cwd)
        out = self._record(target, kind, outcome, f"cmd:{_sha(command)}@{tree}",
                           {"likelihood": spec["outcomes"][outcome], "command": command, "tree": tree})
        return {**out, "outcome": outcome, "tail": (r.stdout + r.stderr)[-800:]}

    def _model_id(self, subject, ob, binding, cwd):
        """M is identified by everything it claims: the code version, the term, and the binding."""
        if binding is None:
            return "M:" + _sha(subject, ob["id"])
        if cwd is not None and binding["language"] == "python":   # the way of calling the code must at least load
            r = self._run_code(binding, [], cwd)
            if isinstance(r, str):
                raise KernelError("the binding's setup does not run: " + r)
        return "M:" + _sha(subject, ob["id"], json.dumps(binding, sort_keys=True, ensure_ascii=False))

    def _model(self, m):
        st = self.state()
        if m not in st.models:
            raise KernelError(f"unknown model hypothesis {m}")
        if self.gate is None:
            raise KernelError("no Lean gate configured; cannot evaluate the object")
        if (st.models[m]["binding"] or {}).get("language") != "python":
            raise KernelError(f"{m} does not say how to call code, so it cannot be checked by running it")
        return st.algebra.objs[st.models[m]["obj"]], st.models[m]["binding"]

    @staticmethod
    def _run_code(binding, inputs, cwd, timeout=300):
        """What the code returns on each input, written out by the kernel; or an error string.
        An input on which the code raises yields "!raised <Type>": that is a result, not a fault."""
        lines = [_SHOW, binding["setup"]]
        for values in inputs:
            call = binding["call"]
            for i, (v, d) in enumerate(zip(values, binding["domains"])):
                call = call.replace("{%d}" % i, _python(v, d))
            lines.append(f"try:\n    print(_show({call}))\nexcept Exception as _e:\n    print('!raised ' + type(_e).__name__)")
        try:
            r = subprocess.run(["python3", "-c", "\n".join(lines)], cwd=cwd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return "the code did not finish in time"
        out = r.stdout.strip().splitlines()
        if r.returncode != 0 or len(out) != len(inputs):
            return (r.stdout + r.stderr)[-500:]
        return out

    def _compare(self, m, inputs, cwd):
        """[(lean arguments, agree?, model's value, code's value)] for each input, or an error string."""
        obj, binding = self._model(m)
        args = [" ".join(_lean(v, d) for v, d in zip(values, binding["domains"])) for values in inputs]
        lean = self.gate.evaluate(obj["type"], obj["text"], args)
        if not lean["ok"]:
            return "Lean could not evaluate the object on these arguments: " + lean["reason"]
        code = self._run_code(binding, inputs, cwd)
        if isinstance(code, str):
            return "the code could not be run: " + code
        return [(a, _values(c) == _values(v), v, c) for a, v, c in zip(args, lean["values"], code)]

    def observe_model(self, m, values, cwd):
        """A chosen check of model hypothesis M on one input, given as a list of argument values
        (an integer, "3/4", or a list of these; each must lie in its argument's domain).

        M is universal, so if M holds agreement is certain: one disagreement refutes M. An
        input picked by hand is not a random draw, so agreeing checks of this kind support M
        only as much as one of them does.
        """
        _, binding = self._model(m)
        if len(values) != len(binding["domains"]):
            raise KernelError(f"expected {len(binding['domains'])} arguments")
        res = self._compare(m, [tuple(_value(v, d) for v, d in zip(values, binding["domains"]))], cwd)
        if isinstance(res, str):
            return {"error": res}
        args, same, lean, code = res[0]
        outcome = "agree" if same else "disagree"
        out = self._record(m, "instance_check", outcome, f"chosen:{args}",
                           {"likelihood": self.catalog["evidence"]["instance_check"]["outcomes"][outcome], "args": args})
        return {**out, "outcome": outcome, "lean": lean, "code": code}

    def sample_model(self, m, cwd, n=10, seed=None):
        """Random checks of model hypothesis M. The kernel draws the inputs from M's recorded
        domains, calls the code the recorded way, and compares with the Lean object.

        Because the draws are random they are exchangeable, and each further agreement raises the
        lower probability of M (see credal.exchangeable_agreement). What gets supported is
        agreement on almost all inputs *under this distribution*. The same input is the same
        evidence, whoever drew it.
        """
        _, binding = self._model(m)
        rng = random.Random(seed)
        draws = sorted({tuple(DOMAINS[d][0](rng, binding["bound"]) for d in binding["domains"]) for _ in range(n)}, key=repr)
        res = self._compare(m, draws, cwd)
        if isinstance(res, str):
            return {"error": res}
        spec, new, disagreements = self.catalog["sampling"], 0, []
        for args, same, lean, code in res:
            r = self._record(m, "sampled_check", "agree" if same else "disagree", f"draw:{args}", {"args": args, **spec})
            new += not r["duplicate"]
            if not same:
                disagreements.append({"args": args, "lean": lean, "code": code})
        return {"drawn": len(draws), "new": new, "agree": len(draws) - len(disagreements), "disagreements": disagreements,
                "distribution": f"{' × '.join(binding['domains'])} within {binding['bound']}"}

    def declare_independent(self, eid, justification):
        """Assert evidence `eid` is conditionally independent of all other evidence on its target."""
        if not justification.strip():
            raise KernelError("independence needs a justification")
        with self._tx() as (con, st):
            if eid not in st.evidence:
                raise KernelError(f"unknown evidence {eid}")
            self._append(con, st, "independence", {"eid": eid, "justification": justification})
        return {"eid": eid}

    def prove(self, relation, args, proof):
        """Ask the Lean gate to verify a relation (see lindenbaum.RELATIONS).

        Nothing is recorded unless the gate accepts. A failed attempt is NOT evidence.
        """
        kinds = RELATIONS.get(relation)
        if kinds is None or len(kinds) != len(args):
            raise KernelError(f"relation must be one of {sorted(RELATIONS)} with matching arity")
        if self.gate is None:
            raise KernelError("no Lean gate configured; proofs cannot be accepted")
        verdict = self.gate.check(relation, self._items(relation, args, self.state().algebra), proof)
        if not verdict["ok"]:
            return {"accepted": False, "reason": verdict["reason"]}
        with self._tx() as (con, st):
            self._append(con, st, "proof", {
                "relation": relation, "args": list(args), "proof_sha": _sha(proof), "proof": proof,
                "axioms": verdict["axioms"], "gamma": verdict["gamma"],
            })
        return {"accepted": True, "axioms": verdict["axioms"], "gamma": verdict["gamma"]}

    @staticmethod
    def _items(relation, args, alg):
        """The (Lean type, Lean term) pairs a relation is stated about."""
        items = []
        for want, x in zip(RELATIONS[relation], args):
            if alg.kind(x) != want:
                raise KernelError(f"{relation} needs a {want} id, got {x}")
            if want == "F":
                items.append(("Prop", alg.props[x]["text"]))
            elif want == "P":
                items.append((f"({alg.preds[x]['type']}) → Prop", alg.preds[x]["text"]))
            else:
                items.append((alg.objs[x]["type"], alg.objs[x]["text"]))
        return items

    # ---- inference -------------------------------------------------------
    def infer(self, query, current=None, tree=None):
        """Lower and upper probability [lo, hi] of a formula, given all evidence and proofs.

        `current` maps a piece of code ("path::name") to its present version, and `tree` names
        the present working tree. Given them, only what was learnt about the code as it is now
        counts: models of other versions and check runs on other trees are set aside.
        """
        st = self.state()
        if current is not None:
            fresh = lambda m: current.get(st.models[m]["subject"].split("@")[0], st.models[m]["subject"]) == st.models[m]["subject"]
            st.links = [l for l in st.links if all(fresh(x) for x in l[0] if x[0] == "M")]
        if tree is not None:
            st.evidence = {k: e for k, e in st.evidence.items() if e.get("tree", tree) == tree}
        alg = st.algebra
        q = fm.rename(fm.parse(query), st.rep)
        for a in fm.atoms(q):
            if a not in st.atoms:
                raise KernelError(f"unknown atom {a}")
        A = lambda x: ("atom", x)

        # T: what a connection means, plus what Lean has verified
        links = sorted({(gs, h, st.rep(f)) for gs, h, f in st.links})
        all_of = lambda xs: xs[0] if len(xs) == 1 else ("and", xs[0], all_of(xs[1:]))
        order = alg.order()
        shape = {
            "holds": lambda a: A(a), "not": lambda a: ("not", A(a)),
            "implies": lambda a, b: ("imp", A(a), A(b)),
            "contradiction": lambda a, b: ("not", ("and", A(a), A(b))),
        }
        theory = [("imp", all_of([A(g) for g in gs]), ("iff", A(h), A(f))) for gs, h, f in links]
        theory += [shape[rel](*ids) for rel, ids in order]
        conflicts = self._conflicts(st)
        theory += [("not", ("and", A(a), A(b))) for a, b in conflicts]   # decisions nothing can meet together

        # The component of the query. A class Lean has decided is a constant: sharing
        # it creates no dependence, so it does not pull unrelated claims together.
        decided = alg.decided()
        comp = set(fm.atoms(q))
        seeds = set(comp)
        grew = True
        while grew:
            grew = False
            for grp in map(fm.atoms, theory):
                if grp & (comp - (decided - seeds)) and not grp <= comp:
                    comp |= grp
                    grew = True
        names = sorted(comp)
        if len(names) > self.max_atoms:
            raise KernelError(f"component has {len(names)} atoms (> {self.max_atoms}); split the query")
        links = [l for l in links if {*l[0], l[1], l[2]} <= comp]
        order = [(rel, ids) for rel, ids in order if set(ids) <= comp]
        env, m = stone_space(names, [t for t in theory if fm.atoms(t) <= comp])
        if m == 0:
            raise Conflict(f"no possible world satisfies the proofs over {names}")

        # Reliability model (Bovens-Hartmann). A link is reliable when all its hypotheses hold.
        #   - each hypothesis sits at its base rate; how hypotheses depend on one another is left open
        #   - the fact reported is independent of the hypotheses of the link reporting it
        #   - with no reliable link, a claim is a draw at its base rate, whatever the hypotheses are;
        #     the base rate is taken among the worlds where no decision that excludes it holds
        K = CredalSet(m)
        everywhere = np.ones(m, dtype=bool)

        def settings(guards):
            """Every truth assignment to `guards`, as (event, {guard: value})."""
            for values in itertools.product((True, False), repeat=len(guards)):
                event = everywhere.copy()
                for g, v in zip(guards, values):
                    event &= env[g] if v else ~env[g]
                yield event, dict(zip(guards, values))

        related = {f for _, ids in order for f in ids}
        for a in names:
            kind = st.atoms[a]["kind"]
            if kind in ("G", "M"):
                K.constrain(env[a], everywhere, st.prior[a])
            elif kind == "H":
                mine = [l for l in links if l[1] == a]
                possible = everywhere.copy()
                for x, y in conflicts:
                    if a in (x, y) and {x, y} <= comp:
                        possible &= ~env[y if a == x else x]
                for event, val in settings(sorted({g for l in mine for g in l[0]})):
                    if not any(all(val[g] for g in l[0]) for l in mine):
                        K.constrain(env[a], event & possible, st.prior[a])
            elif a not in related:
                K.constrain(env[a], everywhere, st.prior[a])
                for l in links:
                    if l[2] == a:
                        for event, _ in settings(l[0]):
                            K.constrain(env[a], event, st.prior[a])
        if not K.feasible():
            raise Conflict(f"base rates are incompatible with the verified proofs over {names}")

        # Evidence: virtual evidence on one atom; pieces on the same atom are joined by a copula class.
        blocks = {}
        for e in st.evidence.values():
            t = st.rep(e["target"])
            if t in comp:
                blocks.setdefault((t, e["block"]), []).append(e)
        # What the formal layer itself shows about a specification hypothesis G:
        #   its predicate excludes something (a verified counterexample), and
        #   more than one author connected the same claim to the same specification.
        derived, nonvacuous = self.catalog["derived"], alg.nonvacuous()
        spec_of = lambda f: alg.find(alg.props[f]["pred"]) if alg.props[f]["pred"] else alg.find(f)
        for gs, h, f in st.links:
            g = next((x for x in gs if x[0] == "G"), None)
            if g is None or g not in comp:
                continue
            if spec_of(f) in nonvacuous:
                blocks.setdefault((g, "shared"), []).append({"kind": "nonvacuous", "likelihood": derived["nonvacuous"]})
            agreeing = set()
            for gs2, h2, f2 in st.links:
                if h2 == h and gs2[0][0] == "G" and spec_of(f2) == spec_of(f):
                    agreeing |= st.authors.get(gs2[0], set())
            if len(agreeing) > 1:
                blocks.setdefault((g, "shared"), []).append(
                    {"kind": "concurrence", "likelihood": derived["independent_formalization"]})
        choices = []
        for (t, _), evs in sorted(blocks.items()):
            items = [((e["likelihood"][0],) * 2, (e["likelihood"][1],) * 2) for e in evs if "likelihood" in e]
            draws = [e for e in evs if e["kind"] == "sampled_check"]
            if not items and not draws:
                continue
            if any(e["outcome"] == "disagree" for e in draws):
                items.append(((0, 0), (1, 1)))          # a counterexample refutes a universal hypothesis
            elif draws:
                rng = exchangeable_agreement(len(draws), draws[0]["agree_rate_if_wrong"], draws[0]["min_concentration"])
                items.append(((1, 1), rng))
            choices.append([np.where(env[t], pt, pf) for pt, pf in joint_likelihood(items, self.dependence)])
        candidates = (np.prod(combo, axis=0) if combo else np.ones(m) for combo in itertools.product(*choices))
        b = K.bounds(np.asarray(fm.evaluate(q, env), dtype=bool) & everywhere, candidates)
        if b is None:
            raise Conflict(f"the recorded evidence has probability zero over {names}")
        return {"lo": b[0], "hi": b[1], "atoms": names, "worlds": m}

    # ---- decisions over time ------------------------------------------------
    @staticmethod
    def _conflicts(st):
        """Pairs of standing formal claims about the same code whose specifications Lean has shown disjoint."""
        hs = [h for h in st.formal if h not in st.withdrawn]
        return [(a, b) for i, a in enumerate(hs) for b in hs[i + 1:]
                if st.formal[a]["subject"] == st.formal[b]["subject"]
                and st.algebra.disjoint(st.formal[a]["pred"], st.formal[b]["pred"])]

    def withdraw(self, h, justification):
        """A person declares that a decision no longer stands (it was superseded or was wrong)."""
        if not justification.strip():
            raise KernelError("withdrawing a decision needs a justification")
        with self._tx() as (con, st):
            if st.atoms.get(h, {}).get("kind") != "H":
                raise KernelError(f"unknown claim {h}")
            self._append(con, st, "withdraw", {"h": h, "justification": justification})
        return {"h": h}

    def recheck(self, cwd, n=20):
        """Hold every standing decision against the files as they are in `cwd`, without anyone's judgement.

        A decision says a file satisfies a specification, through a reading of the file as a
        Lean term. When the file changes, what happens depends on how it was read:

          by a reader      the term is recomputed and the stored proofs are tried again
          as a code model  the same term is checked against the new code by fresh random draws
          by an agent      nothing can be done here: someone has to read the file again

          current         the file is the version the decision was established for
          re-established  the file changed and the decision was carried over mechanically
          violated        Lean has verified that the file, as read, does NOT satisfy the specification
          uncovered       the file changed and the old proof no longer covers it. This is not a
                          verdict: the decision may still hold, but nothing shows it
          stale           the file changed since an agent read it
          unsupported     no reading was ever attached
        """
        st = self.state()
        standing = [h for h in st.formal if h not in st.withdrawn]
        current = {**self.versions(cwd), **{st.formal[h]["subject"]: subject_id(st.formal[h]["subject"], cwd) for h in standing}}
        tree, report = _tree(cwd), []
        for h in standing:
            st = self.state()
            now = current[st.formal[h]["subject"]]
            entry = {"h": h, "text": st.atoms[h]["text"], "subject": now,
                     "spec": st.algebra.preds[st.formal[h]["pred"]]["text"]}
            mine = [(x, f) for gs, hh, f in st.links if hh == h for x in gs if x[0] == "M"]
            by_reader = mine and (st.models[mine[-1][0]]["binding"] or {}).get("language") == "reader"
            if not by_reader and any(st.models[m]["subject"] == now for m, _ in mine):
                entry["state"] = "current"
            elif not mine:
                entry["state"] = "unsupported"
            else:
                old, old_f = mine[-1]
                how = (st.models[old]["binding"] or {}).get("language")
                obj = st.algebra.objs[st.models[old]["obj"]]
                try:
                    if how == "reader":              # computed afresh every time, never taken from the record
                        new = self.attach_derived(h, st.models[old]["binding"], cwd)
                        if new["m"] in [m for m, _ in mine]:
                            entry["state"] = "current"
                        else:
                            entry.update(self._carry_proofs(old_f, new["f"]))
                    elif how == "python":
                        new = self.attach_model(h, obj["text"], subject_version=now, binding=st.models[old]["binding"], cwd=cwd)
                        r = self.sample_model(new["m"], cwd, n=n)
                        if "error" in r:
                            entry.update(state="unsupported", error=r["error"])
                        elif r["disagreements"]:
                            entry.update(state="uncovered", counterexample=r["disagreements"][0], model=obj["text"])
                        else:
                            entry["state"] = "re-established"
                    else:
                        entry["state"] = "stale"
                except KernelError as e:
                    entry.update(state="unsupported", error=str(e))
            for kind, command in sorted({(e["kind"], e["command"]) for e in st.evidence.values()
                                         if e["target"] == h and "tree" in e}):
                self.observe_command(h, kind, command, cwd)
            st = self.state()
            if entry["state"] == "current":
                # the file is read, but what it reads as may not be proved yet: try what was proved before
                decided = st.algebra.decided()
                now_f = [f for gs, hh, f in st.links if hh == h and all(st.models[x]["subject"] == now for x in gs if x[0] == "M")]
                before = [f for _, f in mine if st.rep(f) in decided]
                if now_f and before and not any(st.rep(f) in decided for f in now_f):
                    carried = self._carry_proofs(before[-1], now_f[-1])
                    if carried["state"] != "re-established":
                        entry.update(carried)
                st = self.state()
            refuted = {x for rel, ids in st.algebra.order() if rel == "not" for x in ids}
            if any(st.rep(f) in refuted for gs, hh, f in st.links
                   if hh == h and all(st.models[x]["subject"] == now for x in gs if x[0] == "M")):
                entry["state"] = "violated"
            try:
                b = self.infer(h, current=current, tree=tree)
                entry.update(lo=b["lo"], hi=b["hi"])
            except KernelError as e:
                entry.update(lo=0.0, hi=1.0, error=str(e))
            report.append(entry)
        for h in [x for x in self.state().facts if x not in self.state().withdrawn]:
            current = {**current, **{p["at"]: subject_id(p["at"], cwd) for p in self.state().facts[h]["places"]}}
            report.append(self._recheck_fact(h, cwd, current))
        # A claim in natural language can only be held by the commands recorded for it: run them again.
        st = self.state()
        for h, info in st.atoms.items():
            if info["kind"] != "H" or h in st.formal or h in st.facts or h in st.withdrawn:
                continue
            commands = sorted({(e["kind"], e["command"]) for e in st.evidence.values() if e["target"] == h and "tree" in e})
            if not commands:
                continue
            runs = [self.observe_command(h, kind, command, cwd) for kind, command in commands]
            failed = [c for (k_, c), r in zip(commands, runs) if r["outcome"] != "pass"]
            b = self.infer(h, current=current, tree=tree)
            entry = {"h": h, "text": info["text"], "natural_language": True, "lo": b["lo"], "hi": b["hi"],
                     "state": "checks fail" if failed else "checks pass", "checks": len(commands)}
            if failed:
                entry["failed"] = failed[0]
            report.append(entry)
        st = self.state()
        return {"decisions": report, "tree": tree,
                "conflicts": [{"a": a, "b": b, "subject": st.formal[a]["subject"],
                               "specs": [st.algebra.preds[st.formal[x]["pred"]]["text"] for x in (a, b)]}
                              for a, b in self._conflicts(st)]}

    def _carry_proofs(self, old_f, new_f):
        """The file was read again and gives proposition `new_f`. Try what was proved about `old_f`."""
        st = self.state()
        if st.rep(old_f) == st.rep(new_f):
            return {"state": "re-established"}              # the reading did not change
        stored = [p for p in st.proofs if p["relation"] in ("holds", "not") and p["args"] == [old_f] and p.get("proof")]
        for p in stored:
            if self.prove(p["relation"], [new_f], p["proof"])["accepted"]:
                return {"state": "re-established" if p["relation"] == "holds" else "violated"}
        # A specification that can be decided is often decided by the same tactics either way:
        # try what proved the old proposition on the opposite of the new one.
        for p in stored:
            other = "not" if p["relation"] == "holds" else "holds"
            if self.prove(other, [new_f], p["proof"])["accepted"]:
                return {"state": "violated" if other == "not" else "re-established"}
        if self.prove("not", [new_f], "decide")["accepted"]:
            return {"state": "violated"}
        return {"state": "uncovered", "note": "the stored proof does not go through for the file as it is now"}

    def versions(self, cwd):
        """The present version of every piece of code some model is about, as found in `cwd`.

        A claim about code means the code as it is now. A model of another version, supported
        or refuted, is about something else; counted together with the present one it only
        blurs the picture. Pass the result as `current` to `infer`.
        """
        st = self.state()
        bases = ({info["subject"].split("@")[0] for info in st.models.values()} | {f["subject"] for f in st.formal.values()}
                 | {p["at"] for f in st.facts.values() for p in f["places"]})
        found = {b: subject_id(b, cwd) for b in bases}
        for info in st.models.values():              # a quoted reading is of the present version while its quote is there
            base = info["subject"].split("@")[0]
            if info.get("anchor") and _anchored(info["quote"], base, cwd):
                found[base] = info["subject"]
        return {b: v for b, v in found.items() if "@" in v}     # code that is not here is left alone

    def distance(self, a, b, current=None):
        """Frechet-Nikodym distance d(a, b) = P(a and b disagree), as an interval.

        Lean makes it exactly 0 between equal propositions; a connection bounds it by
        1 - P(G); the triangle inequality does the rest.
        """
        r = self.infer(f"({a}) <-> ({b})", current=current)
        return {"lo": round(1 - r["hi"], 9), "hi": round(1 - r["lo"], 9)}

    def status(self, current=None):
        st = self.state()
        alg = st.algebra
        out = {"claims": [], "evidence": len(st.evidence), "proofs": st.proofs,
               "models": {}, "propositions": alg.classes("F"),
               "specifications": {c: [alg.preds[p] for p in ps] for c, ps in alg.classes("P").items()},
               "objects": {c: [alg.objs[o] for o in os_] for c, os_ in alg.classes("O").items()}}
        for mid, info in st.models.items():
            if current is not None and current.get(info["subject"].split("@")[0], info["subject"]) != info["subject"]:
                continue                                    # a model of another version of the code
            b = self.infer(mid, current=current)
            out["models"][mid] = {**info, "lo": b["lo"], "hi": b["hi"]}
        for a, info in st.atoms.items():
            if info["kind"] != "H":
                continue
            try:
                b = self.infer(a, current=current)
                entry = {"h": a, "text": info["text"], "lo": b["lo"], "hi": b["hi"]}
            except KernelError as e:
                entry = {"h": a, "text": info["text"], "error": str(e)}
            entry["formal"] = a in st.formal
            entry["means"] = []
            for gs, h, f in st.links:
                if h == a:
                    p = alg.props[f]
                    entry["means"].append({
                        "g": next((x for x in gs if x[0] == "G"), None),
                        **st.notes.get(next((x for x in gs if x[0] == "G"), ""), {}),
                        "m": next((x for x in gs if x[0] == "M"), None), "f": f,
                        "proposition_class": alg.find(f),
                        "specification_class": p["pred"] and alg.find(p["pred"]),
                        "object_class": p["obj"] and alg.find(p["obj"]),
                    })
            out["claims"].append(entry)
        return out
