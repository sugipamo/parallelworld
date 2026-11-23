"""Knowledge kernel: append-only event log, and the model that ties the layers together.

  lindenbaum.py   formal layer: what Lean has verified, as a presented Boolean algebra
  credal.py       probabilistic layer: credal sets, generalized Bayes rule
  this file       the events, and the reliability model connecting claims to propositions

Events are of three kinds: model extension (claim / ground / independence),
evidence (observe), and verified proof. A proof shrinks the space of worlds; evidence
reweights measures on it. Nothing else changes the state.
"""
import hashlib
import itertools
import json
import os
import random
import re
import sqlite3
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


def reader(expr, fmt="json"):
    """A recorded, mechanical way to read a file as a Lean term.

    `expr` is a Python expression over `data` (the parsed file: JSON, or the text) that
    evaluates to the Lean term as a string. Helpers: `permille(x)` gives a number as a whole
    number of thousandths and fails if it is not one; `lean_string(s)` writes a string literal.
    With a reader nobody has to be believed about what the file says: the term is recomputed
    whenever the file changes.
    """
    if fmt not in ("json", "text") or not expr.strip():
        raise KernelError("a reader needs an expression and a format: json or text")
    return {"language": "reader", "format": fmt, "expr": expr.strip()}


_READ = """
import json, sys
from fractions import Fraction
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


def _tree(cwd):
    """Identifies the state of the working tree a check ran against."""
    def git(*args):
        r = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
        return r.stdout if r.returncode == 0 else f"nogit:{time.time()}"
    return "tree:" + _sha(git("rev-parse", "HEAD"), git("status", "--porcelain"), git("diff", "HEAD"))


def subject_id(subject, cwd):
    """`path::name` plus a hash of the file, so a hypothesis about code dies when the code changes."""
    path = os.path.join(cwd, subject.split("::")[0])
    if os.path.isfile(path):
        with open(path, "rb") as fh:
            return f"{subject}@{hashlib.sha256(fh.read()).hexdigest()[:10]}"
    return subject


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
            if p.get("pred"):
                self.formal[p["h"]] = {"subject": p["subject"], "pred": p["pred"]["id"]}
                self.algebra.add_pred(p["pred"]["id"], p["pred"]["type"], p["pred"]["text"])
        elif typ == "object":
            self.algebra.add_obj(p["id"], p["lean_type"], p["text"])
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
        self.max_atoms = max_atoms
        if catalog is None:
            with open(CATALOG_PATH) as fh:
                catalog = json.load(fh)
        self.catalog = catalog
        os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)
        with self._tx() as (con, _):
            con.execute(
                "CREATE TABLE IF NOT EXISTS events (id INTEGER PRIMARY KEY AUTOINCREMENT,"
                " ts REAL, actor TEXT, type TEXT, payload TEXT)"
            )

    # ---- event log -------------------------------------------------------
    @contextmanager
    def _tx(self):
        """Exclusive transaction: replay + check + append is atomic across processes."""
        con = sqlite3.connect(self.db_path, timeout=60, isolation_level=None)
        try:
            con.execute("BEGIN IMMEDIATE")
            state = State()
            try:
                for typ, payload in con.execute("SELECT type, payload FROM events ORDER BY id"):
                    state.apply(typ, json.loads(payload))
            except sqlite3.OperationalError:
                pass  # table not created yet
            yield con, state
            con.execute("COMMIT")
        except BaseException:
            con.execute("ROLLBACK")
            raise
        finally:
            con.close()

    def _append(self, con, state, typ, payload):
        con.execute(
            "INSERT INTO events (ts, actor, type, payload) VALUES (?,?,?,?)",
            (time.time(), self.actor, typ, json.dumps(payload, ensure_ascii=False)),
        )
        state.apply(typ, payload)

    def state(self):
        with self._tx() as (_, state):
            return state

    def events(self):
        con = sqlite3.connect(self.db_path)
        try:
            return [
                {"id": i, "ts": ts, "actor": a, "type": t, **json.loads(p)}
                for i, ts, a, t, p in con.execute("SELECT id, ts, actor, type, payload FROM events ORDER BY id")
            ]
        finally:
            con.close()

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
        path = os.path.join(cwd, subject.split("::")[0].split("@")[0])
        r = subprocess.run(["python3", "-c", _READ, path, rd["format"], rd["expr"]], capture_output=True, text=True, timeout=120)
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
        alg = self.state().algebra
        items = []
        for want, x in zip(kinds, args):
            if alg.kind(x) != want:
                raise KernelError(f"{relation} needs a {want} id, got {x}")
            if want == "F":
                items.append(("Prop", alg.props[x]["text"]))
            elif want == "P":
                items.append((f"({alg.preds[x]['type']}) → Prop", alg.preds[x]["text"]))
            else:
                items.append((alg.objs[x]["type"], alg.objs[x]["text"]))
        verdict = self.gate.check(relation, items, proof)
        if not verdict["ok"]:
            return {"accepted": False, "reason": verdict["reason"]}
        with self._tx() as (con, st):
            self._append(con, st, "proof", {
                "relation": relation, "args": list(args), "proof_sha": _sha(proof), "proof": proof,
                "axioms": verdict["axioms"], "gamma": verdict["gamma"],
            })
        return {"accepted": True, "axioms": verdict["axioms"], "gamma": verdict["gamma"]}

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
            if any(st.models[m]["subject"] == now for m, _ in mine):
                entry["state"] = "current"
            elif not mine:
                entry["state"] = "unsupported"
            else:
                old, old_f = mine[-1]
                how = (st.models[old]["binding"] or {}).get("language")
                obj = st.algebra.objs[st.models[old]["obj"]]
                try:
                    if how == "reader":
                        new = self.attach_derived(h, st.models[old]["binding"], cwd)
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
        # A claim in natural language can only be held by the commands recorded for it: run them again.
        st = self.state()
        for h, info in st.atoms.items():
            if info["kind"] != "H" or h in st.formal or h in st.withdrawn:
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
        for p in st.proofs:
            if p["relation"] in ("holds", "not") and p["args"] == [old_f] and p.get("proof"):
                if self.prove(p["relation"], [new_f], p["proof"])["accepted"]:
                    return {"state": "re-established" if p["relation"] == "holds" else "violated"}
        if self.prove("not", [new_f], "decide")["accepted"]:  # a decidable specification can simply be evaluated
            return {"state": "violated"}
        return {"state": "uncovered", "note": "the stored proof does not go through for the file as it is now"}

    def versions(self, cwd):
        """The present version of every piece of code some model is about, as found in `cwd`.

        A claim about code means the code as it is now. A model of another version, supported
        or refuted, is about something else; counted together with the present one it only
        blurs the picture. Pass the result as `current` to `infer`.
        """
        st = self.state()
        bases = {info["subject"].split("@")[0] for info in st.models.values()} | {f["subject"] for f in st.formal.values()}
        found = {b: subject_id(b, cwd) for b in bases}
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
