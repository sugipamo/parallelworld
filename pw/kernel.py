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
import sqlite3
import subprocess
import time
from contextlib import contextmanager

import numpy as np

from . import formula as fm
from .credal import COPULAS, CredalSet, exchangeable_agreement, joint_likelihood, stone_space
from .lindenbaum import RELATIONS, Lindenbaum

CATALOG_PATH = os.path.join(os.path.dirname(__file__), "catalog.json")


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
                guards = (p["g"],)
            if p.get("m"):
                if p["m"] not in self.atoms:
                    self.atoms[p["m"]] = {"kind": "M", "text": f'{obj["id"]} models {p["subject"]}'}
                    self.prior[p["m"]] = p["model_prior"]
                    self.models[p["m"]] = {"subject": p["subject"], "obj": obj["id"]}
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

    def attach_model(self, h, obj, subject_version=None, model_prior=None):
        """For a formal claim: state that Lean object `obj` models the claim's code.
        Introduces only the model hypothesis M; if M holds, the claim is true iff predicate(obj) is."""
        st = self.state()
        if h not in st.formal:
            raise KernelError(f"{h} is not a formal claim; use ground_at")
        pred = dict(st.algebra.preds[st.formal[h]["pred"]], id=st.formal[h]["pred"])
        obj = _norm(obj)
        self._screen(obj)
        subject = subject_version or st.formal[h]["subject"]
        ob = {"id": "O:" + _sha(pred["type"], obj), "type": pred["type"], "text": obj}
        lean = f"((({pred['text']}) : ({pred['type']}) → Prop) (({obj}) : ({pred['type']})))"
        f, m = "F:" + _sha(lean), "M:" + _sha(subject, ob["id"])
        with self._tx() as (con, st):
            if not any(l == ((m,), h, f) for l in st.links):
                self._append(con, st, "ground", {
                    "h": h, "f": f, "lean": lean, "pred": pred, "obj": ob, "subject": subject, "m": m,
                    "model_prior": self.catalog["priors"]["model"] if model_prior is None else model_prior,
                })
        return {"m": m, "f": f, "p": pred["id"], "o": ob["id"]}

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

    def ground(self, h, lean, prior=None):
        """One connection hypothesis G: claim `h` means the closed Lean proposition `lean`."""
        lean = _norm(lean)
        self._screen(lean)
        return self._ground(h, lean, {"prior": self.catalog["priors"]["grounding"] if prior is None else prior})

    def ground_at(self, h, subject, typ, predicate, obj, prior=None, model_prior=None):
        """Claim `h` says: the thing `subject` satisfies a property. Two separate hypotheses:

          G  `predicate : typ -> Prop` expresses the property the claim talks about
          M  `obj : typ` models `subject`     (shared by every claim about that subject and object)

        If both hold, the claim is true iff predicate(obj) is. Keeping specification and
        object apart also lets Lean say "same specification" and "same object" separately.
        """
        typ, predicate, obj = _norm(typ), _norm(predicate), _norm(obj)
        for text in (typ, predicate, obj):
            self._screen(text)
        pred = {"id": "P:" + _sha(typ, predicate), "type": typ, "text": predicate}
        ob = {"id": "O:" + _sha(typ, obj), "type": typ, "text": obj}
        priors = self.catalog["priors"]
        return self._ground(h, f"((({predicate}) : ({typ}) → Prop) (({obj}) : ({typ})))", {
            "prior": priors["specification"] if prior is None else prior,
            "pred": pred, "obj": ob, "subject": subject, "m": "M:" + _sha(subject, ob["id"]),
            "model_prior": priors["model"] if model_prior is None else model_prior,
        })

    def _screen(self, text):
        if self.gate is not None:
            self.gate.screen(text)

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
        out = self.observe(target, kind, outcome, source=f"cmd:{_sha(command)}@{_tree(cwd)}")
        return {**out, "outcome": outcome, "tail": (r.stdout + r.stderr)[-800:]}

    def _model(self, m):
        st = self.state()
        if m not in st.models:
            raise KernelError(f"unknown model hypothesis {m}")
        if self.gate is None:
            raise KernelError("no Lean gate configured; cannot evaluate the object")
        return st.algebra.objs[st.models[m]["obj"]]

    def _compare(self, obj, lean_args, commands, cwd, timeout):
        """[(agree?, lean value, code output)] for each input, or an error string."""
        lean = self.gate.evaluate(obj["type"], obj["text"], lean_args)
        if not lean["ok"]:
            return "Lean could not evaluate the object: " + lean["reason"]
        out = []
        for value, command in zip(lean["values"], commands):
            r = subprocess.run(["bash", "-c", command], cwd=cwd, capture_output=True, text=True, timeout=timeout)
            if r.returncode != 0:
                return "command failed: " + (r.stdout + r.stderr)[-500:]
            code = " ".join(r.stdout.split())
            out.append((code.lower() == value.lower(), value, code))
        return out

    def observe_model(self, m, lean_args, command, cwd, timeout=300):
        """A chosen check of model hypothesis M: evaluate the Lean object on `lean_args`, run
        `command` (which must print what the real code returns for the same input), compare.

        M is universal, so if M holds agreement is certain: one disagreement refutes M. An
        input picked by hand is not a random draw, so agreeing checks of this kind support M
        only as much as one of them does.
        """
        obj = self._model(m)
        res = self._compare(obj, [lean_args], [command], cwd, timeout)
        if isinstance(res, str):
            return {"error": res}
        same, lean, code = res[0]
        out = self.observe(m, "instance_check", "agree" if same else "disagree",
                           source=f"args:{_sha(_norm(lean_args))}@cmd:{_sha(command)}@{_tree(cwd)}")
        return {**out, "outcome": "agree" if same else "disagree", "lean": lean, "code": code}

    def sample_model(self, m, command, cwd, n=10, bound=15, seed=None, timeout=300):
        """Random checks of model hypothesis M. The kernel draws the inputs itself.

        `command` is a shell template with {0}, {1}, ... for the arguments; it must print
        what the real code returns. Arguments are drawn uniformly: Nat from 0..bound, Int
        from -bound..bound. Because the draws are random they are exchangeable, and each
        further agreement raises the lower probability of M (see credal.exchangeable_agreement).
        What gets supported is agreement on almost all inputs *under this distribution*.
        """
        obj = self._model(m)
        domains = [t.strip() for t in obj["type"].split("→")][:-1]
        if not domains or any(d not in ("Nat", "Int") for d in domains):
            raise KernelError(f"can only draw Nat and Int arguments, not {obj['type']}")
        spec = self.catalog["sampling"]
        rng = random.Random(seed)
        draws = sorted({tuple(rng.randint(0 if d == "Nat" else -bound, bound) for d in domains) for _ in range(n)})
        lean_args = [" ".join(str(v) if v >= 0 else f"({v})" for v in d) for d in draws]
        commands = []
        for d in draws:
            c = command
            for i, v in enumerate(d):
                c = c.replace("{%d}" % i, str(v))
            commands.append(c)
        res = self._compare(obj, lean_args, commands, cwd, timeout)
        if isinstance(res, str):
            return {"error": res}
        tree, dist = _tree(cwd), f"uniform {' × '.join(domains)} within {bound}"
        new, disagreements = 0, []
        for d, (same, lean, code) in zip(draws, res):
            r = self._record(m, "sampled_check", "agree" if same else "disagree",
                             f"draw:{d}@cmd:{_sha(command)}@{tree}",
                             {"args": list(d), "distribution": dist, **spec})
            new += not r["duplicate"]
            if not same:
                disagreements.append({"args": list(d), "lean": lean, "code": code})
        return {"drawn": len(draws), "new": new, "agree": len(draws) - len(disagreements),
                "disagreements": disagreements, "distribution": dist}

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
                "relation": relation, "args": list(args), "proof_sha": _sha(proof),
                "axioms": verdict["axioms"], "gamma": verdict["gamma"],
            })
        return {"accepted": True, "axioms": verdict["axioms"], "gamma": verdict["gamma"]}

    # ---- inference -------------------------------------------------------
    def infer(self, query):
        """Lower and upper probability [lo, hi] of a formula, given all evidence and proofs."""
        st = self.state()
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
        #   - with no reliable link, a claim is a draw at its base rate, whatever the hypotheses are
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
                for event, val in settings(sorted({g for l in mine for g in l[0]})):
                    if not any(all(val[g] for g in l[0]) for l in mine):
                        K.constrain(env[a], event, st.prior[a])
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

    def distance(self, a, b):
        """Frechet-Nikodym distance d(a, b) = P(a and b disagree), as an interval.

        Lean makes it exactly 0 between equal propositions; a connection bounds it by
        1 - P(G); the triangle inequality does the rest.
        """
        r = self.infer(f"({a}) <-> ({b})")
        return {"lo": round(1 - r["hi"], 9), "hi": round(1 - r["lo"], 9)}

    def status(self):
        st = self.state()
        alg = st.algebra
        out = {"claims": [], "evidence": len(st.evidence), "proofs": st.proofs,
               "models": {}, "propositions": alg.classes("F"),
               "specifications": {c: [alg.preds[p] for p in ps] for c, ps in alg.classes("P").items()},
               "objects": {c: [alg.objs[o] for o in os_] for c, os_ in alg.classes("O").items()}}
        for mid, info in st.models.items():
            b = self.infer(mid)
            out["models"][mid] = {**info, "lo": b["lo"], "hi": b["hi"]}
        for a, info in st.atoms.items():
            if info["kind"] != "H":
                continue
            try:
                b = self.infer(a)
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
                        "m": next((x for x in gs if x[0] == "M"), None), "f": f,
                        "proposition_class": alg.find(f),
                        "specification_class": p["pred"] and alg.find(p["pred"]),
                        "object_class": p["obj"] and alg.find(p["obj"]),
                    })
            out["claims"].append(entry)
        return out
