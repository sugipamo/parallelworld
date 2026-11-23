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
import sqlite3
import subprocess
import time
from contextlib import contextmanager

import numpy as np

from . import formula as fm
from .credal import COPULAS, CredalSet, joint_likelihood, stone_space
from .lindenbaum import RELATIONS, Lindenbaum

CATALOG_PATH = os.path.join(os.path.dirname(__file__), "catalog.json")


class KernelError(Exception):
    pass


class Conflict(KernelError):
    """Priors / evidence are jointly impossible given the verified proofs."""


def _sha(*parts):
    return hashlib.sha256("\x00".join(parts).encode()).hexdigest()[:10]


def _norm(text):
    return " ".join(text.split())


class State:
    def __init__(self):
        self.atoms = {}      # world atoms: id -> {"kind": H|F|G, "text": str}
        self.prior = {}      # base rates
        self.links = []      # (g, h, f): connection g says claim h means proposition f
        self.evidence = {}   # eid -> dict
        self.proofs = []     # proof events as recorded
        self.algebra = Lindenbaum()

    def rep(self, a):
        return self.algebra.find(a)

    def apply(self, typ, p):
        if typ == "claim":
            self.atoms[p["h"]] = {"kind": "H", "text": p["text"]}
            self.prior[p["h"]] = p["prior"]
        elif typ == "ground":
            pred, obj = p.get("pred"), p.get("obj")
            if pred:
                self.algebra.add_pred(pred["id"], pred["type"], pred["text"])
                self.algebra.add_obj(obj["id"], obj["type"], obj["text"])
            if p["f"] not in self.atoms:
                self.atoms[p["f"]] = {"kind": "F", "text": p["lean"]}
                self.prior[p["f"]] = self.prior[p["h"]]
            self.algebra.add_prop(p["f"], p["lean"], pred and pred["id"], obj and obj["id"])
            self.atoms[p["g"]] = {"kind": "G", "text": f'{p["h"]} means {p["f"]}'}
            self.prior[p["g"]] = p["prior"]
            self.links.append((p["g"], p["h"], p["f"]))
        elif typ == "observe":
            self.evidence[p["eid"]] = dict(p, block="shared")
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

    def ground(self, h, lean, prior=None):
        """Connection hypothesis G: claim `h` means the closed Lean proposition `lean`."""
        return self._ground(h, _norm(lean), None, None, prior)

    def ground_at(self, h, typ, predicate, obj, prior=None):
        """Connection hypothesis G: claim `h` says object `obj : typ` satisfies `predicate : typ -> Prop`.

        Keeping the specification and the object apart lets Lean say "same
        specification" and "same object" separately; closed propositions cannot.
        """
        typ, predicate, obj = _norm(typ), _norm(predicate), _norm(obj)
        pred = {"id": "P:" + _sha(typ, predicate), "type": typ, "text": predicate}
        ob = {"id": "O:" + _sha(typ, obj), "type": typ, "text": obj}
        lean = f"((({predicate}) : ({typ}) → Prop) (({obj}) : ({typ})))"
        return self._ground(h, lean, pred, ob, prior)

    def _ground(self, h, lean, pred, obj, prior):
        if self.gate is not None:
            for text in (lean, *((pred["type"],) if pred else ())):
                self.gate.screen(text)
        f = "F:" + _sha(lean)
        g = f"G:{h[2:]}~{f[2:]}"
        with self._tx() as (con, st):
            if h not in st.atoms:
                raise KernelError(f"unknown claim {h}")
            if g not in st.atoms:
                prior = self.catalog["priors"]["grounding"] if prior is None else prior
                event = {"g": g, "h": h, "f": f, "lean": lean, "prior": prior}
                if pred:
                    event.update(pred=pred, obj=obj)
                self._append(con, st, "ground", event)
        out = {"g": g, "f": f}
        if pred:
            out.update(p=pred["id"], o=obj["id"])
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
        eid = "E:" + _sha(target, kind, source)
        with self._tx() as (con, st):
            if target not in st.atoms:
                raise KernelError(f"unknown atom {target}")
            old = st.evidence.get(eid)
            if old is not None:
                if old["outcome"] != outcome:
                    raise KernelError(f"{eid}: same source already recorded with outcome {old['outcome']}")
                return {"eid": eid, "duplicate": True}
            self._append(con, st, "observe", {
                "eid": eid, "target": target, "kind": kind, "outcome": outcome,
                "source": source, "likelihood": spec["outcomes"][outcome],
            })
        return {"eid": eid, "duplicate": False}

    def observe_command(self, target, kind, command, cwd, timeout=900):
        """Run a check ourselves and record its result, so evidence is not self-reported."""
        def git(*args):
            r = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
            return r.stdout if r.returncode == 0 else f"nogit:{time.time()}"
        tree = _sha(git("rev-parse", "HEAD"), git("status", "--porcelain"), git("diff", "HEAD"))
        r = subprocess.run(["bash", "-c", command], cwd=cwd, capture_output=True, text=True, timeout=timeout)
        outcome = "pass" if r.returncode == 0 else "fail"
        out = self.observe(target, kind, outcome, source=f"cmd:{_sha(command)}@tree:{tree}")
        return {**out, "outcome": outcome, "tail": (r.stdout + r.stderr)[-800:]}

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
        links = sorted({(g, h, st.rep(f)) for g, h, f in st.links})
        order = alg.order()
        shape = {
            "holds": lambda a: A(a), "not": lambda a: ("not", A(a)),
            "implies": lambda a, b: ("imp", A(a), A(b)),
            "contradiction": lambda a, b: ("not", ("and", A(a), A(b))),
        }
        theory = [("imp", A(g), ("iff", A(h), A(f))) for g, h, f in links]
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
        links = [l for l in links if set(l) <= comp]
        order = [(rel, ids) for rel, ids in order if set(ids) <= comp]
        env, m = stone_space(names, [t for t in theory if fm.atoms(t) <= comp])
        if m == 0:
            raise Conflict(f"no possible world satisfies the proofs over {names}")

        # Reliability model (Bovens-Hartmann): a connection is reliable at its base rate;
        # reliability is independent of the fact reported; an unconnected claim sits at its base rate.
        K = CredalSet(m)
        everywhere = np.ones(m, dtype=bool)
        related = {f for _, ids in order for f in ids}
        for a in names:
            kind = st.atoms[a]["kind"]
            if kind == "G":
                K.constrain(env[a], everywhere, st.prior[a])
            elif kind == "H":
                unconnected = everywhere.copy()
                for g, h, _ in links:
                    if h == a:
                        unconnected &= ~env[g]
                K.constrain(env[a], unconnected, st.prior[a])
            elif a not in related:
                K.constrain(env[a], everywhere, st.prior[a])
                for g, _, f in links:
                    if f == a:
                        K.constrain(env[a], env[g], st.prior[a])
        if not K.feasible():
            raise Conflict(f"base rates are incompatible with the verified proofs over {names}")

        # Evidence: virtual evidence on one atom; pieces on the same atom are joined by a copula class.
        blocks = {}
        for e in st.evidence.values():
            t = st.rep(e["target"])
            if t in comp:
                blocks.setdefault((t, e["block"]), []).append(e["likelihood"])
        choices = [
            [np.where(env[t], pt, pf) for pt, pf in joint_likelihood(likes, self.dependence)]
            for (t, _), likes in sorted(blocks.items())
        ]
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
               "propositions": alg.classes("F"),
               "specifications": {c: [alg.preds[p] for p in ps] for c, ps in alg.classes("P").items()},
               "objects": {c: [alg.objs[o] for o in os_] for c, os_ in alg.classes("O").items()}}
        for a, info in st.atoms.items():
            if info["kind"] != "H":
                continue
            try:
                b = self.infer(a)
                entry = {"h": a, "text": info["text"], "lo": b["lo"], "hi": b["hi"]}
            except KernelError as e:
                entry = {"h": a, "text": info["text"], "error": str(e)}
            entry["means"] = []
            for g, h, f in st.links:
                if h == a:
                    p = alg.props[f]
                    entry["means"].append({
                        "g": g, "f": f, "proposition_class": alg.find(f),
                        "specification_class": p["pred"] and alg.find(p["pred"]),
                        "object_class": p["obj"] and alg.find(p["obj"]),
                    })
            out["claims"].append(entry)
        return out
