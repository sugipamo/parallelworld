"""Knowledge kernel: append-only event log + interval inference.

State changes are events of exactly three kinds:
  * model extension   (claim / ground / independence)
  * Bayesian evidence (observe)
  * verified proof    (proof)   -- only ever written after the Lean gate accepts

Inference never stores a joint distribution. It solves linear programs over the
possible worlds of the connected component of the query, so every dependence
that is not stated stays unknown and shows up as interval width.
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
from scipy.optimize import linprog

from . import formula as fm

CATALOG_PATH = os.path.join(os.path.dirname(__file__), "catalog.json")
RELATIONS = {"holds": 1, "not": 1, "iff": 2, "implies": 2, "contradiction": 2}


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
        self.atoms = {}      # id -> {"kind": H|F|G, "text": str}
        self.prior = {}      # H, G, F -> base rate
        self.links = []      # (g, h, f)
        self.evidence = {}   # eid -> dict
        self.proofs = []     # dict
        self._parent = {}    # union-find over F (Lean-proved iff)

    def rep(self, a):
        if a not in self._parent:
            return a
        while self._parent[a] != a:
            self._parent[a] = self._parent[self._parent[a]]
            a = self._parent[a]
        return a

    def union(self, a, b):
        ra, rb = sorted((self.rep(a), self.rep(b)))
        self._parent[rb] = ra  # keep lexicographically smallest as representative

    def apply(self, typ, p):
        if typ == "claim":
            self.atoms[p["h"]] = {"kind": "H", "text": p["text"]}
            self.prior[p["h"]] = p["prior"]
        elif typ == "ground":
            if p["f"] not in self.atoms:
                self.atoms[p["f"]] = {"kind": "F", "text": p["lean"]}
                self._parent[p["f"]] = p["f"]
                self.prior[p["f"]] = self.prior[p["h"]]
            self.atoms[p["g"]] = {"kind": "G", "text": f'{p["h"]} means {p["f"]}'}
            self.prior[p["g"]] = p["prior"]
            self.links.append((p["g"], p["h"], p["f"]))
        elif typ == "observe":
            self.evidence[p["eid"]] = dict(p, block="shared")
        elif typ == "independence":
            self.evidence[p["eid"]]["block"] = p["eid"]
        elif typ == "proof":
            self.proofs.append(p)
            if p["relation"] == "iff":
                self.union(*p["fs"])


class Kernel:
    def __init__(self, db_path, gate=None, catalog=None, actor=None, max_atoms=14):
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
        """Introduce connection hypothesis G: 'H means the Lean proposition F'."""
        lean = _norm(lean)
        if self.gate is not None:
            self.gate.screen(lean)
        f = "F:" + _sha(lean)
        g = f"G:{h[2:]}~{f[2:]}"
        with self._tx() as (con, st):
            if h not in st.atoms:
                raise KernelError(f"unknown claim {h}")
            if g not in st.atoms:
                prior = self.catalog["priors"]["grounding"] if prior is None else prior
                self._append(con, st, "ground", {"g": g, "h": h, "f": f, "lean": lean, "prior": prior})
        return {"g": g, "f": f}

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

    def prove(self, relation, fs, proof):
        """Ask the Lean gate to verify a relation between formal propositions.

        Nothing is recorded unless the gate accepts. A failed attempt is NOT evidence.
        """
        if RELATIONS.get(relation) != len(fs):
            raise KernelError(f"relation must be one of {RELATIONS} with matching arity")
        if self.gate is None:
            raise KernelError("no Lean gate configured; proofs cannot be accepted")
        st = self.state()
        for f in fs:
            if st.atoms.get(f, {}).get("kind") != "F":
                raise KernelError(f"unknown formal proposition {f}")
        verdict = self.gate.check(relation, [st.atoms[f]["text"] for f in fs], proof)
        if not verdict["ok"]:
            return {"accepted": False, "reason": verdict["reason"]}
        with self._tx() as (con, st):
            self._append(con, st, "proof", {
                "relation": relation, "fs": list(fs), "proof_sha": _sha(proof),
                "axioms": verdict["axioms"], "gamma": verdict["gamma"],
            })
        return {"accepted": True, "axioms": verdict["axioms"], "gamma": verdict["gamma"]}

    # ---- inference -------------------------------------------------------
    def infer(self, query):
        """Bounds [lo, hi] on P(query | all evidence), under all verified proofs."""
        st = self.state()
        q = fm.rename(fm.parse(query), st.rep)
        for a in fm.atoms(q):
            if a not in st.atoms:
                raise KernelError(f"unknown atom {a}")

        links = [(g, h, st.rep(f)) for g, h, f in st.links]
        proofs = [(p["relation"], [st.rep(f) for f in p["fs"]]) for p in st.proofs if p["relation"] != "iff"]
        groups = [set(l) for l in links] + [set(fs) for _, fs in proofs]
        comp = set(fm.atoms(q))
        grew = True
        while grew:
            grew = False
            for grp in groups:
                if grp & comp and not grp <= comp:
                    comp |= grp
                    grew = True
        names = sorted(comp)
        n = len(names)
        if n > self.max_atoms:
            raise KernelError(f"component has {n} atoms (> {self.max_atoms}); split the query")
        links = [l for l in links if l[0] in comp]
        proofs = [p for p in proofs if set(p[1]) <= comp]

        bits = (np.arange(2 ** n)[:, None] >> np.arange(n)) & 1
        env = {a: bits[:, i].astype(bool) for i, a in enumerate(names)}
        ok = np.ones(2 ** n, dtype=bool)
        for g, h, f in links:                       # G -> (H <-> F): what a connection means
            ok &= ~env[g] | (env[h] == env[f])
        for rel, fs in proofs:                      # Lean theorems remove impossible worlds
            a = env[fs[0]]
            b = env[fs[-1]]
            ok &= {"holds": a, "not": ~a, "implies": ~a | b, "contradiction": ~(a & b)}[rel]
        if not ok.any():
            raise Conflict(f"no possible world satisfies the proofs over {names}")
        env = {a: v[ok] for a, v in env.items()}
        m = int(ok.sum())
        one = np.ones(m)

        # prior constraints, each as a row r with r . mu = 0
        rows = []
        cond = lambda a, c, p: rows.append((a & c).astype(float) - p * c.astype(float))  # P(a | c) = p
        touched = {f for _, fs in proofs for f in fs}
        for a in names:
            kind = st.atoms[a]["kind"]
            if kind == "G":
                cond(env[a], one.astype(bool), st.prior[a])
            elif kind == "H":
                # where no connection of H holds, H keeps its base rate
                free = np.ones(m, dtype=bool)
                for g, h, _ in links:
                    if h == a:
                        free &= ~env[g]
                cond(env[a], free, st.prior[a])
            elif a not in touched:
                # an F untouched by non-iff proofs keeps a base rate, unrelated to its connections
                cond(env[a], one.astype(bool), st.prior[a])
                for g, _, f in links:
                    if f == a:
                        cond(env[a], env[g], st.prior[a])

        def lp(c, weights):
            A = np.vstack(rows + [weights]) if rows else weights[None, :]
            b = np.zeros(len(A))
            b[-1] = 1.0
            return linprog(c, A_eq=A, b_eq=b, bounds=(0, None), method="highs")

        if lp(np.zeros(m), one).status != 0:
            raise Conflict(f"base rates are incompatible with the verified proofs over {names}")

        # evidence: per target, blocks of evidence with unknown mutual redundancy
        blocks = {}
        for e in st.evidence.values():
            t = st.rep(e["target"])
            if t in comp:
                blocks.setdefault((t, e["block"]), []).append(e["likelihood"])
        choices = []
        for (t, _), likes in sorted(blocks.items()):
            a = np.array(likes)
            indep = (a[:, 0].prod(), a[:, 1].prod())   # no redundancy inside the block
            dup = (a[:, 0].min(), a[:, 1].min())       # fully redundant
            opts = {indep, dup}
            choices.append([np.where(env[t], pt, pf) for pt, pf in opts])

        qv = np.asarray(fm.evaluate(q, env), dtype=float) * one
        lo, hi = 1.0, 0.0
        for combo in itertools.product(*choices):
            L = one.copy()
            for w in combo:
                L = L * w
            r1, r2 = lp(L * qv, L), lp(-L * qv, L)
            if r1.status != 0 or r2.status != 0:
                raise Conflict(f"the recorded evidence has probability zero over {names}")
            lo, hi = min(lo, r1.fun), max(hi, -r2.fun)
        lo, hi = max(0.0, round(lo, 9)), min(1.0, round(hi, 9))
        return {"lo": lo, "hi": hi, "atoms": names, "worlds": m}

    def status(self):
        st = self.state()
        out = {"claims": [], "classes": {}, "proofs": st.proofs, "evidence": len(st.evidence)}
        for a, info in st.atoms.items():
            if info["kind"] == "H":
                try:
                    b = self.infer(a)
                    entry = {"h": a, "text": info["text"], "lo": b["lo"], "hi": b["hi"]}
                except KernelError as e:
                    entry = {"h": a, "text": info["text"], "error": str(e)}
                entry["groundings"] = [{"g": g, "f": f, "class": st.rep(f)} for g, h, f in st.links if h == a]
                out["claims"].append(entry)
            elif info["kind"] == "F":
                out["classes"].setdefault(st.rep(a), []).append({"f": a, "lean": info["text"]})
        return out
