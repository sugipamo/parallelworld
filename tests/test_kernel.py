import pytest

from pw import formula as fm
from pw.kernel import Conflict, Kernel, KernelError
from pw.lean_gate import GateError, LeanGate


class FakeGate(LeanGate):
    """Accepts every proof. Stands in for Lean so kernel semantics can be tested alone."""
    def check(self, relation, props, proof):
        self.render(relation, props, proof)
        return {"ok": True, "axioms": [], "gamma": "fake"}


@pytest.fixture
def k(tmp_path):
    return Kernel(str(tmp_path / "e.db"), gate=FakeGate())


def approx(b, lo, hi):
    assert b["lo"] == pytest.approx(lo, abs=1e-6) and b["hi"] == pytest.approx(hi, abs=1e-6), b


def test_formula():
    e = fm.parse("!a & (b | c) -> d <-> e")
    assert fm.atoms(e) == set("abcde")
    assert fm.evaluate(fm.parse("a -> b"), {"a": True, "b": False}) == False


def test_spec_section6_lower_bound(k):
    h1, h2 = k.claim("sort is stable")["h"], k.claim("equal keys keep input order")["h"]
    g1 = k.ground(h1, "∀ n : Nat, n + 0 = n", prior=0.9)
    g2 = k.ground(h2, "∀ n : Nat, 0 + n = n", prior=0.8)
    approx(k.infer(f"{h1} <-> {h2}"), 0.0, 1.0)          # nothing links them yet
    assert k.prove("iff", [g1["f"], g2["f"]], "simp")["accepted"]
    approx(k.infer(f"{g1['g']} & {g2['g']}"), 0.7, 0.8)   # Frechet, no independence assumed
    approx(k.infer(f"{h1} <-> {h2}"), 0.7, 1.0)
    approx(k.infer(h1), 0.5, 0.5)                         # the proof alone says nothing about truth


def test_exact_bayes_and_dedup(k):
    h = k.claim("parser rejects empty input")["h"]
    approx(k.infer(h), 0.5, 0.5)
    e = k.observe(h, "property_test", "pass", "run-1")
    assert not e["duplicate"]
    approx(k.infer(h), 0.9 / 1.05, 0.9 / 1.05)
    assert k.observe(h, "property_test", "pass", "run-1")["duplicate"]   # second agent, same run
    approx(k.infer(h), 0.9 / 1.05, 0.9 / 1.05)
    with pytest.raises(KernelError):
        k.observe(h, "property_test", "fail", "run-1")


def test_dependent_evidence_is_an_interval_until_independence_is_declared(k):
    h = k.claim("cache never returns stale data")["h"]
    k.observe(h, "property_test", "pass", "run-1")
    e2 = k.observe(h, "property_test", "pass", "run-2")
    single, both = 0.9 / 1.05, 0.81 / (0.81 + 0.0225)
    approx(k.infer(h), single, both)      # anywhere between "same evidence twice" and "two pieces"
    k.declare_independent(e2["eid"], "different generator seed and different machine")
    approx(k.infer(h), both, both)


def test_proof_does_not_make_a_claim_certain(k):
    h = k.claim("id is idempotent")["h"]
    g = k.ground(h, "∀ n : Nat, n = n", prior=0.9)
    assert k.prove("holds", [g["f"]], "intro n; rfl")["accepted"]
    approx(k.infer(h), 0.95, 0.95)        # 0.9 (connection right) + 0.1 * 0.5 (base rate)
    approx(k.infer(g["g"]), 0.9, 0.9)     # condition 3: proof leaves the connection uncertain
    k.observe(g["g"], "instance_check", "agree", "inst-1")
    assert k.infer(h)["lo"] > 0.95


def test_evidence_flows_through_proved_equivalence(k):
    h1, h2 = k.claim("A")["h"], k.claim("B")["h"]
    g1, g2 = k.ground(h1, "(1:Nat) = 1", prior=0.9), k.ground(h2, "(2:Nat) = 2", prior=0.9)
    k.observe(h1, "property_test", "pass", "run-1")
    approx(k.infer(h2), 0.5, 0.5)
    k.prove("iff", [g1["f"], g2["f"]], "simp")
    assert k.infer(h2)["lo"] > 0.6


def test_contradictory_formalizations_surface_as_conflict(k):
    h = k.claim("limit is inclusive")["h"]
    g1, g2 = k.ground(h, "(1:Nat) ≤ 1", prior=0.9), k.ground(h, "(1:Nat) < 1", prior=0.8)
    k.prove("holds", [g1["f"]], "decide")
    k.prove("not", [g2["f"]], "decide")
    with pytest.raises(Conflict):
        k.infer(h)


def test_gate_is_the_only_way_in(tmp_path):
    k = Kernel(str(tmp_path / "e.db"))
    h = k.claim("x")["h"]
    f = k.ground(h, "True")["f"]
    with pytest.raises(KernelError):
        k.prove("holds", [f], "trivial")


def test_gate_screening_and_axiom_judgement():
    gate = LeanGate()
    for bad in ("sorry", "exact foo\naxiom cheat : False", "simp\n#eval 1", "native_decide"):
        with pytest.raises(GateError):
            gate.render("holds", ["True"], bad)
    src = gate.render("iff", ["1 = 1", "2 = 2"], "simp")
    assert "theorem pw_goal : _root_.Iff PWStmt.S0 PWStmt.S1" in src and src.endswith("#print axioms pw_goal\n")
    assert LeanGate.judge(0, "'pw_goal' depends on axioms: [propext, Quot.sound]", "g")["ok"]
    assert LeanGate.judge(0, "'pw_goal' does not depend on any axioms", "g")["axioms"] == []
    assert not LeanGate.judge(0, "'pw_goal' depends on axioms: [sorryAx]", "g")["ok"]
    assert not LeanGate.judge(1, "error: unsolved goals", "g")["ok"]
    assert not LeanGate.judge(0, "", "g")["ok"]
