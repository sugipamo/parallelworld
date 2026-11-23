import pytest

from pw import formula as fm
from pw.kernel import Conflict, Kernel, KernelError
from pw.lean_gate import GateError, LeanGate


class FakeGate(LeanGate):
    """Accepts every proof. Stands in for Lean so kernel semantics can be tested alone."""
    def check(self, relation, items, proof):
        self.render(relation, items, proof)
        return {"ok": True, "axioms": [], "gamma": "fake"}

    def typecheck(self, items):
        return {"ok": True, "reason": ""}


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
    both = 0.81 / (0.81 + 0.0225)
    approx(k.infer(h), 0.81 / (0.81 + 0.15), 0.9 / (0.9 + 0.0225))   # every positively dependent copula
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


def test_equivalence_of_two_theorems_carries_no_information(k):
    """Found in the first real two-worker run: both F were proved, then proved equivalent.
    Any two theorems are equivalent, so the bounds must not move."""
    h1, h2 = k.claim("A")["h"], k.claim("B")["h"]
    g1, g2 = k.ground(h1, "(1:Nat) = 1"), k.ground(h2, "(2:Nat) = 2")
    for h, g in ((h1, g1), (h2, g2)):
        k.observe(h, "test", "pass", f"run-{h}")
        k.prove("holds", [g["f"]], "rfl")
    before = k.infer(h1)
    approx(before, 0.76 / 0.84, 0.76 / 0.84)
    k.prove("iff", [g1["f"], g2["f"]], "simp")
    assert k.infer(h1) == before
    joint = k.infer(f"{g1['g']} & {g2['g']}")             # asked jointly, dependence is still unknown
    assert joint["lo"] < joint["hi"]


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
            gate.render("holds", [("Prop", "True")], bad)
    # a string is data: the name of a tool is not a command. But nothing may pose as a string.
    gate.render("holds", [("Prop", 'x = ["declare_independent", "open", "theorem"]')], "rfl")
    for bad in ('"a\\" axiom cheat : False "', "'\"' axiom cheat : False '\"'", '"unterminated axiom cheat : False'):
        with pytest.raises(GateError):
            gate.render("holds", [("Prop", bad)], "rfl")
    src = gate.render("iff", [("Prop", "1 = 1"), ("Prop", "2 = 2")], "simp")
    assert "theorem pw_goal : _root_.Iff PWStmt.S0 PWStmt.S1" in src and "#print" not in src
    assert LeanGate.judge(0, "'pw_goal' depends on axioms: [propext, Quot.sound]", "g")["ok"]
    assert LeanGate.judge(0, "'pw_goal' does not depend on any axioms", "g")["axioms"] == []
    assert not LeanGate.judge(0, "'pw_goal' depends on axioms: [sorryAx]", "g")["ok"]
    assert not LeanGate.judge(1, "error: unsolved goals", "g")["ok"]
    forged = "'pw_goal' does not depend on any axioms\n'pw_goal' depends on axioms: [sorryAx]"
    assert not LeanGate.judge(0, forged, "g")["ok"]
    assert not LeanGate.judge(0, "", "g")["ok"]


def test_identity_is_a_metric_and_section6_is_the_triangle_inequality(k):
    """d(A, B) = 1 - P(A <-> B). Lean gives d(F1, F2) = 0; a connection gives d(H, F) <= 1 - P(G)."""
    h1, h2 = k.claim("A")["h"], k.claim("B")["h"]
    g1, g2 = k.ground(h1, "(1:Nat) = 1 ∨ False", prior=0.9), k.ground(h2, "(1:Nat) = 1 ∧ True", prior=0.8)
    k.prove("iff", [g1["f"], g2["f"]], "simp")
    k.observe(h1, "property_test", "pass", "r1")
    k.observe(g2["g"], "back_translation", "mismatch", "b1")
    d = lambda a, b: 1 - k.infer(f"{a} <-> {b}")["lo"]          # upper distance
    assert d(g1["f"], g2["f"]) == pytest.approx(0, abs=1e-9)
    for h, g in ((h1, g1), (h2, g2)):
        assert d(h, g["f"]) <= 1 - k.infer(g["g"])["lo"] + 1e-9
    assert d(h1, h2) <= d(h1, g1["f"]) + d(g2["f"], h2) + 1e-9


T = "Nat → Nat"


def test_same_specification_and_same_object_are_separate_identities(k):
    h1, h2 = k.claim("f never decreases its input")["h"], k.claim("g returns at least its argument")["h"]
    a = k.ground_at(h1, "f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1", prior=0.9, model_prior=1)
    b = k.ground_at(h2, "g", T, "fun f => ∀ n, f n ≥ n", "fun n => 1 + n", prior=0.8, model_prior=1)
    alg = lambda: k.state().algebra
    assert alg().find(a["f"]) != alg().find(b["f"])

    k.prove("pred_iff", [a["p"], b["p"]], "intro f; exact Iff.rfl")      # same specification
    assert alg().find(a["p"]) == alg().find(b["p"])
    assert alg().find(a["f"]) != alg().find(b["f"])                      # ...of different objects
    approx(k.infer(f"{h1} <-> {h2}"), 0.0, 1.0)

    k.prove("obj_eq", [a["o"], b["o"]], "funext n; omega")               # same object
    assert alg().find(a["f"]) == alg().find(b["f"])                      # congruence: P(a) = P'(a')
    approx(k.infer(f"{h1} <-> {h2}"), 0.7, 1.0)
    approx(k.distance(h1, h2), 0.0, 0.3)
    s = k.status()
    assert len(s["specifications"]) == 1 and len(s["objects"]) == 1 and len(s["propositions"]) == 1


def test_refinement_between_specifications_orders_their_instances(k):
    h1, h2 = k.claim("f is strictly above its input")["h"], k.claim("f is at least its input")["h"]
    a = k.ground_at(h1, "f", T, "fun f => ∀ n, n < f n", "fun n => n + 1", prior=0.9)
    b = k.ground_at(h2, "f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1", prior=0.9)
    k.prove("pred_implies", [a["p"], b["p"]], "intro f h n; exact Nat.le_of_lt (h n)")
    approx(k.infer(f"{a['f']} -> {b['f']}"), 1.0, 1.0)
    before = k.infer(h2)["lo"]
    k.prove("holds", [a["f"]], "intro n; omega")
    assert k.infer(h2)["lo"] > before          # the stronger instance is a theorem, so the weaker one is true
    with pytest.raises(KernelError):
        k.prove("pred_iff", [a["f"], b["f"]], "x")   # wrong kind of id


@pytest.mark.parametrize("dependence,lo,hi", [
    ("independent", 0.81 / 0.8325, 0.81 / 0.8325),
    ("comonotone", 0.9 / 1.05, 0.9 / 1.05),
    ("pqd", 0.81 / 0.96, 0.9 / 0.9225),
    ("frechet", 0.8 / 0.95, 1.0),
])
def test_copula_classes(tmp_path, dependence, lo, hi):
    k = Kernel(str(tmp_path / "e.db"), dependence=dependence)
    h = k.claim("x")["h"]
    k.observe(h, "property_test", "pass", "r1")
    k.observe(h, "property_test", "pass", "r2")
    approx(k.infer(h), lo, hi)


def test_model_hypothesis_is_shared_by_claims_about_the_same_code(k):
    """'This term models that code' is one hypothesis, however many claims lean on it."""
    h1, h2 = k.claim("f is at least its input")["h"], k.claim("f is positive")["h"]
    a = k.ground_at(h1, "f.py::f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1")
    b = k.ground_at(h2, "f.py::f", T, "fun f => ∀ n, 0 < f n", "fun n => n + 1")
    assert a["m"] == b["m"] and a["g"] != b["g"]
    other = k.ground_at(k.claim("g is positive")["h"], "g.py::g", T, "fun f => ∀ n, 0 < f n", "fun n => n + 1")
    assert other["m"] != a["m"] and other["p"] == b["p"] and other["o"] == b["o"]

    for x in (a, b):
        k.prove("holds", [x["f"]], "intro n; omega")
    # specification 0.8 and model 0.75 with unknown dependence: both hold with probability in [0.55, 0.75]
    approx(k.infer(f"{a['g']} & {a['m']}"), 0.55, 0.75)
    approx(k.infer(h1), 0.55 + 0.45 * 0.5, 0.75 + 0.25 * 0.5)
    before = k.infer(h1)["lo"], k.infer(h2)["lo"]
    k.observe(a["m"], "instance_check", "agree", "input-3")      # one check of the model...
    assert k.infer(h1)["lo"] > before[0] and k.infer(h2)["lo"] > before[1]   # ...supports both claims
    assert k.status()["models"][a["m"]]["subject"] == "f.py::f"
    with pytest.raises(KernelError):
        k.observe(a["m"], "test", "pass", "r")                   # tests are evidence about claims, not models


def _model(k):
    h = k.claim("f is at least its input")["h"]
    g = k.ground_at(h, "f.py::f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1")
    return h, g["m"]


def test_chosen_checks_never_lower_the_bound_and_one_counterexample_refutes(k):
    """A model hypothesis is universal: if it holds, every instance agrees."""
    h, m = _model(k)
    approx(k.infer(m), 0.75, 0.75)
    k.observe(m, "instance_check", "agree", "in-1")
    one = k.infer(m)
    assert one["lo"] == pytest.approx(0.75 / (0.75 + 0.25 * 0.35))
    for i in range(2, 6):
        k.observe(m, "instance_check", "agree", f"in-{i}")
    five = k.infer(m)
    assert five["lo"] == pytest.approx(one["lo"]) and five["hi"] > one["hi"]   # hand-picked: no further support
    bad = k.observe(m, "instance_check", "disagree", "in-6")
    approx(k.infer(m), 0.0, 0.0)
    approx(k.infer(h), 0.5, 0.5)            # the claim is back at its base rate
    k.retract(bad["eid"], "the command printed a float where Lean prints a Nat")
    assert k.infer(m)["lo"] == pytest.approx(one["lo"])
    with pytest.raises(KernelError):
        k.observe(m, "instance_check", "disagree", "in-6")


def test_random_checks_raise_the_lower_bound(k):
    """Exchangeable draws: with the uniform prior as the least concentrated one, k agreements
    leave at most 1 / (k + 1) for a wrong model (Laplace's rule of succession)."""
    from pw.credal import exchangeable_agreement
    for n in (1, 5, 20):
        lo, hi = exchangeable_agreement(n, 0.5, 2)
        assert lo == pytest.approx(0.5 ** n) and hi == pytest.approx(1 / (n + 1))
    assert exchangeable_agreement(5, 0.35, 1e-9)[1] == pytest.approx(0.35, abs=1e-6)   # no bound: no learning

    h, m = _model(k)
    spec = k.catalog["sampling"]
    lows = []
    for i in range(20):
        k._record(m, "sampled_check", "agree", f"draw-{i}", {"args": [i], **spec})
        if i + 1 in (1, 5, 20):
            lows.append(k.infer(m)["lo"])
    assert lows == pytest.approx([0.75 * n1 / (0.75 * n1 + 0.25) for n1 in (2, 6, 21)])   # 0.857, 0.947, 0.984
    k._record(m, "sampled_check", "disagree", "draw-x", {"args": [99], **spec})
    approx(k.infer(m), 0.0, 0.0)


def test_formal_claim_has_no_specification_hypothesis(k):
    """Stated as a predicate, a claim needs no translation: only the model link is uncertain."""
    c = k.claim_formal("f.py::f", T, "fun f => ∀ n, n ≤ f n", gloss="f never decreases its input")
    assert k.claim_formal("f.py::f", T, "fun f => ∀ n, n ≤ f n")["h"] == c["h"]
    approx(k.infer(c["h"]), 0.5, 0.5)
    with pytest.raises(KernelError):
        k.ground_at(c["h"], "f.py::f", T, "fun f => True", "fun n => n")     # its meaning is fixed
    a = k.attach_model(c["h"], "fun n => n + 1", subject_version="f.py::f@abc")
    assert a["p"] == c["p"]
    st = k.state()
    assert [x for x in st.atoms if x[0] == "G"] == [] and st.links == [((a["m"],), c["h"], a["f"])]
    k.prove("holds", [a["f"]], "intro n; omega")
    approx(k.infer(c["h"]), 0.75 + 0.25 * 0.5, 0.75 + 0.25 * 0.5)            # a point: nothing else is unknown
    for i in range(20):
        k._record(a["m"], "sampled_check", "agree", f"d{i}", {"args": [i], **k.catalog["sampling"]})
    m = 0.75 * 21 / (0.75 * 21 + 0.25)
    assert k.infer(c["h"])["lo"] == pytest.approx(m + (1 - m) * 0.5)         # the claim follows the model
    assert k.status()["claims"][0]["formal"]


def test_specification_that_excludes_something_is_better_supported(k):
    h = k.claim("f never decreases its input")["h"]
    g = k.ground_at(h, "f.py::f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1")
    approx(k.infer(g["g"]), 0.8, 0.8)
    r = k.reject_object(g["p"], "fun n => 0", "intro h; exact absurd (h 1) (by decide)")
    assert r["accepted"] and k.state().algebra.nonvacuous() == {g["p"]}
    assert [e["type"] for e in k.events()][-2:] == ["object", "proof"]
    approx(k.infer(g["g"]), 0.8 / (0.8 + 0.2 * 0.7), 0.8 / (0.8 + 0.2 * 0.7))
    k.reject_object(g["p"], "fun n => n - 1", "x")                            # a second counterexample adds nothing
    approx(k.infer(g["g"]), 0.8 / (0.8 + 0.2 * 0.7), 0.8 / (0.8 + 0.2 * 0.7))
    # the rejected object, used as a model elsewhere, makes that proposition false
    other = k.ground_at(k.claim("z never decreases its input")["h"], "z.py::z", T, "fun f => ∀ n, n ≤ f n", "fun n => 0")
    approx(k.infer(other["f"]), 0.0, 0.0)


def test_two_authors_reaching_the_same_specification_support_it(tmp_path):
    def worker(name):
        return Kernel(str(tmp_path / "e.db"), gate=FakeGate(), actor=name)
    a, b = worker("a"), worker("b")
    h = a.claim("f never decreases its input")["h"]
    ga = a.ground_at(h, "f.py::f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1")
    approx(a.infer(ga["g"]), 0.8, 0.8)
    a.ground_at(h, "f.py::f", T, "fun f => ∀ n, n ≤ f n", "fun n => n + 1")           # same author again: nothing
    approx(a.infer(ga["g"]), 0.8, 0.8)
    gb = b.ground_at(h, "f.py::f", T, "fun f => ∀ n, f n ≥ n", "fun n => n + 1")       # different text
    approx(a.infer(ga["g"]), 0.8, 0.8)                                               # not yet known to agree
    b.prove("pred_iff", [ga["p"], gb["p"]], "intro f; exact Iff.rfl")
    assert a.infer(ga["g"])["lo"] > 0.8 and a.infer(gb["g"])["lo"] > 0.8


def test_outputs_are_compared_by_value_not_by_spelling():
    from pw.kernel import _values
    assert _values("(Fraction(1, 6), 0.0, 1)") == _values("(1/6, 0, 1)")
    assert _values("[0.75, True]") == _values("[3/4, true]")
    assert _values("0.30000000000000004") != _values("3/10")     # a float that is not the exact value
    assert _values("5") != _values("6") and _values("-2") == _values("-2.0")


def test_a_proposed_decision_that_contradicts_an_established_one_does_not_block_the_rest(k):
    """Found in the first decisions run: one unsupported, contradictory proposal made every
    claim about the same code impossible to evaluate."""
    old = k.claim_formal("f.py::f", T, "fun f => ∀ n, n ≤ f n")
    a = k.attach_model(old["h"], "fun n => n + 1", subject_version="f.py::f@v1")
    k.prove("holds", [a["f"]], "x")
    for i in range(20):
        k._record(a["m"], "sampled_check", "agree", f"d{i}", {"args": [i], **k.catalog["sampling"]})
    third = k.claim_formal("f.py::f", T, "fun f => ∀ n, 0 < f n")
    b = k.attach_model(third["h"], "fun n => n + 1", subject_version="f.py::f@v1")
    k.prove("holds", [b["f"]], "x")
    before = k.infer(old["h"])["lo"], k.infer(third["h"])["lo"]

    new = k.claim_formal("f.py::f", T, "fun f => ∀ n, f n < n")      # proposed, nothing attached
    k.prove("pred_disjoint", [old["p"], new["p"]], "x")
    # the established decision and the bystander stand; they give up only the little room in
    # which their model is wrong and the proposal could then be right
    assert k.infer(old["h"])["lo"] == pytest.approx(before[0], abs=0.01)
    assert k.infer(third["h"])["lo"] == pytest.approx(before[1], abs=0.01)
    assert k.infer(new["h"])["hi"] < 0.02                                    # the proposal is all but excluded
    approx(k.infer(f"{old['h']} & {new['h']}"), 0.0, 0.0)


def test_what_a_formalization_leaves_out_is_kept_with_it(k):
    h = k.claim("the bound never exceeds the product of the probabilities")["h"]
    k.ground(h, "∀ p q : Nat, p * q ≤ p * q", left_out="only two probabilities; the sentence has no count",
             added="probabilities read as naturals")
    means = k.status()["claims"][0]["means"][0]
    assert means["left_out"].startswith("only two") and means["added"] == "probabilities read as naturals"
    approx(k.infer(h), 0.5, 0.5)          # the notes are for a reader; they move no number


def test_a_subject_is_a_file_or_a_part_of_one(tmp_path):
    """A reading is tied to the content it is about, not to the rest of the file."""
    from pw.kernel import locate, subject_id
    cwd = str(tmp_path)
    md = "# Title\n\nintro\n\n## Rules\n\n- one\n\n```\n# not a heading\n```\n\n### Detail\n\nmore\n\n## Other\n\ntext\n"
    (tmp_path / "doc.md").write_text(md)
    assert locate("doc.md::Rules", cwd).decode() == "## Rules\n\n- one\n\n```\n# not a heading\n```\n\n### Detail\n\nmore\n\n"
    before = subject_id("doc.md::Rules", cwd)
    (tmp_path / "doc.md").write_text(md.replace("text", "changed elsewhere"))
    assert subject_id("doc.md::Rules", cwd) == before != subject_id("doc.md::Other", cwd)
    (tmp_path / "doc.md").write_text(md.replace("- one", "- two"))
    assert subject_id("doc.md::Rules", cwd) != before

    (tmp_path / "c.json").write_text('{"a": {"x": [1, 2]}, "b": 3}')
    v = subject_id("c.json::a.x", cwd)
    (tmp_path / "c.json").write_text('{"b": 4,   "a": {"x": [1, 2]}}')            # other key, order, spacing
    assert subject_id("c.json::a.x", cwd) == v and locate("c.json::a.x.1", cwd) == b"2"

    py = "LIMIT = 3\n\nclass K:\n    def f(self, n):\n        return n + LIMIT\n\ndef g():\n    return 1\n"
    (tmp_path / "m.py").write_text(py)
    f, lim = subject_id("m.py::K.f", cwd), subject_id("m.py::LIMIT", cwd)
    (tmp_path / "m.py").write_text(py.replace("return 1", "return 2").replace("LIMIT = 3", "LIMIT = 4"))
    assert subject_id("m.py::K.f", cwd) == f and subject_id("m.py::LIMIT", cwd) != lim

    (tmp_path / "blob.bin").write_bytes(b"\x00\xff\x10")                         # any file at all
    assert subject_id("blob.bin", cwd).startswith("blob.bin@") and subject_id("blob.bin::x", cwd).startswith("blob.bin::x@")
    assert subject_id("doc.md::No such heading", cwd) == "doc.md::No such heading@" + subject_id("doc.md", cwd).split("@")[1]
    assert subject_id("missing.txt::a", cwd) == "missing.txt::a"


def test_a_place_is_read_by_a_description_not_by_code():
    from pw.kernel import _read_pattern, pattern
    text = 'def __init__(self, max_atoms=14, dependence="pqd"):\nALLOWED = {"propext", "Quot.sound", "propext", "Classical.choice"}\nthreshold 0.9 and -3\n'
    assert _read_pattern(pattern(find=r'dependence="(\w+)"'), text) == '"pqd"'
    assert _read_pattern(pattern(find=r"max_atoms=(\d+)", kind="nat"), text) == "14"
    assert _read_pattern(pattern(find=r"threshold ([0-9.]+)", kind="permille"), text) == "900"
    assert _read_pattern(pattern(find=r"and (-?\d+)", kind="int"), text) == "(-3)"
    names = r'"([^"]+)"'
    part = text.splitlines()[1]
    assert _read_pattern(pattern(find_all=names), part) == '["propext", "Quot.sound", "propext", "Classical.choice"]'
    assert _read_pattern(pattern(find_all=names, sort=True, unique=True), part) == '["Classical.choice", "Quot.sound", "propext"]'
    assert _read_pattern(pattern(find_all=r"(\d+)", kind="nat", sort=True), "9 10 2") == "[2, 9, 10]"       # by size, not as text
    assert _read_pattern(pattern(find_all=r"zzz(\d)", kind="nat"), text) == "[]"
    assert _read_pattern(pattern(find=r"^ALLOWED = (.)"), text) == '"{"'                                    # ^ is a line start
    for found, why in ((r'"(\w+)"', "matches 3 times"), (r"nothing (here)", "matches 0 times")):
        with pytest.raises(KernelError, match=why):
            _read_pattern(pattern(find=found), text)
    with pytest.raises(KernelError):
        _read_pattern(pattern(find=r"threshold ([0-9.]+)", kind="nat"), text)                               # 0.9 is not a natural number
    with pytest.raises(KernelError):
        _read_pattern(pattern(find=r"(0\.[0-9]+)", kind="permille"), "0.9005")                              # not a whole number of thousandths
    for bad in (dict(find="no group"), dict(find="(a)(b)"), dict(find="(a)", find_all="(b)"), dict(), dict(find="(a)", kind="float"),
                dict(find=r"(?<=x)(a)"), dict(find=r"(a)\1"), dict(find=r"(?P<n>a)"), dict(find="(a")):
        with pytest.raises(KernelError):
            pattern(**bad)


def test_planted_changes_have_known_answers():
    import random
    from pw.calibrate import interval, mutants, same
    rng = random.Random(0)
    text = "## Model\n\nThe default class is `pqd`; `pqd` is positive dependence. Not `pqdx`.\nAt most 14 atoms, range 0-15, 114 in total.\n"
    made = mutants(text, "pqd", rng, 3)
    assert len(made) == 3 and all(k == "value replaced" for k, _, _ in made)
    for _, changed, planted in made:
        assert planted != "pqd" and changed.count(f"`{planted}`") == 2 and "`pqdx`" in changed and "`pqd`" not in changed
    (_, changed, planted), = mutants(text, 14, rng, 1)
    assert planted != 14 and f"At most {planted} atoms" in changed and "114 in total" in changed and "0-15" in changed
    assert mutants(text, "frechet", rng, 3) == []                                   # not in the words: cannot be planted

    table = "| `claim(text)` | registers |\n| `prove(r)` | proves |\n| `claim_formal` | other |\n| `status()` | shows |\n"
    made = mutants(table, ["claim", "prove", "status"], random.Random(1), 3)
    assert {k for k, _, _ in made} == {"entry renamed", "row removed"}
    for kind, changed, planted in made:
        assert len(planted) == (2 if kind == "row removed" else 3) and "claim_formal" in changed
        for e in planted:
            assert f"`{e}" in changed                                               # every planted entry is in the changed text
    (_, changed, planted), = mutants("`blind` and `read blind` and `computed`", ["blind", "computed", "read blind"], random.Random(3), 1)
    assert all(f"`{e}`" in changed for e in planted) and len(planted) == 3          # an entry inside another entry changes with it
    assert same(["b", "a"], ["a", "b"]) and not same(["a"], ["a", "b"]) and same(14, 14) and not same("14", 14)
    lo, hi = interval(30, 30)
    assert 0.88 < lo < 0.89 and hi == 1.0                                           # thirty out of thirty: at least 0.88
    lo, hi = interval(0, 30)
    assert lo == 0.0 and 0.11 < hi < 0.12


def test_a_proposed_place_is_checked_against_the_file(tmp_path):
    import json
    from pw.discover import Refused, _agree, merge, screen
    repo = str(tmp_path)
    (tmp_path / "guide.md").write_text("# Guide\n\n## Limits\n\nAt most 14 atoms are solved. The class is `fast`.\n\n## Other\n\nNothing.\n")
    (tmp_path / "app.py").write_text('LIMIT = 14\n\ndef run(threshold=0.9, mode="fast"):\n    return threshold\n\nNAMES = ["b", "a"]\n')
    (tmp_path / "pw-log.jsonl").write_text("{}\n")

    def refused(*a, **kw):
        with pytest.raises(Refused) as e:
            screen(repo, *a, **kw)
        return str(e.value)

    p = screen(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms are solved.")
    assert p == {"at": "guide.md::Limits", "read": None, "value": 14, "quote": "At most 14 atoms are solved."}
    assert screen(repo, "Nat", "guide.md::Limits", "14", "At most 14 atoms are solved.")["value"] == 14      # JSON text is accepted too
    assert "word for word" in refused("Nat", "guide.md::Limits", 14, "At most 14 atoms can be solved.")
    assert "word for word" in refused("Nat", "guide.md::Other", 14, "At most 14 atoms are solved.")          # the quote is in another part
    assert "does not occur in the quote" in refused("Nat", "guide.md::Limits", 15, "At most 14 atoms are solved.")
    assert "no heading" in refused("Nat", "guide.md::Limit", 14, "At most 14 atoms are solved.")
    assert "no file" in refused("Nat", "missing.md", 14, "x")
    assert "not a value of type Nat" in refused("Nat", "guide.md::Limits", '"14"', "At most 14 atoms are solved.")
    for own in ("pw-log.jsonl", "../guide.md", ".git/config"):
        assert "not a file of the project" in refused("Nat", own, 14, "x")

    p = screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert p["read"] == {"find": r"LIMIT = (\d+)", "as": "nat"}
    p = screen(repo, "Nat", "app.py::run", 900, "def run(threshold=0.9", find=r"threshold=([0-9.]+)", kind="permille")
    assert p["read"]["as"] == "permille"                                             # a computed value need not be in the quote
    assert "needs a pattern" in refused("Nat", "app.py::run", 900, "def run(threshold=0.9")
    assert "not the value you gave" in refused("Nat", "app.py::LIMIT", 15, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert "does not work" in refused("Nat", "app.py", 14, "LIMIT = 14", find=r"(\d+)")                      # matches more than once
    p = screen(repo, "List String", "app.py::NAMES", ["a", "b"], 'NAMES = ["b", "a"]', find_all=r'"(\w)"')
    assert p["read"] == {"find_all": r'"(\w)"', "as": "string", "sort": True}
    (tmp_path / "notes.txt").write_text("14\n")
    assert "only Markdown, JSON and Python" in refused("Nat", "notes.txt::x", 14, "14")

    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits"]}]
    merged, added = merge(facts, [
        {"fact": "limit", "place": screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"LIMIT = (\d+)")},
        {"fact": "limit", "place": screen(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms are solved.")},     # already listed
        {"new": {"name": "class", "type": "String", "gloss": "the class"}, "places": [
            screen(repo, "String", "guide.md::Limits", "fast", "The class is `fast`."),
            screen(repo, "String", "app.py::run", "fast", 'mode="fast"', find=r'mode="(\w+)"')]}])
    assert facts[0]["places"] == ["guide.md::Limits"]                                # the input is left alone
    assert merged[0]["places"] == ["guide.md::Limits", {"at": "app.py::LIMIT", "read": {"find": r"LIMIT = (\d+)", "as": "nat"}}]
    assert merged[1] == {"name": "class", "type": "String", "gloss": "the class",
                         "places": ["guide.md::Limits", {"at": "app.py::run", "read": {"find": r'mode="(\w+)"', "as": "string"}}]}
    assert len(added) == 3 and _agree([p for _, p in added[1:]]) and not _agree([{"value": 1}, {"value": 2}])
    k = Kernel(str(tmp_path / "e.db"), gate=FakeGate())
    (tmp_path / "facts.json").write_text(json.dumps(merged))
    assert len(k.sync_facts(str(tmp_path / "facts.json"))) == 2                      # what is merged is a valid declaration


def test_a_search_that_failed_does_not_look_like_one_that_found_nothing(tmp_path, monkeypatch):
    import json
    from pw import discover
    (tmp_path / "guide.md").write_text("## Limits\n\nAt most 14 atoms are solved.\n")
    (tmp_path / "app.py").write_text("LIMIT = 14\n")
    (tmp_path / "other.py").write_text("LIMIT = 14\n")
    repo = str(tmp_path)
    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits", "app.py::LIMIT"]}]
    place = lambda at: {"fact": "limit", "place": {"at": at, "read": None, "value": 14, "quote": "LIMIT = 14"}}

    def agent(lines, result):
        """Stand in for the agent: what its tools wrote, and how the session ended."""
        def run(cmd, **kw):
            with open(cmd[cmd.index("--mcp-config") + 1]) as fh:
                env = json.load(fh)["mcpServers"]["find"]["env"]
            with open(env["PW_DISCOVER_OUT"], "w") as fh:
                fh.writelines(json.dumps(x) + "\n" for x in lines)
            return type("R", (), {"stdout": json.dumps(result) if result is not None else "boom", "stderr": ""})()
        monkeypatch.setattr(discover.subprocess, "run", run)

    ok = {"num_turns": 3, "total_cost_usd": 0.1, "result": "found nothing", "subtype": "success", "is_error": False}
    agent([], ok)                                                    # the tools never came up: the agent only talked
    proposals, run = discover.further(repo, "m", facts, 1.0)
    assert proposals == [] and "never started" in run["problems"][0] and "did not say it finished" in run["problems"][1]
    agent([{"started": True}], ok)                                   # tools up, but the agent never said it was done
    assert discover.further(repo, "m", facts, 1.0)[1]["problems"] == ["the agent did not say it finished searching for: limit"]
    agent([{"started": True}, {"finished": "limit"}], {**ok, "subtype": "error_max_budget_usd", "is_error": True})
    assert discover.further(repo, "m", facts, 1.0)[1]["problems"] == ["the session ended with error_max_budget_usd"]
    agent([{"started": True}, {"finished": "limit"}], None)
    assert "gave no result" in discover.further(repo, "m", facts, 1.0)[1]["problems"][0]
    agent([{"started": True}, {"finished": ""}], ok)
    assert discover.new(repo, "m", facts, 1.0)[1]["problems"] == []
    agent([{"started": True}, {"finished": "limit"}], ok)            # only now does nothing mean nothing
    proposals, run = discover.further(repo, "m", facts, 1.0)
    assert proposals == [] and run["problems"] == [] and run["controls"] == {}

    # a known place left out as a control: coming back with it shows the search works, and is not a proposal
    agent([{"started": True}, place("app.py"), place("other.py::LIMIT"), {"finished": "limit"}], ok)
    proposals, run = discover.further(repo, "m", facts, 1.0, hide={"limit": "app.py::LIMIT"})
    assert [p["place"]["at"] for p in proposals] == ["other.py::LIMIT"] and run["controls"] == {"limit": {"at": "app.py::LIMIT", "found": True}}
    agent([{"started": True}, place("other.py::LIMIT"), {"finished": "limit"}], ok)
    assert discover.further(repo, "m", facts, 1.0, hide={"limit": "app.py::LIMIT"})[1]["controls"]["limit"]["found"] is False
