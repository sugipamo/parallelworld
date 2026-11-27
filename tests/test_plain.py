"""Written-out values are compared as they stand: no Lean, no proof, nothing to forge."""
import json

import pytest

from pw import check
from pw.core import Kernel
from pw.kernel import KernelError, pattern


def repo(tmp_path, code="LIMIT = 14\nMODES = ['fast', \"safe\"]\n", doc="## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `safe`\n"):
    (tmp_path / "k.py").write_text(code)
    (tmp_path / "doc.md").write_text(doc)
    return str(tmp_path)


FACTS = [
    {"name": "limit", "type": "Nat", "places": [{"at": "k.py", "read": {"find": r"LIMIT = (\d+)", "as": "nat"}},
                                                 {"at": "doc.md::Limits", "read": {"find": r"most (\d+)", "as": "nat"}}]},
    {"name": "modes", "type": "List String", "places": [{"at": "k.py::MODES", "read": {"python": "value", "sort": True}},
                                                        {"at": "doc.md::Modes", "read": {"find_all": "`(\\w+)`", "sort": True}, "some": True}]},
]


def states(tmp_path, facts=FACTS, gate=None):
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=gate)
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    return k, {d["fact"]: d for d in k.recheck(str(tmp_path))["decisions"]}


def test_values_are_compared_without_lean(tmp_path):
    repo(tmp_path)
    k, got = states(tmp_path)
    assert {n: d["state"] for n, d in got.items()} == {"limit": "current", "modes": "current"} and not k.needs_lean()
    assert not k.state().proofs and not k.state().props                   # nothing was put to anyone as a proposition

    repo(tmp_path, code="LIMIT = 15\nMODES = ['fast']\n")
    _, got = states(tmp_path)
    assert got["limit"]["state"] == "violated"
    assert got["modes"]["state"] == "violated" and got["modes"]["places"][1]["not in the whole"] == ["safe"]

    laid = [{**FACTS[0], "instructions": [{"is": 14, "by": "ann"}]}, FACTS[1]]
    _, got = states(tmp_path, laid)
    assert [p.get("against") for p in got["limit"]["places"]] == [["ann"], None]
    both = [{**FACTS[0], "instructions": [{"is": 14, "by": "ann"}, {"is": 15, "by": "bob"}]}, FACTS[1]]
    _, got = states(tmp_path, both)
    assert got["limit"]["state"] == "conflict"


def test_a_value_of_the_wrong_kind_is_refused_without_lean(tmp_path):
    repo(tmp_path)
    k = Kernel(str(tmp_path / "pw-log.jsonl"))
    h = k.claim_fact("limit", "Nat", [{"at": "k.py", "reader": pattern(find=r"LIMIT = (\w+)")}])["h"]     # reads a string, for a number
    with pytest.raises(KernelError, match="is not a Nat written out"):
        k.read_place(h, "k.py", cwd=str(tmp_path))
    with pytest.raises(KernelError, match="not a Nat written out"):
        k.claim_fact("other", "Nat", ["doc.md::Limits"], instructions=[{"is": '"fourteen"', "by": "ann"}])


def test_what_the_record_says_lean_proved_is_not_used(tmp_path, capsys):
    """A line added to the record claiming a proof changes nothing: the values are looked at."""
    repo(tmp_path, code="LIMIT = 15\nMODES = ['fast', 'safe']\n")
    (tmp_path / "pw-facts.json").write_text(json.dumps(FACTS))
    record = tmp_path / "pw-log.jsonl"
    k, got = states(tmp_path)
    h = got["limit"]["h"]
    lean = "(((15) : Nat) = ((14) : Nat))"
    lines = [{"ts": 0, "actor": "x", "type": "agree", "h": h, "f": "F:forged", "lean": lean, "guards": []},
             {"ts": 0, "actor": "x", "type": "proof", "relation": "holds", "args": ["F:forged"], "proof": "rfl", "proof_sha": "x", "axioms": [], "gamma": "x"}]
    with open(record, "a") as fh:
        fh.write("".join(json.dumps(line) + "\n" for line in lines))
    assert check.run(str(tmp_path), str(record), unconfirmed="warn") is True
    assert "FAIL violated" in capsys.readouterr().out


def test_a_definition_needs_lean(tmp_path, monkeypatch):
    monkeypatch.setenv("PW_LAKE", str(tmp_path / "no-lake"))            # (as where Lean is not installed)
    repo(tmp_path, doc="## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `safe`: 2 modes\n")
    count = {"name": "number of modes", "type": "Nat", "defined": {"from": ["modes"], "as": "fun ms => ms.length"},
             "places": [{"at": "doc.md::Modes", "read": {"find": r"(\d+) modes", "as": "nat"}}]}
    (tmp_path / "pw-facts.json").write_text(json.dumps(FACTS + [count]))
    k = Kernel(str(tmp_path / "pw-log.jsonl"))
    with pytest.raises(KernelError, match="Lean"):                        # a definition is a Lean function: it is not taken unseen
        k.sync_facts(str(tmp_path / "pw-facts.json"))
    k.claim_fact("modes", "List String", ["doc.md::Modes"])
    k.claim_fact("number of modes", "Nat", ["doc.md::Modes"], defined={"from": ["modes"], "as": "fun ms => ms.length"})
    assert k.needs_lean()
    with pytest.raises(KernelError, match="Lean"):                        # what the definition gives has to be worked out
        k.recheck(str(tmp_path))
    with pytest.raises(Exception, match="Lean"):                          # the command says so before anything else
        check.run(str(tmp_path), str(tmp_path / "pw-log.jsonl"))


def test_a_partial_place_with_an_entry_of_its_own_is_named(tmp_path, capsys):
    """The places stating the whole agree, an example lists something they do not have: that is
    said, with the entry (and not passed over as 'not judged')."""
    repo(tmp_path, doc="## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `bogus`\n")
    two = [FACTS[0], {**FACTS[1], "places": FACTS[1]["places"] + [{"at": "k.py", "read": {"find_all": r"'(\w+)'|\"(\w+)\"".split("|")[0], "sort": True}, "some": True}]}]
    _, got = states(tmp_path, [FACTS[0], FACTS[1]])
    part = got["modes"]["places"][1]
    assert got["modes"]["state"] == "violated" and part["not in the whole"] == ["bogus"] and not part.get("whole undecided")
    (tmp_path / "pw-facts.json").write_text(json.dumps([FACTS[0], FACTS[1]]))
    check.run(str(tmp_path), str(tmp_path / "pw-log.jsonl"), unconfirmed="warn")
    assert "not among the entries the other places state: bogus" in capsys.readouterr().out and two
