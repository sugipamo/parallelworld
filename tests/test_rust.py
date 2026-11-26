"""The Rust check (rust/) has to judge as the Python check does: the same declaration, record
and files give the same verdicts, by the same rules. Skipped when it is not built and cargo is
not there to build it."""
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "experiments", "history"))
from rust import trimmed      # noqa: E402

PW = os.path.join(ROOT, "rust", "target", "release", "pw")


@pytest.fixture(scope="module")
def pw():
    if not os.path.exists(PW):
        if not shutil.which("cargo"):
            pytest.skip("the Rust check is not built and cargo is not installed")
        subprocess.run(["cargo", "build", "--release", "--locked"], cwd=os.path.join(ROOT, "rust"), check=True, capture_output=True)
    return PW


def both(pw, repo, *args):
    py = subprocess.run([sys.executable, "-m", "pw.check", "--repo", repo, *args], capture_output=True, text=True, env={**os.environ, "PYTHONPATH": ROOT})
    rs = subprocess.run([pw, "check", "--repo", repo, *args], capture_output=True, text=True)
    return py, rs


def declare(tmp_path, facts, **files):
    for name, text in files.items():
        (tmp_path / name).write_text(text)
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    return str(tmp_path)


LIMIT = {"name": "limit", "type": "Nat", "places": [{"at": "k.py::LIMIT", "read": {"python": "value", "as": "nat"}},
                                                     {"at": "doc.md::Limits", "read": {"find": r"most (\d+)", "as": "nat"}}]}
MODES = {"name": "modes", "type": "List String", "places": [{"at": "k.py::MODES", "read": {"python": "keys", "sort": True}},
                                                            {"at": "cfg.toml", "read": {"data": "mode.*.name", "sort": True}},
                                                            {"at": "doc.md::Modes", "read": {"find_all": "`(\\w+)`", "sort": True}, "some": True}]}
FILES = {"k.py": "LIMIT = 14\nMODES = {'fast': 1,\n         \"safe\": 2}\n", "doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`\n",
         "cfg.toml": '[[mode]]\nname = "fast"\n\n[[mode]]\nname = "safe"\n'}


@pytest.mark.parametrize("change", [
    {},                                                                    # everything agrees
    {"k.py": "LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n"},              # a value differs
    {"doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `bogus`\n"},  # an example lists what the whole does not have
    {"cfg.toml": '[[mode]]\nname = "fast"\n'},                             # the lists differ
    {"k.py": "LIMIT = N\nMODES = {'fast': 1, 'safe': 2}\n"},               # not written out: cannot be read
    {"doc.md": "## Limit\n\nAt most 14.\n\n## Modes\n\n`fast`\n"},         # the heading is gone
])
def test_the_same_verdicts_and_the_same_words(pw, tmp_path, change):
    repo = declare(tmp_path, [LIMIT, MODES], **{**FILES, **change})
    py, rs = both(pw, repo, "--json", "--unconfirmed", "warn")
    assert py.returncode == rs.returncode and trimmed(json.loads(py.stdout)) == trimmed(json.loads(rs.stdout))
    py, rs = both(pw, repo, "--unconfirmed", "warn")
    same = lambda out: [line for line in out.splitlines() if "cannot be read" not in line and "not written out" not in line and ": the place is not" not in line]
    assert same(py.stdout) == same(rs.stdout)                              # (what a parser says when it fails is its own wording)


def test_what_people_laid_down(pw, tmp_path):
    laid = {**LIMIT, "instructions": [{"is": 14, "by": "ann"}]}
    for facts, files in [([laid, MODES], {**FILES, "k.py": "LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n"}),
                         ([{**LIMIT, "instructions": [{"is": 14, "by": "ann"}, {"is": 15, "by": "bob", "said": "make it 15"}]}, MODES], FILES)]:
        repo = declare(tmp_path, facts, **files)
        py, rs = both(pw, repo, "--unconfirmed", "warn")
        assert py.returncode == rs.returncode == 1 and py.stdout == rs.stdout


def test_this_repository_and_what_needs_lean(pw):
    py, rs = both(pw, ROOT, "--json")
    a, b = trimmed(json.loads(py.stdout)), trimmed(json.loads(rs.stdout))
    beyond = [name for name, d in b.items() if d["state"] == "needs Lean"]
    assert beyond == ["number of conditions a rule may ask for"]           # the one definition: not judged by this build yet
    assert {n: d for n, d in a.items() if n not in beyond} == {n: d for n, d in b.items() if n not in beyond}
    assert both(pw, ROOT)[1].returncode == 2                               # ...and it says so by its exit status
    assert both(pw, ROOT, "--needs-lean")[1].stdout == both(pw, ROOT, "--needs-lean")[0].stdout == "yes\n"


def test_a_declaration_that_cannot_be_used(pw, tmp_path):
    for text in ["[{", '{"name": "x"}', '[{"name": "x", "places": ["a"]}]', '[{"name": "x", "type": "Nat", "place": ["a"]}]',
                 json.dumps([{"name": "x", "type": "Nat", "places": ["a"]}] * 2), '[{"name": "x", "type": "Nat", "places": [{"at": "a", "reader": 1}]}]']:
        (tmp_path / "pw-facts.json").write_text(text)
        py, rs = both(pw, str(tmp_path))
        assert py.returncode == rs.returncode == 2 and rs.stderr.startswith("pw: ")
    os.remove(tmp_path / "pw-facts.json")
    py, rs = both(pw, str(tmp_path))
    assert py.returncode == rs.returncode == 2 and py.stderr == rs.stderr
