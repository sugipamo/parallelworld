"""Two branches both add to the record. Is the merged record judged the same whichever way
the merge is made, and is the judgement the right one?

    python experiments/merge/run.py [--out FILE]

Each scenario builds a small repository with real git: a base commit, two branches that
each change files and add to pw-log.jsonl the way `pw.maintain` would (computed readings,
equations, proofs, a blind reader's readings), then both merges, a into b and b into a. The
record is merged by git itself with `merge=union`; other files that conflict are resolved
the way the scenario says. After each merge the facts are held against the merged files.

Reported per scenario: the state of every fact after each merge, whether the two merges
agree, whether that is the state the scenario expects, whether every recorded proof still
passes Lean, and whether any line of either branch's record was lost.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from pw.kernel import INSTRUCTIONS, Kernel      # noqa: E402
from pw.lean_gate import LeanGate               # noqa: E402

MODEL = "claude-opus-5-5"
LIMIT = {"name": "limit", "type": "Nat", "gloss": "the largest number of atoms that is solved",
         "places": [{"at": "k.py", "read": {"find": "LIMIT = (\\d+)", "as": "nat"}}, "doc.md::Limits"]}
MODE = {"name": "mode", "type": "String", "gloss": "the default mode",
        "places": [{"at": "k.py", "read": {"find": "MODE = \"(\\w+)\"", "as": "string"}}, "doc.md::Modes"]}


# (the two facts are kept apart in each file, so that git does not see edits to both as one conflict)
K = 'LIMIT = 14\n\n\n# how the solver is run\n\n\nMODE = "fast"\n'
D = ("## Limits\n\nAt most 14 atoms are solved.\n\n## Background\n\nComponents are solved one at a time.\n\n"
     "The solver is exact.\n\n## Modes\n\nThe default mode is `fast`.\n")


class Repo:
    def __init__(self):
        self.dir = tempfile.mkdtemp(prefix="pw-merge-")
        self.git("init", "-q", "-b", "base")
        self.write(".gitattributes", "pw-log.jsonl merge=union\n")
        self.write("pw-calibration.json", json.dumps([{"model": MODEL, "instructions": INSTRUCTIONS,
                   "planted": {"n": 27, "read": 27, "stuck": 0}, "decoys": {"n": 27, "accepted": 0}}]))
        self.write("k.py", K)
        self.write("doc.md", D)
        self.facts([LIMIT, MODE])
        self.n = 0

    def git(self, *args, ok=(0,)):
        r = subprocess.run(["git", "-c", "user.name=pw", "-c", "user.email=pw@example.invalid", *args], cwd=self.dir, capture_output=True, text=True)
        if r.returncode not in ok:
            raise RuntimeError(f"git {' '.join(args)}: {r.stdout}{r.stderr}")
        return r

    def write(self, path, text):
        with open(os.path.join(self.dir, path), "w", encoding="utf-8") as fh:
            fh.write(text)

    def read(self, path):
        with open(os.path.join(self.dir, path), encoding="utf-8") as fh:
            return fh.read()

    def sub(self, path, old, new):
        text = self.read(path)
        assert old in text, (path, old)
        self.write(path, text.replace(old, new))

    def facts(self, declared):
        self.write("pw-facts.json", json.dumps(declared, indent=1) + "\n")

    def kernel(self, actor):
        k = Kernel(os.path.join(self.dir, "pw-log.jsonl"), gate=LeanGate(), actor=actor)
        k.sync_facts(os.path.join(self.dir, "pw-facts.json"))
        return k

    def maintain(self, readings, actor=None):
        """What a round of pw.maintain leaves in the record: `readings` is {place: (value, quote)}
        for the places a blind reader reads now (a place two facts share: {(fact, place): ...});
        then everything is held against the files."""
        self.n += 1
        k = self.kernel(actor or f"reader-{self.n}")
        for h, fact in k.state().facts.items():
            for p in fact["places"]:
                got = readings.get((fact["name"], p["at"])) or readings.get(p["at"])
                if got and h not in k.state().withdrawn:
                    k.read_place(h, p["at"], got[0], cwd=self.dir, quote=got[1], blind=True, model=MODEL)
        k.recheck(self.dir)

    def commit(self, message):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)

    def states(self):
        """Hold the facts against the files, on a copy of the record; and run its proofs through Lean again."""
        work = tempfile.mkdtemp(prefix="pw-merge-check-")
        try:
            shutil.copy(os.path.join(self.dir, "pw-log.jsonl"), work)
            k = Kernel(os.path.join(work, "pw-log.jsonl"), gate=LeanGate(), actor="check")
            recorded = list(k.state().proofs)
            k.sync_facts(os.path.join(self.dir, "pw-facts.json"))
            out = {}
            for d in k.recheck(self.dir)["decisions"]:
                standing = all(p["stands"] for p in d["places"])
                out[d["fact"]] = d["state"] + ("" if standing or d["state"] not in ("current", "re-established") else " (a reading does not stand)")
                if d["state"] == "stale":
                    out[d["fact"]] += ": " + "; ".join(sorted({u["why"][:60] for u in d["unread"]}))
            return out, len(k.verify(recorded))
        finally:
            shutil.rmtree(work, ignore_errors=True)


DOC = {"doc.md::Limits": ("14", "At most 14 atoms are solved."), "doc.md::Modes": ('"fast"', "The default mode is `fast`.")}
# a blind reader has looked at what the patterns read, once: that holds while the patterns stay as they are
CODE = {("limit", "k.py"): ("14", "LIMIT = 14"), ("mode", "k.py"): ('"fast"', 'MODE = "fast"')}


def base(repo, both=True):
    repo.maintain({**CODE, **(DOC if both else {})})
    repo.commit("base")


def scenario(name, expect, a, b, resolve=None, setup=base, note=""):
    """Run one scenario; `a` and `b` change a branch and commit; `resolve` settles conflicts in other files."""
    result = {"scenario": name, "expected": expect, "note": note, "merges": {}}
    for order in ("a into b", "b into a"):
        repo = Repo()
        try:
            setup(repo)
            for branch, change in (("a", a), ("b", b)):
                repo.git("checkout", "-q", "-b", branch, "base")
                change(repo)
                repo.commit(branch)
            lines = {br: set(repo.git("show", f"{br}:pw-log.jsonl").stdout.splitlines()) for br in "ab"}
            into, other = ("b", "a") if order == "a into b" else ("a", "b")
            repo.git("checkout", "-q", into)
            m = repo.git("merge", "--no-edit", "-q", other, ok=(0, 1))
            conflicted = repo.git("diff", "--name-only", "--diff-filter=U").stdout.split()
            if m.returncode:
                if resolve is None:
                    raise RuntimeError(f"{name}: unexpected conflict in {conflicted}")
                resolve(repo)
                repo.commit("merge")
            merged = repo.read("pw-log.jsonl").splitlines()
            states, refused = repo.states()
            result["merges"][order] = {"states": states, "conflicts": conflicted, "proofs refused": refused,
                                       "record lines lost": len((lines["a"] | lines["b"]) - set(merged)),
                                       "record lines twice": len(merged) - len(set(merged))}
        finally:
            shutil.rmtree(repo.dir, ignore_errors=True)
    x, y = (result["merges"][o]["states"] for o in ("a into b", "b into a"))
    result["same either way"] = x == y
    fits = lambda got, want: got.startswith(want) or (want == "current" and got == "re-established")     # (in order either way)
    result["as expected"] = set(x) == set(expect) and all(fits(x[f], s) for f, s in expect.items())
    mark = "ok  " if result["same either way"] and result["as expected"] else "DIFF"
    print(f"{mark} {name}\n       a into b: {x}\n       b into a: {y}\n       expected: {expect}", flush=True)
    for o, r in result["merges"].items():
        if r["proofs refused"] or r["record lines lost"]:
            print(f"       {o}: {r['proofs refused']} proof(s) refused, {r['record lines lost']} record line(s) lost")
    return result


def run():
    out = []

    # 1. each branch changes another fact, in all its places, and reads the prose again
    def a(r):
        r.sub("k.py", "LIMIT = 14", "LIMIT = 15"); r.sub("doc.md", "At most 14", "At most 15")
        r.maintain({"doc.md::Limits": ("15", "At most 15 atoms are solved.")})

    def b(r):
        r.sub("k.py", 'MODE = "fast"', 'MODE = "safe"'); r.sub("doc.md", "is `fast`", "is `safe`")
        r.maintain({"doc.md::Modes": ('"safe"', "The default mode is `safe`.")})
    out.append(scenario("each branch changes another fact", {"limit": "current", "mode": "current"}, a, b))

    # 2. both branches do nothing but read the same unchanged places (two sessions ran maintain)
    def setup_unread(r):
        base(r, both=False)
    out.append(scenario("both branches read the same places", {"limit": "current", "mode": "current"},
                        lambda r: r.maintain(DOC), lambda r: r.maintain(DOC), setup=setup_unread))

    # 3. the classic: one branch changes the value everywhere it knows, the other adds a place that states the old value
    def b3(r):
        r.write("notes.md", "## Size\n\nComponents have up to 14 atoms.\n")
        r.facts([{**LIMIT, "places": LIMIT["places"] + ["notes.md::Size"]}, MODE])
        r.maintain({"notes.md::Size": ("14", "Components have up to 14 atoms.")})
    out.append(scenario("one branch changes the value, the other adds a place stating the old one",
                        {"limit": "violated", "mode": "current"}, a, b3,
                        note="no file conflicts: git merges cleanly, and the merged tree is inconsistent"))

    # 4. both change the same value, differently; the conflict is resolved file by file, inconsistently
    def b4(r):
        r.sub("k.py", "LIMIT = 14", "LIMIT = 16"); r.sub("doc.md", "At most 14", "At most 16")
        r.maintain({"doc.md::Limits": ("16", "At most 16 atoms are solved.")})

    def mixed(r):                                   # the code from a, the prose from b
        r.write("k.py", K.replace("14", "15"))
        r.write("doc.md", D.replace("14", "16"))
    out.append(scenario("both change the value; conflicts resolved one file from each side",
                        {"limit": "violated", "mode": "current"}, a, b4, resolve=mixed))

    def all_a(r):
        r.write("k.py", K.replace("14", "15"))
        r.write("doc.md", D.replace("14", "15"))
    out.append(scenario("both change the value; conflicts resolved for one side throughout",
                        {"limit": "current", "mode": "current"}, a, b4, resolve=all_a,
                        note="the other branch's readings are of text that is no longer there, and are simply not used"))

    # 5. the two readers read the same text differently
    def b5(r):
        r.maintain({"doc.md::Limits": ("41", "At most 14 atoms are solved.")})

    def setup5(r):
        r.maintain({**CODE, "doc.md::Modes": DOC["doc.md::Modes"]}); r.commit("base")
    out.append(scenario("two readers read the same passage differently", {"limit": "disputed", "mode": "current"},
                        lambda r: r.maintain({"doc.md::Limits": DOC["doc.md::Limits"]}), b5, setup=setup5))

    # 6. one branch stops declaring a fact, the other goes on reading it
    def a6(r):
        r.facts([MODE]); r.maintain({})

    def b6(r):
        r.sub("doc.md", "At most 14 atoms are solved.", "At most 14 atoms are solved at once.")
        r.maintain({"doc.md::Limits": ("14", "At most 14 atoms are solved at once.")})
    out.append(scenario("one branch withdraws a fact, the other reads it again", {"mode": "current"}, a6, b6))

    def keep(r):
        r.facts([LIMIT, MODE])
    def a6b(r):
        r.facts([MODE]); r.maintain({})

    def b6b(r):                                    # touches the declaration too, so that git cannot settle it alone
        r.facts([{**LIMIT, "places": LIMIT["places"][::-1]}, MODE])
        b6(r)
    out.append(scenario("... and the merge keeps the fact after all", {"limit": "current", "mode": "current"}, a6b, b6b, resolve=keep,
                        note="the record holds a withdrawal, and the fact is declared again"))

    # 7. one branch rewords the question, the other rewrites the passage; each reads again on its side
    def a7(r):
        r.facts([{**LIMIT, "gloss": "the largest number of atoms a component may have for inference to be exact"}, MODE])
        r.maintain({"doc.md::Limits": DOC["doc.md::Limits"]})
    out.append(scenario("one branch rewords the question, the other rewrites the passage", {"limit": "stale", "mode": "current"}, a7, b6,
                        note="neither reading answers the new question about the new text: it has to be read once more"))

    # 8. both branches add another place to the same fact
    def add(path, text, quote):
        def change(r):
            r.write(path, text)
            r.facts([{**LIMIT, "places": LIMIT["places"] + [f"{path}::Size"]}, MODE])
            r.maintain({f"{path}::Size": ("14", quote)})
        return change

    def both_places(r):
        r.facts([{**LIMIT, "places": LIMIT["places"] + ["one.md::Size", "two.md::Size"]}, MODE])
    out.append(scenario("both branches add a place to the same fact", {"limit": "current", "mode": "current"},
                        add("one.md", "## Size\n\nUp to 14 atoms.\n", "Up to 14 atoms."),
                        add("two.md", "## Size\n\nNo more than 14 atoms.\n", "No more than 14 atoms."), resolve=both_places,
                        note="pw-facts.json conflicts as text and is resolved by listing both places"))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    args = ap.parse_args()
    results = run()
    print(f"\n{sum(1 for r in results if r['same either way'])} of {len(results)} the same either way, "
          f"{sum(1 for r in results if r['as expected'])} as expected")
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(results, fh, ensure_ascii=False, indent=1)
