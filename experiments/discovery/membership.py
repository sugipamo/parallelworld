"""Does showing a proposed place, alone, to a blind reader sort the right proposals from the wrong ones?

    python experiments/discovery/membership.py [--model claude-sonnet-5-5]

The searches in run.py proposed seven places that the hand-written declaration did not have.
They all passed the mechanical checks (the place exists, the quote is in it, the value is in
the quote). Judged by hand, three state the fact and four do not. Here each is shown to a blind
reader the way `pw.discover` does before it keeps a proposal, against a copy of the record and
the declaration as it was before the search.
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

from pw import discover                                    # noqa: E402
from pw.kernel import LOG                                  # noqa: E402
from pw.core import LEAN_DIR                          # noqa: E402

BEFORE = "2ce25a5"       # the commit whose pw-facts.json is the hand-written declaration
SUBJECT = "e11f8fe"      # the repository the proposals were made about; some of those places have since been removed
JUDGED = {               # by hand: does the place state the fact?
    ("default dependence class", "docs/symbols.md::9. 置いている仮定"): (True, "says the default is pqd"),
    ("default threshold, in thousandths", "pw/check.py"): (True, "the usage line gives the default"),
    ("default threshold, in thousandths", "pw/maintain.py"): (True, "the usage line gives the default"),
    ("Lean version", "experiments/selfcheck/lean/lakefile.toml"): (False, "the revision of mathlib, not the Lean version"),
    ("Lean version", "experiments/selfcheck/lean/lake-manifest.json::packages.0.inputRev"): (False, "the revision of mathlib, not the Lean version"),
    ("axioms a proof may depend on", "docs/symbols.md::2. 形式層 ― リンデンバウム代数（一致）"): (False, "mentions one axiom in passing, not the list"),
    ("axioms a proof may depend on", "experiments/selfcheck/RESULTS.md"): (False, "a record of one experiment's proofs"),
}


def proposed():
    """The seven proposals, as the searches reported them."""
    found = {}
    out = os.path.join(ROOT, "experiments/discovery/results")
    for name in sorted(os.listdir(out)):
        if name[:2] not in ("A-", "B-"):
            continue
        for r in json.load(open(os.path.join(out, name), encoding="utf-8")):
            for fact, extras in ([(t["fact"], t["extras"]) for t in r["trials"]] if "trials" in r else [(r["fact"], r["extras"])]):
                for e in extras:
                    if (fact, e["at"]) in JUDGED:
                        found[(fact, e["at"])] = {"fact": fact, "place": {k: e[k] for k in ("at", "read", "value", "quote")}}
    return [found[k] for k in JUDGED]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="claude-sonnet-5-5")
    ap.add_argument("--budget", type=float, default=3.0)
    args = ap.parse_args()
    facts = json.loads(subprocess.run(["git", "show", f"{BEFORE}:pw-facts.json"], cwd=ROOT, capture_output=True, text=True, check=True).stdout)
    record = os.path.join(tempfile.mkdtemp(prefix="pw-membership-"), LOG)       # the project's record is only read
    shutil.copy(os.path.join(ROOT, LOG), record)
    repo = tempfile.mkdtemp(prefix="pw-membership-")
    tar = subprocess.run(["git", "archive", SUBJECT], cwd=ROOT, capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", repo], input=tar, check=True)
    _, verdicts, runs = discover.confirm(repo, LEAN_DIR, facts, proposed(), args.model, args.budget, record)
    right = 0
    print(f"\n{'by hand':<8} {'reader':<8} place")
    for v in verdicts:
        states, note = JUDGED[(v["fact"], v["at"])]
        got = "keep" if v["kept"] else "drop" if v["answered"] else "????"
        right += v["answered"] and v["kept"] == states
        print(f"{'keep' if states else 'drop':<8} {got:<8} {v['fact']} at {v['at']}\n{'':<17} by hand: {note}\n{'':<17} reader:  {v['why'][:260]}")
    print(f"\nthe blind reader agrees with the hand judgement on {right} of {len(verdicts)}   "
          f"(${round(sum(r.get('cost_usd', 0) for r in runs), 2)}, {args.model})")
    with open(os.path.join(ROOT, f"experiments/discovery/results/membership-{args.model}.json"), "w", encoding="utf-8") as fh:
        json.dump([{**v, "by hand": JUDGED[(v["fact"], v["at"])][0]} for v in verdicts], fh, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
