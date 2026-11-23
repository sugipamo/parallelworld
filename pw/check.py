"""Hold every standing decision against the code as it is now.

    python -m pw.check [--repo DIR] [--db PATH] [--lean-dir DIR] [--threshold 0.9]

No model is consulted: stored checks are run again and Lean-verified relations are read off.
Exit status is 1 if a decision is no longer covered by its proof or is unsupported, or two decisions
contradict each other.
"""
import argparse
import os
import sys

from .kernel import Kernel
from .lean_gate import LEAN_DIR, LeanGate


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--db")
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--threshold", type=float, default=0.9)
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(args.db or os.path.join(repo, ".pw", "events.db"), gate=LeanGate(args.lean_dir), actor="check")
    report = kernel.recheck(repo)
    bad = bool(report["conflicts"])
    for d in report["decisions"]:
        if d.get("natural_language"):
            # held only by its own checks: the bound says how far those checks go, and is not a gate
            ok = d["state"] == "checks pass"
            bad |= not ok
            print(f"{'ok  ' if ok else 'FAIL'} {d['state']:<15} [{d['lo']:.3f}, {d['hi']:.3f}] {d['h']} \"{d['text'][:90]}\" ({d['checks']} check(s), not formal)")
            if "failed" in d:
                print(f"       failing check: {d['failed'][:200]}")
            continue
        ok = d["state"] in ("current", "re-established") and d["lo"] >= args.threshold
        bad |= not ok
        print(f"{'ok  ' if ok else 'FAIL'} {d['state']:<15} [{d['lo']:.3f}, {d['hi']:.3f}] {d['h']} {d['subject'].split('@')[0]} satisfies {d['spec']}")
        if "counterexample" in d:
            c = d["counterexample"]
            print(f"       the code no longer matches the model the proof was about: on {c['args']} the model gives {c['lean']}, the code gives {c['code']}")
        if "error" in d:
            print(f"       {d['error'][:300]}")
    for c in report["conflicts"]:
        print(f"FAIL contradictory decisions about {c['subject']}: {c['a']} ({c['specs'][0]}) and {c['b']} ({c['specs'][1]}) cannot both hold (verified by Lean)")
    if not report["decisions"]:
        print("no decisions recorded")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
