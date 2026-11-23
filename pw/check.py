"""Hold every standing decision against the code as it is now.

    python -m pw.check [--repo DIR] [--db PATH] [--lean-dir DIR] [--threshold 0.9]

The record is pw-log.jsonl in the repository. If the repository has a pw-facts.json, the facts
declared there are the ones that stand.
No model is consulted: readers and stored checks are run again, stored proofs are tried again, and
Lean-verified relations are read off. Exit status is 1 unless every decision is current or was
carried over mechanically, and no two decisions contradict each other.
"""
import argparse
import os
import sys

from .kernel import LOG, Kernel
from .lean_gate import LEAN_DIR, LeanGate


FACTS = "pw-facts.json"      # a project's list of facts and the places that state them


def show(report, threshold, unconfirmed="fail"):
    """Print where every decision stands. Returns True if anything needs attention.

    With unconfirmed="warn", a decision that holds mechanically but rests on a reading that does
    not stand by the rules is reported and does not count as needing attention.
    """
    bad = bool(report["conflicts"])

    def declined(by):
        for x in by:
            print(f"          a blind reader ({x['model'] or x['actor']}) says the place does not state this: {x['why'][:200]}")
            print("          if it is about something else, take the place out of pw-facts.json")

    mark = lambda ok, soft=False: "ok  " if ok else ("WARN" if soft and unconfirmed == "warn" else "FAIL")
    for d in report["decisions"]:
        if d.get("natural_language"):
            # held only by its own checks: the bound says how far those checks go, and is not a gate
            ok = d["state"] == "checks pass"
            bad |= not ok
            print(f"{'ok  ' if ok else 'FAIL'} {d['state']:<15} [{d['lo']:.3f}, {d['hi']:.3f}] {d['h']} \"{d['text'][:90]}\" ({d['checks']} check(s), not formal)")
            if "failed" in d:
                print(f"       failing check: {d['failed'][:200]}")
            continue
        if "fact" in d:
            # Lean says whether the places agree; the project's rules say whether each reading stands.
            agree = d["state"] in ("current", "re-established")
            loose = [p for p in d["places"] if not p["stands"]]
            ok = agree and not loose
            bad |= not ok and not (agree and unconfirmed == "warn")
            print(f"{mark(ok, agree)} {d['state']:<15} {d['h']} fact: {d['fact']}")
            if not ok or len({p["reads as"] for p in d["places"]}) > 1:
                for p in d["places"]:
                    print(f"       {p['at']} reads as {p['reads as'][:100]}   ({p['why'] if p['stands'] else 'does not stand'})")
                    if not p["stands"]:
                        print("          " + ", ".join(f"{c}: {'yes' if v else 'no'}" for c, v in p["has"].items()))
                        if p["unmeasured readers"]:
                            print(f"          read blind by {', '.join(p['unmeasured readers'])}: not a measured reader here (python -m pw.calibrate --model ...)")
                        for other in p.get("read blind as", []):
                            print(f"          a blind reader reads {other[:100]} off it, not what the pattern computes")
                        declined(p.get("declined", []))
            for u in d.get("unread", []):
                print(f"       {u['at']}: {u['why'][:160]}")
                declined(u.get("declined", []))
            if d["state"] == "violated":
                print("       the places do not say the same thing (verified by Lean); which one is right is for a person to say")
            elif d["state"] == "stale":
                print("       read the place(s) again: python -m pw.maintain")
            elif d["state"] == "disputed":
                print("       a person has to say which reading is right: python -m pw.confirm --who NAME M:... and --reject M:...")
            elif not ok:
                print("       the places agree, but a reading does not stand by the rules (pw-rules.json):")
                print("       python -m pw.maintain (a blind reading) or python -m pw.confirm (a person)")
            if "error" in d:
                print(f"       {d['error'][:300]}")
            continue
        ok = d["state"] in ("current", "re-established") and d["lo"] >= threshold
        soft = d["state"] in ("current", "re-established")
        bad |= not ok and not (soft and unconfirmed == "warn")
        print(f"{mark(ok, soft)} {d['state']:<15} [{d['lo']:.3f}, {d['hi']:.3f}] {d['h']} {d['subject'].split('@')[0]} satisfies {d['spec']}")
        if d["state"] == "stale":
            print("       the file changed since an agent read it; it has to be read again (python -m pw.maintain)")
        elif d["state"] == "violated":
            print("       Lean has verified that the file, as read, does not satisfy the specification")
        elif d["state"] in ("current", "re-established") and not ok:
            print(f"       the reading of the file is not supported well enough (threshold {threshold})")
        if "note" in d:
            print(f"       {d['note']}")
        if "counterexample" in d:
            c = d["counterexample"]
            print(f"       the code no longer matches the model the proof was about: on {c['args']} the model gives {c['lean']}, the code gives {c['code']}")
        if "error" in d:
            print(f"       {d['error'][:300]}")
    for c in report["conflicts"]:
        print(f"FAIL contradictory decisions about {c['subject']}: {c['a']} ({c['specs'][0]}) and {c['b']} ({c['specs'][1]}) cannot both hold (verified by Lean)")
    if not report["decisions"]:
        print("no decisions recorded")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--db")
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--threshold", type=float, default=0.9)
    ap.add_argument("--verify", action="store_true",
                    help="run every recorded proof through Lean again instead of believing the record (use this in CI)")
    ap.add_argument("--unconfirmed", choices=("fail", "warn"), default="fail",
                    help="what to do about decisions that hold mechanically but rest on a reading that does not stand by the rules")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(args.db or os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="check")
    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    bad = show(kernel.recheck(repo), args.threshold, args.unconfirmed)
    if args.verify:
        refused = kernel.verify()
        for r in refused:
            print(f"FAIL the record contains a proof Lean does not accept: {r['relation']} {r['args']}\n       {r['reason'][:200]}")
        print(f"{len(kernel.state().proofs) - len(refused)} recorded proof(s) verified again, {len(refused)} refused")
        bad |= bool(refused)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
