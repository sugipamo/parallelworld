"""Hold every declared fact against the files as they are now.

    python -m pw.check [--repo DIR] [--db PATH] [--lean-dir DIR] [--verify] [--unconfirmed warn]

The facts are those declared in the repository's pw-facts.json; the record is its pw-log.jsonl.
No model is consulted: places read by a pattern are computed again, Lean settles whether the
values agree, and the project's rules (pw-rules.json) say whether each reading stands. Exit
status is 1 unless every fact's places agree and every reading stands.
"""
import argparse
import os
import sys

from .kernel import LOG, Kernel
from .lean_gate import LEAN_DIR, LeanGate


FACTS = "pw-facts.json"      # a project's list of facts and the places that state them


def show(report, unconfirmed="fail"):
    """Print where every fact stands. Returns True if anything needs attention.

    With unconfirmed="warn", a fact whose places agree but that rests on a reading that does
    not stand by the rules is reported and does not count as needing attention.
    """
    bad = False

    def declined(by):
        for x in by:
            print(f"          a blind reader ({x['model'] or x['actor']}) says the place does not state this: {x['why'][:200]}")
            print("          if it is about something else, take the place out of pw-facts.json")

    mark = lambda ok, soft=False: "ok  " if ok else ("WARN" if soft and unconfirmed == "warn" else "FAIL")
    for d in report["decisions"]:
        # Lean says whether the places agree; the project's rules say whether each reading stands.
        agree = d["state"] in ("current", "re-established")
        loose = [p for p in d["places"] if not p["stands"]]
        ok = agree and not loose
        bad |= not ok and not (agree and unconfirmed == "warn")
        print(f"{mark(ok, agree)} {d['state']:<15} {d['h']} fact: {d['fact']}")
        aside = [i for i in d.get("instructions", []) if "set aside" in i]
        if aside:
            print("       people's instructions about this cannot both hold (verified by Lean). They are set aside until one is withdrawn:")
            for i in aside:
                words = f'  "{i["said"][:120]}"' if i.get("said") else ""
                print(f"          {i['by']}{' (' + i['on'] + ')' if i.get('on') else ''}: {i['is'][:100]}{words}")
            if "without the instructions set aside" in d:
                print(f"       judged without them, the fact is: {d['without the instructions set aside']}")
        for i in d.get("instructions", []):
            if "set aside" not in i and not ok:
                print(f"       laid down by {i['by']}: {i['is'][:100]}")
        if not ok:
            for p in d["places"]:
                part = "lists (in part) " if p.get("some") else "reads as "
                print(f"       {p['at']} {part}{p['reads as'][:100]}   ({p['why'] if p['stands'] else 'does not stand'})")
                if p.get("against"):
                    print(f"          against the instruction of {', '.join(p['against'])}")
                if p.get("not in the whole"):
                    print(f"          not among the entries the other places state: {', '.join(map(str, p['not in the whole']))[:200]}")
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
        if d["state"] == "conflict":
            print("       which instruction holds is for the people who gave them: take the other out of pw-facts.json")
        elif d["state"] == "violated" and any(p.get("against") for p in d["places"]):
            print("       a place does not say what was laid down (verified by Lean): change the place, or have the instruction withdrawn")
        elif d["state"] == "violated" and any(p.get("not in the whole") for p in d["places"]):
            print("       a place lists something the others do not have (verified by Lean); which one is right is for a person to say")
        elif d["state"] == "violated":
            print("       the places do not say the same thing (verified by Lean); which one is right is for a person to say")
        elif d["state"] == "stale" and any(u.get("broken") for u in d["unread"]):
            print("       a declared place cannot be read as declared any more: python -m pw.discover (it looks for where the statement went)")
        elif d["state"] == "stale":
            print("       read the place(s) again: python -m pw.maintain")
        elif d["state"] == "disputed":
            print("       a person has to say which reading is right: python -m pw.confirm --who NAME M:... and --reject M:...")
        elif d["state"] == "contested":
            print("       the record holds proofs both that the values agree and that they differ; one is not Lean's: python -m pw.check --verify")
        elif d["state"] == "uncovered":
            print("       Lean could settle neither that the values are the same nor that they differ")
        elif not ok:
            print("       the places agree, but a reading does not stand by the rules (pw-rules.json):")
            print("       python -m pw.maintain (a blind reading) or python -m pw.confirm (a person)")
    if not report["decisions"]:
        print("no facts declared")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--db")
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--verify", action="store_true",
                    help="run every recorded proof through Lean again instead of believing the record (use this in CI)")
    ap.add_argument("--unconfirmed", choices=("fail", "warn"), default="fail",
                    help="what to do about facts whose places agree but that rest on a reading that does not stand by the rules")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(args.db or os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="check")
    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    bad = show(kernel.recheck(repo), args.unconfirmed)
    if args.verify:
        refused = kernel.verify()
        for r in refused:
            print(f"FAIL the record contains a proof Lean does not accept: {r['relation']} {r['args']}\n       {r['reason'][:200]}")
        print(f"{len(kernel.state().proofs) - len(refused)} recorded proof(s) verified again, {len(refused)} refused")
        bad |= bool(refused)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
