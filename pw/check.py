"""Hold every declared fact against the files as they are now.

    python -m pw.check [--repo DIR] [--db PATH] [--lean-dir DIR] [--verify] [--unconfirmed warn] [--record]

The facts are those declared in the repository's pw-facts.json; the record is its pw-log.jsonl.
No model is consulted: places read by a pattern are computed again, Lean settles whether the
values agree, and the project's rules (pw-rules.json) say whether each reading stands. Exit
status is 1 unless every fact's places agree and every reading stands.

Checking only looks: it works on a copy of the record and leaves the project's as it is, so
that trying something out (a file changed on purpose, a branch not yet agreed on) puts nothing
into a file that is committed. Nothing is lost by that: what a check works out, it works out
again the next time. With --record, what it computed and what Lean proved is appended to the
project's record, as `pw.maintain` does for what the readers say.
"""
import argparse
import json
import os
import shutil
import sys
import tempfile

from .kernel import LOG, Kernel
from .lean_gate import LEAN_DIR, LeanGate


FACTS = "pw-facts.json"      # a project's list of facts and the places that state them


def differences(d):
    """For a list whose places do not agree: which entries are not everywhere, and where they are.
    With something laid down or defined: what each place has beyond it, and what it lacks."""
    def entries(text):
        try:
            v = json.loads(text)
        except (ValueError, TypeError):
            return None
        return v if isinstance(v, list) else None

    whole = [(p["at"], entries(p["reads as"])) for p in d["places"] if not p.get("some")]
    if any(v is None for _, v in whole):
        return []
    key = lambda x: json.dumps(x, ensure_ascii=False)
    show_ = lambda xs: ", ".join(sorted(map(str, xs)))[:300]
    laid = next((entries(i["is"]) for i in d.get("instructions", []) if "set aside" not in i), None)
    target = laid if laid is not None else entries(d.get("gives") or "")
    out = []
    if target is not None:
        what = "what was laid down" if laid is not None else "what the definition gives"
        for at, v in whole:
            more, less = [x for x in v if x not in target], [x for x in target if x not in v]
            if more:
                out.append(f"{at} has, beyond {what}: {show_(more)}")
            if less:
                out.append(f"{at} lacks, of {what}: {show_(less)}")
        return out
    where = {}
    for at, v in whole:
        for x in v:
            where.setdefault(key(x), (x, []))[1].append(at)
    groups = {}
    for x, places in where.values():
        if len(set(places)) < len(whole):
            groups.setdefault(tuple(sorted(set(places))), []).append(x)
    return [f"only in {', '.join(places)}: {show_(xs)}" for places, xs in sorted(groups.items())]


def show(report, unconfirmed="fail"):
    """Print where every fact stands. Returns True if anything needs attention.

    With unconfirmed="warn", a fact whose places agree but that rests on a reading that does
    not stand by the rules is reported and does not count as needing attention.
    """
    bad = False

    def declined(by):
        for x in by:
            print(f"          a blind reader ({x['model'] or x['actor']}) says the place does not state this: {x['why'][:200]}")
            print("          if it is about something else, take the place out of pw-facts.json; if it says two things, make it say one")

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
            print("       people's instructions about this cannot both hold. They are set aside until one is withdrawn:")
            for i in aside:
                words = f'  "{i["said"][:120]}"' if i.get("said") else ""
                print(f"          {i['by']}{' (' + i['on'] + ')' if i.get('on') else ''}: {i['is'][:100]}{words}")
            if "without the instructions set aside" in d:
                print(f"       judged without them, the fact is: {d['without the instructions set aside']}")
        if d.get("defined") and not ok:
            gives = f"; that gives {d['gives'][:100]}" if d.get("gives") else ""
            print(f"       defined from {', '.join(d['defined']['from'])} as {d['defined']['as'][:100]}{gives}")
        for i in d.get("instructions", []):
            if "set aside" not in i and not ok:
                print(f"       laid down by {i['by']}: {i['is'][:100]}")
        if not ok:
            for p in d["places"]:
                part = "lists (in part) " if p.get("some") else "reads as "
                if p.get("whole undecided"):
                    print(f"       {p['at']} {part}{p['reads as'][:100]}   (not judged: the places that state the whole of it do not agree)")
                    continue
                print(f"       {p['at']} {part}{p['reads as'][:100]}   ({p['why'] if p['stands'] else 'does not stand'})")
                if p.get("against"):
                    print(f"          against the instruction of {', '.join(p['against'])}")
                if p.get("differs from the definition"):
                    print("          not what the definition gives")
                if p.get("not in the whole"):
                    print(f"          not among the entries the other places state: {', '.join(map(str, p['not in the whole']))[:200]}")
                if not p["stands"]:
                    print("          " + ", ".join(f"{c}: {'yes' if v else 'no'}" for c, v in p["has"].items()))
                    if p["unmeasured readers"]:
                        print(f"          read blind by {', '.join(p['unmeasured readers'])}: not a measured reader here, with the instructions it read this under (python -m pw.calibrate --model ...)")
                    for other in p.get("read blind as", []):
                        print(f"          a blind reader reads {other[:100]} off it, not what the pattern computes")
                    declined(p.get("declined", []))
        if d["state"] == "violated":
            for line in differences(d):
                print(f"       {line}")
        for u in d.get("unread", []):
            print(f"       {u['at']}: {u['why'][:160]}")
            declined(u.get("declined", []))
        if d["state"] == "waits":
            print(f"       nothing to hold its places against yet: {'; '.join(d['waits for'])[:200]}")
        elif d["state"] == "violated" and any(p.get("differs from the definition") for p in d["places"]):
            print("       a place does not say what the definition gives (verified by Lean): the place, or one of the facts it is defined from, has to change")
        elif d["state"] == "conflict":
            print("       which instruction holds is for the people who gave them: take the other out of pw-facts.json")
        elif d["state"] == "violated" and any(p.get("against") for p in d["places"]):
            print("       a place does not say what was laid down: change the place, or have the instruction withdrawn")
        elif d["state"] == "violated" and any(p.get("not in the whole") for p in d["places"]):
            print("       a place lists something the others do not have; which one is right is for a person to say")
        elif d["state"] == "violated":
            print("       the places do not say the same thing; which one is right is for a person to say")
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
    ap.add_argument("--lean", choices=("needed", "always"), default="needed",
                    help="when Lean is asked: only where a value has to be worked out (a definition), or for every comparison, with a recorded proof")
    ap.add_argument("--needs-lean", action="store_true",
                    help="only print yes or no: does anything declared here need Lean? (for a CI job, to know whether to fetch it)")
    ap.add_argument("--json", action="store_true", help="print what was found as JSON instead of text (one object: the decisions)")
    ap.add_argument("--record", action="store_true",
                    help="append what this check computed and what Lean proved to the project's record (by default the record is only read)")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    if args.needs_lean:
        work = tempfile.mkdtemp(prefix="pw-check-")
        try:
            kernel = Kernel(os.path.join(work, LOG))                 # (no gate: only the declaration is looked at)
            kernel.compare = args.lean
            kernel.sync_facts(os.path.join(repo, FACTS))
            print("yes" if kernel.needs_lean() else "no")
        finally:
            shutil.rmtree(work, ignore_errors=True)
        return
    sys.exit(1 if run(repo, args.db or os.path.join(repo, LOG), args.lean_dir, args.verify, args.unconfirmed, args.record, args.lean, args.json) else 0)


def run(repo, record, lean_dir=LEAN_DIR, verify=False, unconfirmed="fail", keep=False, lean="needed", as_json=False):
    """Hold the facts of `repo` against its files and print where they stand. True if anything needs attention.

    Unless `keep`, the record is copied and the copy is what gets appended to.
    """
    scratch = None
    if not keep:
        scratch = tempfile.mkdtemp(prefix="pw-check-")
        if os.path.exists(record):
            shutil.copy(record, os.path.join(scratch, LOG))
        record = os.path.join(scratch, LOG)
    try:
        kernel = Kernel(record, gate=LeanGate(lean_dir), actor="check")
        kernel.compare = lean
        before = kernel.state()
        recorded = list(before.proofs)              # what the project's record claims Lean proved, before this check adds anything
        ways = {(h, at, json.dumps(before.models[m]["binding"], sort_keys=True)) for h, f in before.facts.items()
                for at, m in f["readings"] if before.models[m]["binding"]}
        kernel.sync_facts(os.path.join(repo, FACTS))
        with_lean = kernel.needs_lean()
        if with_lean:
            kernel.gate.usable()
        report = kernel.recheck(repo)
        if as_json:
            import contextlib
            import io
            with contextlib.redirect_stdout(io.StringIO()):
                bad = show(report, unconfirmed)
            print(json.dumps(report, ensure_ascii=False, indent=1, default=sorted))
            return bad
        bad = show(report, unconfirmed)
        if not keep:
            # A computed place stands because a blind reader once read the same off it as its way of
            # reading computes. That holds on when the place changes only if the record has what
            # this way of reading computed for the text the reader saw. A check does not write, so
            # a way of reading that is new to the record is fine now and loses that when the place
            # is next edited: say so while it costs nothing to keep.
            now = kernel.state()
            fresh = sorted({p["at"] for d in report["decisions"] for p in d["places"]
                            if p["by"] == "reader" and p["stands"]
                            and (d["h"], p["at"], json.dumps(now.models[p["m"]]["binding"], sort_keys=True)) not in ways})
            if fresh:
                print(f"note: the way {', '.join(fresh)[:300]} {'is' if len(fresh) == 1 else 'are'} read is not in the record yet. "
                      "It stands for the text as it is; to have it stand when the text changes, run `python -m pw.maintain` "
                      "(or `python -m pw.check --record`) now and commit pw-log.jsonl. No reader is called for that.")
        if verify and not with_lean and not kernel.gate.available():
            # Nothing here is judged by a proof: the values are written out and compared as they stand.
            # What the record says Lean once proved is not used, so it does not have to be run again.
            print(f"{len(recorded)} recorded proof(s) not run again: Lean is not here, and nothing declared needs it")
        elif verify:
            refused = kernel.verify(recorded)
            for r in refused:
                print(f"FAIL the record contains a proof Lean does not accept: {r['relation']} {r['args']}\n       {r['reason'][:200]}")
            print(f"{len(recorded) - len(refused)} recorded proof(s) verified again, {len(refused)} refused")
            bad |= bool(refused)
        return bad
    finally:
        if scratch:
            shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    from .kernel import cli
    cli(main)
