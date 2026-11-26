"""Replay a repository's history and hold its declared facts against every commit.

    python experiments/history/run.py own  [--out FILE]
    python experiments/history/run.py carried [--rev RANGE] [--out FILE]
    python experiments/history/run.py late --repo DIR --rev REV [--facts FILE] [--record FILE] [--read MODEL] [--out FILE]

`own`   This repository's own history. Every commit that has a checker is checked by its
        own `python -m pw.check`, with the declaration, the record, the rules and the
        calibration the commit itself carries: what CI said, or would have said, about the
        commit as it was pushed. (Recorded proofs are not run through Lean again: the
        question here is what a commit needed, not whether its record was tampered with.)

`carried`  The same commits, each with the declaration and record it carries, but held by
        today's checker: this gives the value every place read as at every commit, which
        the older checkers do not print for facts that are in order. Only meaningful for
        commits whose record and rules today's checker judges the same way.

`late`  A repository that declared its facts late (or never). Today's declaration is held
        against every earlier commit: what would have been reported, had the facts been
        declared from the start. Places read by a pattern are computed; a place an agent
        reads counts as read only for content that some reading in --record is of. With
        --read, a blind reader reads each such place whenever its content is one nobody has
        read (as `pw.maintain` would have, commit after commit); the readings accumulate, so
        the same content is never read twice. People's instructions are left out of the
        declaration: nobody had laid anything down yet. The rules and the readers'
        measurements are those of --repo's working tree.

Nothing is written to any repository: each commit is unpacked to a temporary directory and
the record is copied.
"""
import argparse
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from pw import maintain                             # noqa: E402
from pw.check import FACTS                          # noqa: E402
from pw.kernel import CALIBRATION, LOG, RULES, Kernel, KernelError      # noqa: E402
from pw.lean_gate import LEAN_DIR, LeanGate         # noqa: E402


def git(repo, *args, binary=False):
    r = subprocess.run(["git", "-C", repo, *args], capture_output=True, check=True)
    return r.stdout if binary else r.stdout.decode("utf-8", "replace")


def commits(repo, rev):
    """Oldest first, parents before children."""
    out = git(repo, "log", "--reverse", "--topo-order", "--format=%H%x09%P%x09%ad%x09%s", "--date=short", rev)
    return [dict(zip(("sha", "parents", "date", "subject"), line.split("\t", 3))) for line in out.splitlines()]


def unpack(repo, sha, dest):
    tarfile.open(fileobj=io.BytesIO(git(repo, "archive", sha, binary=True))).extractall(dest, filter="data")


def needs(d):
    """Why a fact needs attention at a commit: a short word, or None if it is in order."""
    if d["state"] in ("current", "re-established"):
        return None if all(p["stands"] for p in d["places"]) else "unconfirmed"
    if d["state"] == "stale":
        return "broken" if any(u.get("broken") for u in d["unread"]) else "stale"
    return d["state"]


COMPARE = "needed"      # --lean: when Lean is asked (see Kernel.compare)


def hold(tree, facts, record, lean_dir, read=None, budget=3.0):
    """The facts of `facts` held against the files in `tree`. Without `read`, on a copy of
    `record`; with it, on `record` itself, which takes the readings a blind reader makes."""
    work = tempfile.mkdtemp(prefix="pw-history-")
    try:
        scratch = record
        if not read:
            scratch = os.path.join(work, LOG)
            if record and os.path.exists(record):
                shutil.copy(record, scratch)
        kernel = Kernel(scratch, gate=LeanGate(lean_dir), actor="history")
        kernel.compare = COMPARE
        kernel.sync_facts(facts)
        report, sessions = kernel.recheck(tree), []
        if read:
            agent = lambda d, at: not next(p for p in kernel.state().facts[d["h"]]["places"] if p["at"] == at)["reader"]
            wanted = [(d, u["at"]) for d in report["decisions"] for u in d.get("unread", [])
                      if agent(d, u["at"]) and not u.get("broken") and "disagree" not in u["why"] and not u.get("declined")]
            if wanted:
                args = argparse.Namespace(lean_dir=lean_dir, budget=budget)
                sessions = [{k: r.get(k) for k in ("places", "cost_usd", "turns", "error", "no answer")}
                            for r in maintain.read_blind(kernel, tree, args, wanted, read, "history")]
                report = kernel.recheck(tree)
        out = []
        if sessions:
            out.append({"sessions": sessions})
        for d in report["decisions"]:
            out.append({"fact": d["fact"], "state": d["state"], "needs": needs(d),
                        "places": [{"at": p["at"], "reads as": p["reads as"], "by": p["by"], "stands": p["stands"],
                                    **{k: p[k] for k in ("against", "not in the whole", "differs from the definition") if p.get(k)}}
                                   for p in d["places"]],
                        "unread": [{"at": u["at"], "why": u["why"][:200], "broken": bool(u.get("broken")),
                                    **({"declined": [x["why"][:200] for x in u["declined"]]} if u.get("declined") else {})}
                                   for u in d.get("unread", [])]})
        return out
    finally:
        shutil.rmtree(work, ignore_errors=True)


LINE = re.compile(r"^(ok  |FAIL|WARN) (\S+)\s+(?:\[[^\]]*\] )?(?:H:\w+ )?fact: (.*)$")


def own_check(tree):
    """What the commit's own checker says about the commit."""
    if not os.path.exists(os.path.join(tree, "pw", "check.py")):
        return None
    r = subprocess.run([sys.executable, "-m", "pw.check", "--repo", "."], cwd=tree, capture_output=True, text=True,
                       env={**os.environ, "PYTHONPATH": tree, "PYTHONDONTWRITEBYTECODE": "1"})
    facts, lines = [], r.stdout.splitlines()
    for i, line in enumerate(lines):
        m = LINE.match(line)
        if not m:
            continue
        mark, state, name = m.groups()
        detail = []
        for more in lines[i + 1:]:
            if LINE.match(more):
                break
            detail.append(more.strip())
        why = None
        if mark != "ok  ":
            broken = any("cannot be read as declared" in x or "pw.discover" in x for x in detail)
            why = ("broken" if broken else "stale") if state == "stale" else \
                  "unconfirmed" if state in ("current", "re-established") else state
        facts.append({"fact": name, "state": state, "needs": why, "detail": detail if why else []})
    return {"exit": r.returncode, "facts": facts, "stderr": r.stderr[-400:] if r.returncode not in (0, 1) or not facts else ""}


def replay(repo, rev, lean_dir, facts=None, record=None, progress=True, own=False, read=None, carry=()):
    rows = []
    for n, c in enumerate(commits(repo, rev), 1):
        tree = tempfile.mkdtemp(prefix="pw-tree-")
        try:
            unpack(repo, c["sha"], tree)
            row = {**c, "sha": c["sha"][:10], "parents": [p[:10] for p in c["parents"].split()],
                   "changed": git(repo, "show", "--name-only", "--format=", "--first-parent", c["sha"]).split()}
            if own:
                got = own_check(tree) if os.path.exists(os.path.join(tree, FACTS)) else None
                row["facts"] = got and got["facts"]
                if got and (got["stderr"] or not got["facts"]):
                    row["error"] = (got["stderr"] or "no facts reported").strip().splitlines()[-1][:300]
                if got:
                    row["exit"] = got["exit"]
            elif facts is None and not os.path.exists(os.path.join(tree, FACTS)):
                row["facts"] = None
            else:
                try:
                    if facts is None:
                        row["facts"] = hold(tree, os.path.join(tree, FACTS), os.path.join(tree, LOG), lean_dir)
                        raise StopIteration
                    for name in carry:                               # the rules and the readers' measurements of today
                        if os.path.exists(os.path.join(repo, name)):
                            shutil.copy(os.path.join(repo, name), os.path.join(tree, name))
                    got = hold(tree, facts, record, lean_dir, read)
                    if got and "sessions" in got[0]:
                        row["sessions"] = got.pop(0)["sessions"]
                    row["facts"] = got
                except StopIteration:
                    pass
                except (KernelError, KeyError, ValueError) as e:
                    row["error"] = f"{type(e).__name__}: {e}"[:300]
            rows.append(row)
            if progress:
                bad = [f["needs"] for f in row.get("facts") or [] if f["needs"]]
                if row.get("sessions"):
                    bad.append(f"({sum(len(x['places']) for x in row['sessions'])} read)")
                print(f"{n:4} {row['sha']} {row.get('error') or ('-' if row['facts'] is None else ', '.join(bad) or 'ok'):<40.40} {c['subject'][:70]}", flush=True)
        finally:
            shutil.rmtree(tree, ignore_errors=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=("own", "carried", "late"))
    ap.add_argument("--repo", default=ROOT)
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--facts", help="late: the declaration to hold against every commit (default: the one in --repo's working tree)")
    ap.add_argument("--record", help="late: the record whose readings count (default: the one in --repo's working tree)")
    ap.add_argument("--lean", choices=("needed", "always"), default="needed",
                    help="carried, late: put every comparison to Lean, or only what has to be worked out")
    ap.add_argument("--read", metavar="MODEL", help="late: have this model read, blind, each place whose content nobody has read")
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--out")
    args = ap.parse_args()
    global COMPARE
    COMPARE = args.lean
    repo = os.path.abspath(args.repo)
    if args.mode == "own":
        rows = replay(repo, args.rev, args.lean_dir, own=True)
    elif args.mode == "carried":
        rows = replay(repo, args.rev, args.lean_dir)
    else:
        work = tempfile.mkdtemp(prefix="pw-history-late-")
        with open(args.facts or os.path.join(repo, FACTS), encoding="utf-8") as fh:
            declared = [{k: v for k, v in d.items() if k != "instructions"} for d in json.load(fh)]
        facts = os.path.join(work, FACTS)
        with open(facts, "w", encoding="utf-8") as fh:
            json.dump(declared, fh, ensure_ascii=False)
        record = os.path.join(work, LOG)                     # the readings made here go to a copy
        shutil.copy(args.record or os.path.join(repo, LOG), record)
        rows = replay(repo, args.rev, args.lean_dir, facts, record, read=args.read, carry=(RULES, CALIBRATION))
        if args.read and args.out:
            shutil.copy(record, os.path.splitext(args.out)[0] + ".record.jsonl")
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(rows, fh, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
