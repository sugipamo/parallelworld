"""Does the Rust check judge every commit as the Python check does?

    python experiments/history/rust.py --repo DIR [--rev REV] [--own] [--pw PATH-TO-RUST-BINARY]

Every commit of --rev is unpacked, and both implementations are run on it with --json. By
default they are given the declaration, record, rules and measurements of --repo's working
tree (today's declaration held against the past); with --own, what each commit carries.

Compared, per fact: its state; per place what it read as, by what, whether the reading
stands and by which rule, what each condition came to, the readers that do not count, what
it is against or outside of; per unreadable place whether it is broken, and the reason where
the reason is not an error message. A fact the Rust build cannot judge yet (it needs Lean)
is counted apart.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "experiments", "history"))
from run import commits, unpack      # noqa: E402

CARRY = ("pw-facts.json", "pw-log.jsonl", "pw-rules.json", "pw-calibration.json")


def trimmed(report):
    out = {}
    for d in report["decisions"]:
        places = [{k: p.get(k) for k in ("at", "reads as", "by", "stands", "why", "some", "against", "not in the whole", "whole undecided",
                                         "contained", "has", "unmeasured readers", "read blind as")} | {"declined": len(p.get("declined") or [])}
                  for p in d["places"]]
        unread = [{"at": u["at"], "broken": bool(u.get("broken")), "why": None if u.get("broken") else u["why"], "declined": len(u.get("declined") or [])}
                  for u in d.get("unread", [])]
        out[d["fact"]] = {"state": d["state"].replace("re-established", "current"), "places": places, "unread": unread,
                          "set aside": [i.get("set aside") for i in d.get("instructions", [])],
                          "without": d.get("without the instructions set aside")}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--own", action="store_true")
    ap.add_argument("--pw", default=os.path.join(ROOT, "rust", "target", "release", "pw"))
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    judged = different = beyond = skipped = 0
    spent = {"python": 0.0, "rust": 0.0}
    import time
    for c in commits(repo, args.rev):
        tree = tempfile.mkdtemp(prefix="pw-tree-")
        try:
            unpack(repo, c["sha"], tree)
            if not args.own:
                for name in CARRY:
                    if os.path.exists(os.path.join(repo, name)):
                        shutil.copy(os.path.join(repo, name), os.path.join(tree, name))
            if not os.path.exists(os.path.join(tree, "pw-facts.json")):
                skipped += 1
                continue
            t = time.time()
            py = subprocess.run([sys.executable, "-m", "pw.check", "--repo", tree, "--json"], capture_output=True, text=True, env={**os.environ, "PYTHONPATH": ROOT})
            spent["python"] += time.time() - t
            t = time.time()
            rs = subprocess.run([args.pw, "check", "--repo", tree, "--json"], capture_output=True, text=True)
            spent["rust"] += time.time() - t
            if py.returncode == 2 or rs.returncode == 2:
                if (py.returncode == 2) != (rs.returncode == 2):
                    different += 1
                    print(f"{c['sha'][:10]}: python exit {py.returncode} {py.stderr.strip()[-150:]!r} / rust exit {rs.returncode} {rs.stderr.strip()[-150:]!r}")
                else:
                    skipped += 1
                continue
            a, b = trimmed(json.loads(py.stdout)), trimmed(json.loads(rs.stdout))
            for fact in a:
                if b.get(fact, {}).get("state") == "needs Lean":
                    beyond += 1
                    continue
                judged += 1
                if a[fact] != b.get(fact):
                    different += 1
                    if different <= 8:
                        x, y = a[fact], b.get(fact) or {}
                        where = next((k for k in x if x[k] != y.get(k)), "?")
                        print(f"{c['sha'][:10]} {fact}: differs in {where}\n   python: {json.dumps(x[where], ensure_ascii=False)[:400]}\n   rust:   {json.dumps(y.get(where), ensure_ascii=False)[:400]}")
            if (py.returncode != rs.returncode) and not any(v["state"] == "needs Lean" for v in b.values()):
                different += 1
                print(f"{c['sha'][:10]}: exit status {py.returncode} / {rs.returncode}")
        finally:
            shutil.rmtree(tree, ignore_errors=True)
    print(f"{judged} judgements of a fact at a commit compared, {different} different; {beyond} need Lean (not judged by the Rust build yet); "
          f"{skipped} commits without a usable declaration; python {spent['python']:.0f}s, rust {spent['rust']:.1f}s")
    return different


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
