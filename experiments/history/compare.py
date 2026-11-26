"""Do two replays of the same commits judge them the same?

    python experiments/history/compare.py A.json B.json

A and B are outputs of run.py (carried or late) over the same commits, e.g. one made with
--lean needed and one with --lean always. Every fact at every commit is compared: its state
(current and re-established count as the same: both are in order), and for each place what
it read as, whether the reading stands, and what it was found to be against or outside of.
"""
import json
import sys


def place(p):
    return (p["at"], p["reads as"], p["stands"], p.get("against"), p.get("not in the whole"), p.get("differs from the definition"))


def main(a, b):
    with open(a, encoding="utf-8") as fa, open(b, encoding="utf-8") as fb:
        A, B = json.load(fa), json.load(fb)
    assert [x["sha"] for x in A] == [y["sha"] for y in B], "not the same commits"
    judged = different = 0
    for x, y in zip(A, B):
        if x.get("error") != y.get("error"):
            different += 1
            print(f"{x['sha']}: {x.get('error')} / {y.get('error')}")
        for f, g in zip(x.get("facts") or [], y.get("facts") or []):
            judged += 1
            same = lambda s: s.replace("re-established", "current")
            if same(f["state"]) != same(g["state"]) or list(map(place, f["places"])) != list(map(place, g["places"])):
                different += 1
                print(f"{x['sha']} {f['fact']}: {f['state']} / {g['state']}")
    print(f"{len(A)} commits, {judged} judgements of a fact at a commit, {different} different")
    return different


if __name__ == "__main__":
    sys.exit(1 if main(*sys.argv[1:3]) else 0)
