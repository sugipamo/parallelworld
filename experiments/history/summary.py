"""Count what the replays in results/ show.    python experiments/history/summary.py"""
import json
import os
from collections import Counter

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
load = lambda name: json.load(open(os.path.join(HERE, name), encoding="utf-8"))


def streaks(rows):
    """Runs of consecutive commits that needed attention: [(first, length, causes, the commit that ended it)]."""
    out, run = [], []
    for r in rows:
        bad = sorted({f["needs"] for f in r["facts"] if f["needs"]})
        if bad:
            run.append((r, bad))
        elif run:
            out.append((run[0][0], len(run), sorted({b for _, bs in run for b in bs}), r))
            run = []
    if run:
        out.append((run[0][0], len(run), sorted({b for _, bs in run for b in bs}), None))
    return out


def own():
    rows = [r for r in load("own.json") if r.get("facts")]
    print(f"## own: {len(rows)} commits carry a declaration and a checker")
    for label, part in (("all of them", rows), ("since CI ran the check (d3aa0e6be1)", rows[[r["sha"] for r in rows].index("d3aa0e6be1"):]),
                        ("since the unused layer was removed (af6a739e8f)", rows[[r["sha"] for r in rows].index("af6a739e8f"):])):
        causes = Counter(c for r in part for c in {f["needs"] for f in r["facts"] if f["needs"]})
        ok = sum(1 for r in part if not any(f["needs"] for f in r["facts"]))
        print(f"- {label}: {len(part)} commits, {ok} in order, {len(part) - ok} not; commits by what was needed: {dict(causes)}")
    print("- runs of commits that were not in order:")
    for first, n, causes, end in streaks(rows):
        print(f"    {first['sha']} x{n} {'/'.join(causes):<22} {first['subject'][:60]!r} -> ended by {end and end['subject'][:60]!r}")
    vals = [r for r in load("own-values.json") if r.get("facts")]
    changes, touched = [], 0
    for a, b in zip(vals, vals[1:]):
        was = {f["fact"]: f for f in a["facts"]}
        files = {p["at"].split("::")[0] for f in b["facts"] for p in f["places"]}
        touched += bool(files & set(b["changed"]))
        for f in b["facts"]:
            old = was.get(f["fact"])
            if old is None:
                changes.append((b["sha"], f["fact"], "declared", len(f["places"])))
                continue
            moved = [(p["at"], q["reads as"], p["reads as"]) for p in f["places"] for q in old["places"] if q["at"] == p["at"] and q["reads as"] != p["reads as"]]
            added = sorted({p["at"] for p in f["places"]} - {q["at"] for q in old["places"]})
            gone = sorted({q["at"] for q in old["places"]} - {p["at"] for p in f["places"]})
            if moved:
                changes.append((b["sha"], f["fact"], f"value changed in {len(moved)} of {len(f['places'])} places, state {f['state']}", moved[0][1][:40] + " -> " + moved[0][2][:40]))
            if added or gone:
                changes.append((b["sha"], f["fact"], f"places +{len(added)} -{len(gone)}", ", ".join(added + gone)[:80]))
    print(f"- last {len(vals)} commits (values read by today's checker): {touched} of {len(vals) - 1} touched a file a declared place is in")
    for c in changes:
        print("    ", *c)


def late(name):
    rows = load(name)
    print(f"\n## {name}: {len(rows)} commits, today's declaration held against each")
    by_sha = {r["sha"]: r for r in rows}
    facts = [f["fact"] for f in rows[-1]["facts"]]
    sessions = [s for r in rows for s in r.get("sessions", [])]
    print(f"- blind reading: {sum(len(s['places']) for s in sessions)} place readings in {len(sessions)} sessions over {sum(1 for r in rows if r.get('sessions'))} commits, "
          f"${sum(s.get('cost_usd') or 0 for s in sessions):.2f}; failed sessions {sum(1 for s in sessions if s.get('error') or s.get('no answer'))}")
    for name in facts:
        line = [next(f for f in r["facts"] if f["fact"] == name) for r in rows]
        states = Counter(f["needs"] or "ok" for f in line)
        first_whole = next((i for i, f in enumerate(line) if not any(u["broken"] for u in f["unread"])), None)
        print(f"- {name}: {dict(states)}; every place readable as declared from commit {None if first_whole is None else first_whole + 1} of {len(rows)}")
        # what happened along the way, each commit against its first parent
        events = Counter()
        notes = []
        for r, f in zip(rows, line):
            if not r["parents"] or r["parents"][0] not in by_sha:
                continue
            was = next(x for x in by_sha[r["parents"][0]]["facts"] if x["fact"] == name)
            broke = {u["at"] for u in f["unread"] if u["broken"]} - {u["at"] for u in was["unread"] if u["broken"]}
            mended = {u["at"] for u in was["unread"] if u["broken"]} - {u["at"] for u in f["unread"] if u["broken"]}
            for at in broke:
                events["a place stopped being readable as declared"] += 1
                notes.append(f"{r['sha']} broke {at}: {next(u['why'] for u in f['unread'] if u['at'] == at)[:90]}")
            events["a place became readable as declared"] += len(mended)
            old = {p["at"]: p["reads as"] for p in was["places"]}
            for p in f["places"]:
                if p["at"] in old and old[p["at"]] != p["reads as"]:
                    events["a place's value changed"] += 1
            if (f["needs"] == "violated") != (was["needs"] == "violated") and not broke and not mended:
                kind = "places came to differ" if f["needs"] == "violated" else "places came to agree"
                events[kind] += 1
                notes.append(f"{r['sha']} {kind}: {r['subject'][:70]}")
        print(f"    {dict(events)}")
        for n in notes[:12]:
            print(f"      {n}")


if __name__ == "__main__":
    own()
    for name in sorted(os.listdir(HERE)):
        if name.startswith("miclow") and name.endswith(".json"):
            late(name)
