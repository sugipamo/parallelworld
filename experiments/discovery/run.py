"""How many of the declared places does a search find again?

    python experiments/discovery/run.py [--model claude-opus-5-5] [--levels A B C] [--budget 5]

The places declared in pw-facts.json are the known answers. A scratch copy of the repository is
made with every file that names those places taken out, and `pw.discover` is run on it:

  A  one place of each fact is hidden; the fact and its other places are given
  B  only the fact (name, type, one-sentence description) is given; all its places are hidden
  C  nothing is given; the search has to come up with the facts themselves

A hidden place counts as found if a proposal names the same file and one of the two parts
contains the other. Everything else that passes the tool's checks is listed as an extra, to be
judged by hand: it may be a place the declaration was missing.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from pw import discover                                    # noqa: E402
from pw.check import FACTS                                 # noqa: E402
from pw.kernel import LOG, Kernel, locate                  # noqa: E402
from pw.lean_gate import LEAN_DIR, LeanGate                # noqa: E402

LEAKS = ["pw-facts.json", "pw-log.jsonl", "pw-calibration.json", "docs/natural-language.md",
         "experiments/facts", "experiments/prose", "experiments/calibration", "experiments/discovery"]


def scratch():
    """The committed repository without anything that says which places are declared."""
    work = tempfile.mkdtemp(prefix="pw-discovery-")
    tar = subprocess.run(["git", "archive", "HEAD"], cwd=ROOT, capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", work], input=tar, check=True)
    for leak in LEAKS:
        path = os.path.join(work, leak)
        shutil.rmtree(path) if os.path.isdir(path) else os.path.exists(path) and os.remove(path)
    spec = os.path.join(work, "docs/spec.md")
    text = open(spec, encoding="utf-8").read()
    start = text.index("## 10. 事実と箇所")                    # the section that describes this repository's own facts
    with open(spec, "w", encoding="utf-8") as fh:
        fh.write(text[:start])
    flow = os.path.join(work, ".github/workflows/decisions.yml")
    text = open(flow, encoding="utf-8").read()
    with open(flow, "w", encoding="utf-8") as fh:
        fh.write(re.sub(r"(LEAN_VERSION: [0-9.]+).*", r"\1", text))
    return work


def at(p):
    return p if isinstance(p, str) else p["at"]


def same_place(a, b, repo):
    """Same file, and one part contains the other."""
    if a.partition("::")[0] != b.partition("::")[0]:
        return False
    x, y = locate(a, repo), locate(b, repo)
    return x is not None and y is not None and (x in y or y in x)


def norm(v):
    return json.dumps(sorted(v) if isinstance(v, list) else v, ensure_ascii=False)


def level_a(repo, facts, args):
    """Round r hides place r of every fact that has one; facts with fewer places are controls."""
    rounds = max(len(f["places"]) for f in facts)

    def one(r):
        shown = [{**f, "places": [p for i, p in enumerate(f["places"]) if i != r]} for f in facts]
        proposals, run = discover.further(repo, args.model, shown, args.budget)
        trials = []
        for f in facts:
            mine = [p["place"] for p in proposals if p.get("fact") == f["name"]]
            hidden = at(f["places"][r]) if r < len(f["places"]) else None
            hit = [p for p in mine if hidden and same_place(hidden, p["at"], repo)]
            known = [at(p) for i, p in enumerate(f["places"]) if i != r]
            trials.append({"fact": f["name"], "hidden": hidden, "found": bool(hit), "as": [p["at"] for p in hit],
                           "extras": [{**p, "overlaps a known place": any(same_place(k, p["at"], repo) for k in known)}
                                      for p in mine if p not in hit]})
        return {"round": r, "run": run, "trials": trials}

    with ThreadPoolExecutor(args.parallel) as pool:
        return list(pool.map(one, range(rounds)))


def level_b(repo, facts, args):
    """One session per fact, told what the fact is and nothing about where it is stated."""
    def one(f):
        proposals, run = discover.further(repo, args.model, [{**f, "places": []}], args.budget)
        mine = [p["place"] for p in proposals]
        hits = {at(d): [p["at"] for p in mine if same_place(at(d), p["at"], repo)] for d in f["places"]}
        return {"fact": f["name"], "run": run, "places": [{"hidden": d, "found": bool(h), "as": h} for d, h in hits.items()],
                "extras": [p for p in mine if not any(p["at"] in h for h in hits.values())]}

    with ThreadPoolExecutor(args.parallel) as pool:
        return list(pool.map(one, facts))


def level_c(repo, facts, values, args):
    """Open search, twice. A declared place counts as found if a proposed fact has a place there
    stating the declared value."""
    def one(i):
        proposals, run = discover.new(repo, args.model, [], args.budget)
        covered = []
        for f in facts:
            for d in f["places"]:
                hit = [p["new"]["name"] for p in proposals for q in p["places"]
                       if same_place(at(d), q["at"], repo) and norm(q["value"]) == values[f["name"]]]
                covered.append({"fact": f["name"], "hidden": at(d), "found": bool(hit), "in": sorted(set(hit))})
        return {"run": run, "declared places": covered,
                "proposed": [{**p["new"], "agree": discover._agree(p["places"]), "places": p["places"]} for p in proposals]}

    with ThreadPoolExecutor(args.parallel) as pool:
        return list(pool.map(one, range(args.open_runs)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--levels", nargs="+", default=["A", "B", "C"])
    ap.add_argument("--budget", type=float, default=5.0)
    ap.add_argument("--parallel", type=int, default=4)
    ap.add_argument("--open-runs", type=int, default=2)
    args = ap.parse_args()
    facts = json.load(open(os.path.join(ROOT, FACTS), encoding="utf-8"))
    record = os.path.join(tempfile.mkdtemp(prefix="pw-discovery-"), LOG)       # the project's record is only read
    shutil.copy(os.path.join(ROOT, LOG), record)
    kernel = Kernel(record, gate=LeanGate(LEAN_DIR), actor="discovery")
    kernel.sync_facts(os.path.join(ROOT, FACTS))
    values = {d["fact"]: norm(json.loads(d["places"][0]["reads as"])) for d in kernel.recheck(ROOT)["decisions"] if "fact" in d}
    repo = scratch()
    print(f"scratch copy: {repo}", flush=True)
    out = os.path.join(ROOT, "experiments/discovery/results")
    os.makedirs(out, exist_ok=True)

    def save(level, result):
        with open(os.path.join(out, f"{level}-{args.model}.json"), "w", encoding="utf-8") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)

    cost = lambda runs: round(sum(r.get("cost_usd", 0) for r in runs), 2)
    if "A" in args.levels:
        res = level_a(repo, facts, args)
        save("A", res)
        trials = [t for r in res for t in r["trials"] if t["hidden"]]
        controls = [t for r in res for t in r["trials"] if not t["hidden"]]
        print(f"\nA  one place hidden, the rest given: {sum(t['found'] for t in trials)}/{len(trials)} found   "
              f"(${cost([r['run'] for r in res])}, {len(res)} sessions)")
        for t in trials:
            if not t["found"]:
                print(f"   missed: {t['fact']} at {t['hidden']}")
        extras = [(t["fact"], e) for r in res for t in r["trials"] for e in t["extras"]]
        print(f"   {len(extras)} extra proposal(s), {sum(e['overlaps a known place'] for _, e in extras)} overlapping a known place; "
              f"{sum(bool(t['extras']) for t in controls)}/{len(controls)} controls drew a proposal")
        for name, e in sorted({(n, e["at"]): (n, e) for n, e in extras}.values(), key=lambda x: (x[0], x[1]["at"])):
            print(f"   extra: {name} at {e['at']} says {norm(e['value'])[:60]}" + ("  (overlaps a known place)" if e["overlaps a known place"] else ""))
    if "B" in args.levels:
        res = level_b(repo, facts, args)
        save("B", res)
        places = [(r["fact"], p) for r in res for p in r["places"]]
        print(f"\nB  only the fact given: {sum(p['found'] for _, p in places)}/{len(places)} found   (${cost([r['run'] for r in res])}, {len(res)} sessions)")
        for name, p in places:
            if not p["found"]:
                print(f"   missed: {name} at {at(p['hidden'])}")
        for r in res:
            for e in r["extras"]:
                print(f"   extra: {r['fact']} at {e['at']} says {norm(e['value'])[:60]}")
    if "C" in args.levels:
        res = level_c(repo, facts, values, args)
        save("C", res)
        for i, r in enumerate(res):
            got = r["declared places"]
            names = {c["fact"] for c in got if c["found"]}
            print(f"\nC  nothing given, run {i + 1}: {sum(c['found'] for c in got)}/{len(got)} declared places, "
                  f"{len(names)}/{len(facts)} declared facts   (${r['run'].get('cost_usd')})")
            for p in r["proposed"]:
                print(f"   proposed: {p['name']} ({p['type']}), {len(p['places'])} places" + ("" if p["agree"] else "  -- the places differ"))


if __name__ == "__main__":
    main()
