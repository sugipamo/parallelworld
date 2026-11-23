"""Measure how well a blind reader reads, by planting changes whose answer is known.

    python -m pw.calibrate [--repo DIR] [--model claude-opus-5-5] [--per-place 5] [--seed 0]

For every place an agent has read, the value it states is replaced in the text of the place by
another value of the same kind (another word, another number, a renamed or removed list entry).
A blind reader is shown only the changed text. Since the change was planted, the right answer is
known without anyone judging it:

  read      the reader reports the planted value
  stuck     the reader reports the value that was there before the change: the failure that
            would let a real disagreement between places go unnoticed
  other     anything else, including declining to answer

Unchanged texts are mixed in as controls. Nothing is written to the project's record: every
trial runs against a scratch copy. The counts are appended to pw-calibration.json.

What this does not show: that planted changes resemble the ways real documents drift.
"""
import argparse
import datetime
import json
import os
import random
import re
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

from scipy.stats import beta

from .check import FACTS
from .kernel import LOG, Kernel, locate
from .lean_gate import LEAN_DIR, LeanGate
from .maintain import blind_read

RESULTS = "pw-calibration.json"
_EDGE = r"A-Za-z0-9_."


def _whole(token):
    """The token as a whole word (so that `claim` does not match inside `claim_formal`)."""
    return re.compile(rf"(?<![{_EDGE}]){re.escape(str(token))}(?![{_EDGE}])")


def _fresh(like, text, rng):
    """A value of the same kind as `like` that the text does not contain."""
    for _ in range(200):
        if isinstance(like, int):
            new = like + rng.choice([1, 2, 3, 5, 7, 10])
        elif re.fullmatch(r"[a-z]+", like):
            new = "".join(rng.choice("bcdfghjklmnprstvwz") + rng.choice("aeiou") for _ in range(max(2, len(like) // 2)))[:max(3, len(like))]
        else:
            new = f"{like}_{rng.choice('bcdfgklmnprst')}{rng.choice('aeiou')}{rng.choice('bcdfgklmnprst')}"
        if not _whole(new).search(text):
            return new
    raise ValueError("no fresh value found")


def mutants(text, value, rng, n):
    """Up to n changed versions of `text`, each with the value it now states.

    A single value is replaced everywhere it occurs as a whole word, so the changed text is
    consistent. A list has one entry renamed, or the one table row holding an entry removed.
    Returns [(kind, changed text, planted value)]; a value that does not occur literally in the
    text cannot be planted and yields nothing.
    """
    out = []
    if isinstance(value, list):
        entries = [e for e in value if _whole(e).search(text)]
        rng.shuffle(entries)
        for e in entries:
            if len(out) >= n:
                break
            lines = [ln for ln in text.splitlines(keepends=True) if _whole(e).search(ln)]
            alone = len(lines) == 1 and lines[0].lstrip().startswith("|") and not any(_whole(o).search(lines[0]) for o in value if o != e)
            if alone and len(out) % 2 == 1:
                out.append(("row removed", text.replace(lines[0], "", 1), sorted(x for x in value if x != e)))
            else:
                new = _fresh(e, text, rng)
                out.append(("entry renamed", _whole(e).sub(new, text), sorted(new if x == e else x for x in value)))
        return out
    if not _whole(value).search(text):
        return out
    seen = set()
    while len(out) < n:
        new = _fresh(value, text, rng)
        if new in seen:
            break
        seen.add(new)
        out.append(("value replaced", _whole(value).sub(str(new), text), new))
    return out


def same(a, b):
    return sorted(a) == sorted(b) if isinstance(a, list) and isinstance(b, list) else a == b


def interval(k, n, level=0.95):
    """Clopper-Pearson interval for a proportion: what the counts allow, with no prior."""
    a = (1 - level) / 2
    return (0.0 if k == 0 else float(beta.ppf(a, k, n - k + 1)), 1.0 if k == n else float(beta.ppf(1 - a, k + 1, n - k)))


def trials(kernel, repo, per_place, rng):
    """One list of trials per place an agent has read: the planted changes, then a control."""
    st = kernel.state()
    out = []
    for d in kernel.recheck(repo)["decisions"]:
        if "fact" not in d:
            continue
        for p in d.get("places", []):
            if p["by"] != "stated":
                continue
            try:
                value = json.loads(p["reads as"])
            except ValueError:
                continue
            text = locate(p["at"], repo).decode("utf-8", "replace")
            made = mutants(text, value, rng, per_place)
            for kind, changed, planted in made + [("unchanged", text, value)]:
                out.append({"fact": d["fact"], "asked": d["text"], "type": st.facts[d["h"]]["type"], "place": p["at"],
                            "kind": kind, "text": changed, "planted": planted, "before": value})
    return out


def run_session(args, number, batch):
    """One blind reader, one scratch project holding one changed text per fact."""
    work = tempfile.mkdtemp(prefix="pw-calibrate-")
    kernel = Kernel(os.path.join(work, LOG), gate=LeanGate(args.lean_dir), actor="calibrate")
    items = []
    for i, t in enumerate(batch):
        name = f"passage{i}" + (os.path.splitext(t["place"].split("::")[0])[1] or ".txt")
        with open(os.path.join(work, name), "w", encoding="utf-8") as fh:
            fh.write(t["text"])
        t["h"] = kernel.claim_fact(f"trial {i}", t["type"], [name], gloss=t["asked"])["h"]
        items.append((t["h"], name, t["type"], t["asked"]))
    run = blind_read(work, args.lean_dir, args.model, f"calibrate-{number}", items, args.budget)
    st = kernel.state()
    for t in batch:
        said = [st.algebra.objs[st.models[m]["obj"]]["text"] for _, m in st.facts[t["h"]]["readings"]]
        try:
            t["read"] = json.loads(said[-1]) if said else None
        except ValueError:
            t["read"] = said[-1]
        t["outcome"] = ("read" if t["read"] is not None and same(t["read"], t["planted"])
                        else "stuck" if t["read"] is not None and t["kind"] != "unchanged" and same(t["read"], t["before"])
                        else "other")
        del t["h"], t["text"]
    return run.get("cost_usd", 0), run.get("error")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--per-place", type=int, default=5, help="planted changes per place (one control is added to each)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--budget", type=float, default=2.0)
    ap.add_argument("--parallel", type=int, default=4)
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="calibrate")
    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    todo = trials(kernel, repo, args.per_place, random.Random(args.seed))
    if not todo:
        sys.exit("no place read by an agent whose value occurs literally in it: nothing to plant")

    # a reader never sees two versions of one fact: at most one trial per fact in a session
    sessions = []
    for t in todo:
        s = next((s for s in sessions if all(x["fact"] != t["fact"] for x in s)), None)
        if s is None:
            sessions.append(s := [])
        s.append(t)
    print(f"{len(todo)} trials on {len({t['place'] for t in todo})} place(s), {len(sessions)} blind session(s), {args.model}", flush=True)
    with ThreadPoolExecutor(args.parallel) as pool:
        ran = list(pool.map(lambda ns: run_session(args, *ns), enumerate(sessions)))
    for cost, error in ran:
        if error:
            print("   a session failed:", error[:200])

    planted = [t for t in todo if t["kind"] != "unchanged"]
    controls = [t for t in todo if t["kind"] == "unchanged"]
    count = lambda ts, o: sum(t["outcome"] == o for t in ts)
    summary = {"model": args.model, "date": datetime.date.today().isoformat(), "seed": args.seed,
               "cost_usd": round(sum(c for c, _ in ran), 2),
               "planted": {"n": len(planted), "read": count(planted, "read"), "stuck": count(planted, "stuck"), "other": count(planted, "other")},
               "unchanged": {"n": len(controls), "read": count(controls, "read")}}
    n = len(planted)
    summary["read rate"] = [round(x, 3) for x in interval(summary["planted"]["read"], n)]
    summary["stuck rate"] = [round(x, 3) for x in interval(summary["planted"]["stuck"], n)]

    kinds = sorted({t["kind"] for t in todo})
    print(f"\n{'kind of change':<16} {'n':>3} {'read':>5} {'stuck':>6} {'other':>6}")
    for k in kinds:
        ts = [t for t in todo if t["kind"] == k]
        print(f"{k:<16} {len(ts):>3} {count(ts, 'read'):>5} {count(ts, 'stuck'):>6} {count(ts, 'other'):>6}")
    print(f"\nplanted changes read: {summary['planted']['read']}/{n}   95% interval for the rate: {summary['read rate']}")
    print(f"stuck on the old value: {summary['planted']['stuck']}/{n}   95% interval for the rate: {summary['stuck rate']}")
    print(f"unchanged texts read as before: {summary['unchanged']['read']}/{len(controls)}   cost ${summary['cost_usd']}")
    for t in todo:
        if t["outcome"] != "read":
            print(f"   {t['outcome']}: {t['place']} ({t['kind']}) planted {json.dumps(t['planted'], ensure_ascii=False)[:80]} "
                  f"read {json.dumps(t['read'], ensure_ascii=False)[:80]}")

    path = os.path.join(repo, RESULTS)
    runs = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
    runs.append({**summary, "trials": todo})
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(runs, fh, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
