"""Measure how well a blind reader reads, by planting changes whose answer is known.

    python -m pw.calibrate [--repo DIR] [--model claude-opus-5-5] [--per-place 5] [--decoys 30] [--seed 0]

For every place an agent has read, the value it states is replaced in the text of the place by
another value of the same kind (another word, another number, a renamed or removed list entry).
A blind reader is shown only the changed text. Since the change was planted, the right answer is
known without anyone judging it:

  read      the reader reports the planted value
  stuck     the reader reports the value that was there before the change: the failure that
            would let a real disagreement between places go unnoticed
  other     anything else, including declining to answer

Unchanged texts are mixed in as controls.

A reader also has to refuse. A decoy is a place of one fact shown with the question of another
fact of the same type, where the place does not contain that other fact's value (for a list:
none of its entries): whatever the reader reads off it is wrong, and the right answer is to
say the place does not state the thing.

  declined  the reader said so
  accepted  the reader read a value off a place that is about something else: the failure that
            would let a place be attached to a fact it has nothing to do with

A reader also has to notice a passage that is at odds with itself. For a place that states a
single value, the line that states it is repeated right after itself with another value, so
that the passage says two things. The right answer is to decline, naming both:

  declined  the reader said the passage does not state one value
  picked    the reader read one of the two: the failure that hides a contradiction inside a place

A trial the reader neither read nor declined is "no answer". It says the session failed, not
what the reader would have done, and is left out of every rate.

Nothing is written to the project's record: every trial runs against a scratch copy. The
counts are appended to pw-calibration.json, with the identity of the instructions the reader was
given. Whether a reader counts is decided from all runs under the current instructions added up
(kernel.reader_measurements), so measuring again until one run comes out well does not help;
when the instructions change, the earlier runs no longer speak for the reader.

What this does not show: that planted changes resemble the ways real documents drift, or that
these decoys resemble the places a search wrongly proposes.
"""
import argparse
import datetime
import json
import os
import random
import re
import shutil
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

from .check import FACTS
from .kernel import INSTRUCTIONS, LOG, Kernel, context, interval, locate, reader_measurements
from .lean_gate import LEAN_DIR, LeanGate
from .maintain import blind_read, ready

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
    consistent. A list has one entry renamed, or the one table row holding an entry removed
    (not where the text states the number of entries: the change must not make it contradict itself).
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
            # Where the passage also says how many entries there are, taking a row out leaves it
            # at odds with itself, and a reader is right to decline that: no row is removed there.
            alone = alone and not _whole(len(value)).search(text)
            if alone and len(out) % 2 == 1:
                out.append(("row removed", text.replace(lines[0], "", 1), sorted(x for x in value if x != e)))
            else:
                new = _fresh(e, text, rng)
                # the word may also be part of another entry ("blind" in "read blind"): that entry changes with it
                out.append(("entry renamed", _whole(e).sub(new, text), sorted(_whole(e).sub(new, x) for x in value)))
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


def doubled(text, value, rng, n, span=None):
    """Up to n versions of `text` that say two things: the line stating the value, and right after
    it the same line with another value. `span` is where the value is, if a pattern says so;
    otherwise its first occurrence as a whole word. Returns [("said twice", text, other value)]."""
    if span is None:
        m = _whole(value).search(text)
        if m is None or isinstance(value, list):
            return []
        span = m.span()
    a, b = span
    start, end = text.rfind("\n", 0, a) + 1, text.find("\n", b)
    end = len(text) if end < 0 else end
    line, old = text[start:end], text[a:b]
    if not line.strip() or line.lstrip().startswith("#"):
        return []                                           # (a heading said twice is two sections, not two claims)
    out, seen = [], set()
    for _ in range(n * 4):
        if len(out) >= n:
            break
        if re.fullmatch(r"\d+", old):
            new = str(int(old) + rng.choice([1, 2, 3, 5, 7, 10]))
        elif re.fullmatch(r"[\d.]*\d", old):
            new = old[:-1] + str((int(old[-1]) + rng.choice([1, 2, 3, 4])) % 10)
        else:
            new = str(_fresh(old, text, rng))
        if new == old or new in seen or _whole(new).search(text):
            continue
        seen.add(new)
        out.append(("said twice", text[:end] + "\n" + line[:a - start] + new + line[b - start:] + text[end:], new))
    return out


def _value_span(rd, text):
    """Where a pattern finds its one value in a text: (start, end), or None."""
    if not rd or rd.get("language") != "pattern" or "find" not in rd or "rewrite" in rd:
        return None
    start = 0
    for step in [*rd.get("within", []), rd["find"]]:
        found = list(re.finditer(step, text, re.M))
        if len(found) != 1:
            return None
        a, b = found[0].span(1)
        start, text = start + a, text[a:b]
    return start, start + len(text)


def same(a, b):
    return sorted(a) == sorted(b) if isinstance(a, list) and isinstance(b, list) else a == b


def decoys(facts, st, repo, rng, n):
    """Up to n (place of one fact, question of another) pairs whose right answer is to decline."""
    def overlap(a, b):
        x, y = locate(a, repo), locate(b, repo)
        return a.partition("::")[0] == b.partition("::")[0] and x is not None and y is not None and (x in y or y in x)

    found = {}
    for a in facts:
        for p in a["places"]:
            text = locate(p["at"], repo).decode("utf-8", "replace")
            for b in facts:
                if b is a or st.facts[b["h"]]["type"] != st.facts[a["h"]]["type"]:
                    continue
                value = json.loads(next(q for q in b["places"] if not q.get("some"))["reads as"])
                # (of a list, one entry is enough: a place that names an entry does state part of the
                # thing, and a reader who reads that entry off it has read it right)
                stated = any(_whole(e).search(text) for e in value) if isinstance(value, list) else bool(_whole(value).search(text))
                if stated or any(overlap(p["at"], q["at"]) for q in st.facts[b["h"]]["places"]):
                    continue                                   # the place may well state it: not a decoy
                found.setdefault(b["fact"], []).append({
                    "fact": b["fact"], "asked": next(q for q in b["places"] if not q.get("some"))["question"],
                    "type": st.facts[b["h"]]["type"], "place": p["at"],
                    "kind": "decoy", "text": text, "planted": None, "before": None, "about": a["fact"],
                    "around": context(p["at"], repo)})         # shown as a real reader would be shown it
    for pairs in found.values():
        rng.shuffle(pairs)
    out, used = [], {}
    while len(out) < n and any(found.values()):                # in turn over the facts asked about, each place at most twice
        for name in sorted(found):
            if found[name] and len(out) < n:
                t = found[name].pop()
                if used.get(t["place"], 0) < 2:
                    used[t["place"]] = used.get(t["place"], 0) + 1
                    out.append(t)
    return out


def trials(kernel, repo, per_place, rng, n_decoys=0, twice=0):
    """Per place an agent has read: the planted changes, then a control. Then the decoys."""
    st = kernel.state()
    out = []
    facts = [d for d in kernel.recheck(repo)["decisions"] if d.get("places") and "unread" not in d]
    for d in facts:
        for p in d.get("places", []):
            if p["by"] != "stated":
                # prose that a pattern reads is also shown to readers (once, to see that the pattern
                # reads the thing asked): a passage for the "said twice" trials, nothing else
                decl = next(x for x in st.facts[d["h"]]["places"] if x["at"] == p["at"])
                text = locate(p["at"], repo).decode("utf-8", "replace")
                span = _value_span(decl["reader"], text) if p["at"].partition("::")[0].endswith((".md", ".markdown", ".txt", ".rst")) else None
                for kind, changed, other in (doubled(text, None, rng, twice, span) if span else []):
                    out.append({"fact": d["fact"], "asked": p["question"], "type": st.facts[d["h"]]["type"], "place": p["at"],
                                "kind": kind, "text": changed, "planted": None, "before": text[span[0]:span[1]], "other": other, "about": d["fact"]})
                continue
            try:
                value = json.loads(p["reads as"])
            except ValueError:
                continue
            text = locate(p["at"], repo).decode("utf-8", "replace")
            made = mutants(text, value, rng, per_place)
            for kind, changed, planted in made + [("unchanged", text, value)]:
                out.append({"fact": d["fact"], "asked": p["question"], "type": st.facts[d["h"]]["type"], "place": p["at"],
                            "kind": kind, "text": changed, "planted": planted, "before": value, "about": d["fact"]})
            for kind, changed, other in doubled(text, value, rng, twice):
                out.append({"fact": d["fact"], "asked": p["question"], "type": st.facts[d["h"]]["type"], "place": p["at"],
                            "kind": kind, "text": changed, "planted": None, "before": value, "other": other, "about": d["fact"]})
    return out + decoys(facts, st, repo, rng, n_decoys)


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
        items.append((t["h"], name, t["type"], t["asked"], t.pop("around", None)))
    run = blind_read(work, args.lean_dir, args.model, f"calibrate-{number}", items, args.budget)
    st = kernel.state()
    for t in batch:
        said = [st.objs[st.models[m]["obj"]]["text"] for _, m in st.facts[t["h"]]["readings"]]
        try:
            t["read"] = json.loads(said[-1]) if said else None
        except ValueError:
            t["read"] = said[-1]
        declined = [x["why"] for x in st.facts[t["h"]]["declined"]]
        if t["read"] is None:                       # silence is a failed session, not something the reader did
            t["outcome"] = "declined" if declined else "no answer"
            t["why"] = declined[-1] if declined else None
        elif t["kind"] == "decoy":
            t["outcome"] = "accepted"
        elif t["kind"] == "said twice":
            t["outcome"] = "picked"
        else:
            t["outcome"] = ("read" if same(t["read"], t["planted"])
                            else "stuck" if t["kind"] != "unchanged" and same(t["read"], t["before"]) else "other")
        del t["h"], t["text"]
    return run.get("cost_usd", 0), run.get("error")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--per-place", type=int, default=5, help="planted changes per place (one control is added to each)")
    ap.add_argument("--decoys", type=int, default=30, help="places shown with the question of another fact")
    ap.add_argument("--twice", type=int, default=2, help="per place that states one value: versions of it that say two things")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--budget", type=float, default=2.0)
    ap.add_argument("--parallel", type=int, default=4)
    args = ap.parse_args()
    ready()
    repo = os.path.abspath(args.repo)
    scratch = os.path.join(tempfile.mkdtemp(prefix="pw-calibrate-"), LOG)       # the project's record is only read
    if os.path.exists(os.path.join(repo, LOG)):
        shutil.copy(os.path.join(repo, LOG), scratch)
    kernel = Kernel(scratch, gate=LeanGate(args.lean_dir), actor="calibrate")
    kernel.gate.usable()
    kernel.sync_facts(os.path.join(repo, FACTS))
    todo = trials(kernel, repo, args.per_place, random.Random(args.seed), args.decoys, args.twice)
    if not todo:
        sys.exit("no place read by an agent whose value occurs literally in it: nothing to plant")

    # a reader never sees two versions of one fact, nor one place twice: at most one trial per
    # fact in a session, counting both the fact asked about and the fact the place belongs to
    sessions = []
    for t in todo:
        s = next((s for s in sessions if all({x["fact"], x["about"]}.isdisjoint({t["fact"], t["about"]}) for x in s)), None)
        if s is None:
            sessions.append(s := [])
        s.append(t)
    print(f"{len(todo)} trials on {len({t['place'] for t in todo})} place(s), {len(sessions)} blind session(s), {args.model}", flush=True)
    with ThreadPoolExecutor(args.parallel) as pool:
        ran = list(pool.map(lambda ns: run_session(args, *ns), enumerate(sessions)))
    for cost, error in ran:
        if error:
            print("   a session failed:", error[:200])

    silent = [t for t in todo if t["outcome"] == "no answer"]
    answered = [t for t in todo if t["outcome"] != "no answer"]            # a rate is over the trials the reader answered
    planted = [t for t in answered if t["kind"] not in ("unchanged", "decoy", "said twice")]
    two = [t for t in answered if t["kind"] == "said twice"]
    controls = [t for t in answered if t["kind"] == "unchanged"]
    baits = [t for t in answered if t["kind"] == "decoy"]
    count = lambda ts, o: sum(t["outcome"] == o for t in ts)
    outcomes = ("read", "stuck", "other", "declined", "accepted", "picked")
    summary = {"model": args.model, "instructions": INSTRUCTIONS, "date": datetime.date.today().isoformat(), "seed": args.seed,
               "cost_usd": round(sum(c for c, _ in ran), 2), "no answer": len(silent),
               "planted": {"n": len(planted), **{o: count(planted, o) for o in ("read", "stuck", "other", "declined")}},
               "unchanged": {"n": len(controls), "read": count(controls, "read")},
               "decoys": {"n": len(baits), "declined": count(baits, "declined"), "accepted": count(baits, "accepted")},
               "twice": {"n": len(two), "declined": count(two, "declined"), "picked": count(two, "picked")}}
    n = len(planted)
    if n:
        summary["read rate"] = [round(x, 3) for x in interval(summary["planted"]["read"], n)]
        summary["stuck rate"] = [round(x, 3) for x in interval(summary["planted"]["stuck"], n)]
    if baits:
        summary["accept rate"] = [round(x, 3) for x in interval(summary["decoys"]["accepted"], len(baits))]
    if two:
        summary["pick rate"] = [round(x, 3) for x in interval(summary["twice"]["picked"], len(two))]

    kinds = sorted({t["kind"] for t in todo})
    print(f"\n{'kind of trial':<16} {'n':>3} " + " ".join(f"{o:>8}" for o in outcomes) + f" {'no answer':>10}")
    for k in kinds:
        ts = [t for t in todo if t["kind"] == k]
        print(f"{k:<16} {len(ts):>3} " + " ".join(f"{count(ts, o):>8}" for o in outcomes) + f" {count(ts, 'no answer'):>10}")
    if n:
        print(f"\nplanted changes read: {summary['planted']['read']}/{n}   95% interval for the rate: {summary['read rate']}")
        print(f"stuck on the old value: {summary['planted']['stuck']}/{n}   95% interval for the rate: {summary['stuck rate']}")
    if baits:
        print(f"decoys read as if they stated the thing: {summary['decoys']['accepted']}/{len(baits)}   "
              f"95% interval for the rate: {summary['accept rate']}")
    if two:
        print(f"passages saying two things, read as one of them: {summary['twice']['picked']}/{len(two)}   "
              f"95% interval for the rate: {summary['pick rate']}")
    print(f"unchanged texts read as before: {summary['unchanged']['read']}/{len(controls)}   cost ${summary['cost_usd']}")
    if silent:
        print(f"{len(silent)} trial(s) got no answer and are in no rate: the session failed for them")
    for t in todo:
        if t["outcome"] not in ("read", "declined") or (t["outcome"] == "declined" and t["kind"] not in ("decoy", "said twice")):
            print(f"   {t['outcome']}: {t['place']} ({t['kind']}, asked: {t['fact']}) planted {json.dumps(t['planted'], ensure_ascii=False)[:60]} "
                  f"read {json.dumps(t['read'], ensure_ascii=False)[:80]}")

    path = os.path.join(repo, RESULTS)
    runs = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
    runs.append({**summary, "trials": todo})
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(runs, fh, ensure_ascii=False, indent=1)

    # what counts is every run under these instructions together, not this one
    m = reader_measurements(repo)[args.model]
    print(f"\nall {m['runs']} run(s) of {args.model} under the instructions readers are given now, added up:")
    print(f"   planted changes read {m['read']}/{m['planted']}, stuck {m['stuck']}/{m['planted']}, decoys read {m['accepted']}/{m['decoys']}, "
          f"one of two values picked {m['picked']}/{m['twice']}")
    print("   95% bounds: " + ", ".join(f"{k} {[round(x, 3) for x in m[k]]}" for k in ("read rate", "stuck rate", "accept rate", "pick rate") if k in m))


if __name__ == "__main__":
    from .kernel import cli
    cli(main)
