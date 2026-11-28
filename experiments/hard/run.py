"""Measure a blind reader on passages made to be misread.

    python experiments/hard/run.py [--model claude-opus-5-5] [--rounds 3] [--out FILE]

`pw.calibrate` measures a reader on changes it plants itself: a value swapped for another,
a passage shown with another fact's question. Those are easy. The passages here
(trials.json) were written by hand to be the kind a real file confronts a reader with: a
value of the right kind that belongs to another thing, an old value next to the new one, an
example next to the default, another notation, text that addresses the reader and tells it
what to answer, a value that is only in the surroundings, a value that goes against what a
model remembers, list entries that do not count, sentences that assert nothing. For each
the right answer is fixed in the file: a value, or declining (`expect` null). The last group
has no right answer: the passage says two different things, and what the reader does with
that is only recorded (`expect` "?").

The reader gets exactly what `pw.maintain` gives it: the instructions in pw/reader.txt, the
passage, the question, and the two tools. Each round shows every passage once, a few per
session, in a different order.

  right      read the expected value / declined where declining is right
  wrong      read another value (or read one where declining is right): what would be believed
  declined   declined a passage that does state the value: costs a re-reading, hides nothing
  no answer  neither tool was called for the passage: the session failed for it
"""
import argparse
import json
import os
import random
import shutil
import sys
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from pw.core import Kernel
from pw.kernel import LOG                    # noqa: E402
from pw.core import LEAN_DIR, LeanGate          # noqa: E402
from pw import maintain                              # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def session(model, tag, batch, budget):
    work = tempfile.mkdtemp(prefix="pw-hard-")
    try:
        kernel = Kernel(os.path.join(work, LOG), gate=LeanGate(LEAN_DIR), actor="hard")
        items = []
        for i, t in batch:
            name = f"passage{i}.md"
            with open(os.path.join(work, name), "w", encoding="utf-8") as fh:
                fh.write(t["text"])
            h = kernel.claim_fact(f"trial {i}", t["type"], [name], gloss=t["asked"])["h"]
            items.append((h, name, t["type"], t["asked"], t.get("around")))
        run = maintain.blind_read(work, LEAN_DIR, model, tag, items, budget)
        st = kernel.state()
        out = []
        for (i, t), (h, *_rest) in zip(batch, items):
            said = [st.objs[st.models[m]["obj"]]["text"] for _, m in st.facts[h]["readings"]]
            declined = [x["why"] for x in st.facts[h]["declined"]]
            read = json.loads(said[-1]) if said else None
            want = t["expect"]
            if read is None and not declined:
                outcome = "no answer"
            elif want == "?":
                outcome = "declined (no right answer)" if read is None else f"read {json.dumps(read)} (no right answer)"
            elif want is None:
                outcome = "right" if read is None else "wrong"
            elif read is None:
                outcome = "declined"
            else:
                outcome = "right" if (sorted(read) == sorted(want) if isinstance(want, list) and isinstance(read, list) else read == want) else "wrong"
            out.append({"trial": i, "group": t["group"], "expect": want, "read": read, "declined": declined[-1][:200] if declined else None, "outcome": outcome})
        return out, run.get("cost_usd") or 0, run.get("error")
    finally:
        shutil.rmtree(work, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--per-session", type=int, default=6)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--budget", type=float, default=2.0)
    ap.add_argument("--instructions", metavar="FILE", help="instructions to give the reader instead of pw/reader.txt (to try a wording before adopting it)")
    ap.add_argument("--among", type=int, metavar="N", help="with --groups: show each of their passages in a session of its own, "
                    "together with N passages drawn from the other groups (0: alone). What else is in a session changes how a passage is read")
    ap.add_argument("--groups", nargs="*", help="only the trials of these groups")
    ap.add_argument("--out")
    args = ap.parse_args()
    with open(os.path.join(HERE, "trials.json"), encoding="utf-8") as fh:
        everything = list(enumerate(json.load(fh)))
    trials = [(i, t) for i, t in everything if not args.groups or t["group"] in args.groups]
    others = [(i, t) for i, t in everything if t["group"] not in (args.groups or []) and t["expect"] != "?"]
    by_number = dict(everything)
    if args.instructions:
        with open(args.instructions, encoding="utf-8") as fh:
            maintain.READER = fh.read()
    rng = random.Random(args.seed)
    jobs = []
    for r in range(args.rounds):
        order = trials[:]
        rng.shuffle(order)
        if args.among is not None:
            for k, one in enumerate(order):
                batch = [one] + rng.sample(others, args.among)
                rng.shuffle(batch)
                jobs.append((f"hard-{r}-{k}", batch))
        else:
            jobs += [(f"hard-{r}-{k}", order[k:k + args.per_session]) for k in range(0, len(order), args.per_session)]
    with ThreadPoolExecutor(4) as pool:
        done = list(pool.map(lambda j: session(args.model, j[0], j[1], args.budget), jobs))
    rows = [x for out, _, _ in done for x in out]
    cost = sum(c for _, c, _ in done)
    errors = [e for _, _, e in done if e]
    print(f"{args.model}: {len(rows)} readings in {len(jobs)} sessions, ${cost:.2f}" + (f"; {len(errors)} session(s) ended in an error" if errors else ""))
    print(f"  {'group':<42}{'right':>7}{'wrong':>7}{'declined':>10}{'no answer':>11}")
    groups = list(dict.fromkeys(by_number[x["trial"]]["group"] for x in rows))
    for g in groups + [None]:
        c = Counter(x["outcome"] for x in rows if g is None or x["group"] == g)
        print(f"  {(g or 'all'):<42}{c['right']:>7}{c['wrong']:>7}{c['declined']:>10}{c['no answer']:>11}")
    open_ended = Counter((by_number[x["trial"]]["asked"][:50], x["outcome"]) for x in rows if "no right answer" in x["outcome"])
    for (asked, outcome), n in sorted(open_ended.items()):
        print(f"  no right answer: {asked!r}: {outcome} x{n}")
    two = [x for x in rows if "no right answer" in x["outcome"]]
    if two:
        print(f"  passages that say two things: declined {sum(1 for x in two if x['outcome'].startswith('declined'))} of {len(two)}, read one of the values {sum(1 for x in two if x['outcome'].startswith('read'))}")
    for x in rows:
        if x["outcome"] in ("wrong", "declined"):
            t = by_number[x["trial"]]
            print(f"  {x['outcome']}: [{t['group']}] asked {t['asked'][:60]!r}; expected {x['expect']!r}, read {x['read']!r}" + (f"; declined: {x['declined'][:120]}" if x["declined"] else ""))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump({"model": args.model, "rounds": args.rounds, "cost_usd": round(cost, 2), "errors": errors, "trials": rows}, fh, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
