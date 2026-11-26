"""Keep the facts true of the files as they change.

    python -m pw.maintain [--repo DIR] [--lean-dir DIR]
                          [--model claude-opus-5-5] [--second-model claude-sonnet-5-5] [--budget 3]

One round of the loop that keeping a project consistent comes down to:

  1. hold every fact against the files as they are (what `pw.check` does, mechanically);
  2. have an agent read each place that changed or was never read. The reader is blind: it is
     given the text of that one place and no way to look at anything else, so that its reading
     agreeing with another place means something. It either states what the place says or says
     that the place does not state the thing; a place it does neither for counts as a failed
     session, not as a finding;
  3. have a blind reader look at each place that is read by a pattern and that no reader has
     looked at: a pattern computes a value, it does not show the value is about the thing asked;
  4. where a reading does not stand by the project's rules (pw-rules.json), or differs from the
     other places, have a second model read the place, blind as well;
  5. hold everything against the files once more and report.

The files are read as they are in the working tree, so a change and the readings of it can be
committed together.

What is left after that is for a person: places that do not say the same thing, and readers
who disagree about a place. Exit status 1 if anything is left.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor

from .check import FACTS, show
from .kernel import LOG, READER, Kernel, _sha, context, locate, question
from .lean_gate import LEAN_DIR, LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def ready():
    """Stop before any session is paid for, if a reader could not answer: the readers' tools are
    served over MCP by this package, and the sessions are run by the claude command."""
    import importlib.util
    import shutil
    missing = []
    if importlib.util.find_spec("mcp") is None:
        missing.append("the Python package `mcp` is not installed (pip install mcp): without it a reader has no tool to answer with, "
                       "and every place comes back unanswered")
    if shutil.which("claude") is None:
        missing.append("the `claude` command is not on PATH: it runs the readers' sessions")
    if missing:
        sys.exit("Nothing was read. " + "; ".join(missing) + ".")


def blind_read(repo, lean_dir, model, actor, items, budget, db=None):
    """One agent session shown only the text of the given places (at most one per fact).

    The session has two tools and no other way to act: state what a place says, or say that it
    does not state the thing. What it did is in the record; a place it did neither for was not
    answered, which is a failure of the session and not a finding about the place.
    """
    work = tempfile.mkdtemp(prefix="pw-blind-")
    cfg = os.path.join(work, "mcp.json")
    with open(cfg, "w") as fh:
        json.dump({"mcpServers": {"pw": {"command": sys.executable, "args": ["-m", "pw.mcp_server"], "env": {
            "PW_DB": db or os.path.join(repo, LOG), "PW_AGENT": actor, "PW_WORKDIR": repo, "PW_LEAN_DIR": lean_dir,
            "PW_BLIND": "1", "PW_MODEL": model, "PYTHONPATH": ROOT}}}}, fh)
    prompt = READER
    for h, place, typ, what, around in items:
        text = locate(place, repo).decode("utf-8", "replace")
        prompt += f"\n=== h: {h}   place: {place}\nAsked: {what} (type {typ})\n"
        if around:
            prompt += f"What surrounds the passage in its file (not the passage; do not read the value from here):\n<<<\n{around}\n>>>\n"
        prompt += f"Passage:\n<<<\n{text}\n>>>\n"
    r = subprocess.run(["claude", "-p", prompt, "--model", model, "--tools", "", "--mcp-config", cfg, "--strict-mcp-config",
                        "--allowedTools", "mcp__pw__read_place,mcp__pw__not_stated", "--output-format", "json",
                        "--max-budget-usd", str(budget)],
                       cwd=work, capture_output=True, text=True)
    run = {"actor": actor, "model": model, "places": [item[1] for item in items]}
    try:
        out = json.loads(r.stdout)
    except ValueError:
        return {**run, "error": (r.stdout + r.stderr)[-500:]}
    run.update(turns=out.get("num_turns"), cost_usd=round(out.get("total_cost_usd", 0), 2), said=out.get("result", ""))
    if out.get("is_error") or out.get("subtype", "success") != "success":
        run["error"] = f"the session ended with {out.get('subtype') or 'an error'}: {str(out.get('result', ''))[:300]}"
    return run


def answered(kernel, actor):
    """The (fact, place) pairs an actor read or declined, from the record."""
    return {(e["h"], e["place"]) for e in kernel.events() if e["type"] in ("reading", "decline") and e.get("actor") == actor}


def read_blind(kernel, repo, args, wanted, model, label):
    """Read the wanted (fact entry, place) pairs in sessions that each see one place per fact."""
    st = kernel.state()
    batches = {}
    for d, at in wanted:
        n = sum(1 for b in batches.values() if any(item[0] == d["h"] for item in b))
        # a place too small to tell what it belongs to is shown with what surrounds it, unless
        # another place of the same fact is in that file: the reader must not see two places of one fact
        alone = all(p["at"] == at or p["at"].partition("::")[0] != at.partition("::")[0] for p in st.facts[d["h"]]["places"])
        asked = question(st.facts[d["h"]], next(p for p in st.facts[d["h"]]["places"] if p["at"] == at))[0]
        batches.setdefault(n, []).append((d["h"], at, st.facts[d["h"]]["type"], asked, context(at, repo) if alone else None))
    # a reader's name is its session's: reading the same places again is another session, so that
    # what an earlier one said is never taken for an answer of this one
    tag = _sha(model, label, str(time.time_ns()), *[at for _, at in wanted])[:6]
    print(f"{len(wanted)} place(s) to read {label}, blind, by {model} in {len(batches)} session(s)", flush=True)
    with ThreadPoolExecutor(4) as pool:
        runs = list(pool.map(lambda kv: blind_read(repo, args.lean_dir, model, f"{label}-{tag}-{kv[0]}", kv[1], args.budget,
                                                   db=kernel.db_path), sorted(batches.items())))
    for r, (_, batch) in zip(runs, sorted(batches.items())):
        print(f"   {r['actor']}: " + (r.get("error") or f"{r['turns']} turns, ${r['cost_usd']}"), flush=True)
        done = answered(kernel, r["actor"])
        r["no answer"] = [item[1] for item in batch if (item[0], item[1]) not in done]
        for at in r["no answer"]:                         # silence is not a finding about the place
            print(f"   {r['actor']}: NO ANSWER for {at}: neither read nor declined; the session failed for this place", flush=True)
    return runs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--model", default="claude-opus-5-5", help="the model that reads places")
    ap.add_argument("--second-model", default="claude-sonnet-5-5",
                    help='a different model for a second, blind reading where the first stands alone; "" for none')
    ap.add_argument("--budget", type=float, default=3.0)
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="maintain")
    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    report = kernel.recheck(repo)

    def needs_agent(d, u):
        # (a place that cannot be found as declared is not for a reader: the declaration has to be repaired)
        return (not next(p for p in kernel.state().facts[d["h"]]["places"] if p["at"] == u["at"])["reader"]
                and "disagree" not in u["why"] and not u.get("broken"))

    def unchecked(report):
        """Computed places no blind reader has looked at: is the pattern reading the thing asked?"""
        return [(d, p["at"]) for d in report["decisions"] for p in d["places"]
                if p["by"] == "reader" and not p["stands"]
                and not (p["read blind as"] or any(x["model"] == args.model for x in p["declined"]))]

    unread = [(d, u["at"]) for d in report["decisions"] for u in d.get("unread", [])
              if needs_agent(d, u) and not any(x["model"] == args.model for x in u.get("declined", []))]
    if unread or unchecked(report):
        ready()
        # A reading is of the text that was read, whatever commit that text ends up in. So the
        # files are read as they are now, committed or not, and a change and the readings of it
        # can go into one commit. If a file is edited again before committing, its readings are
        # of text that is gone, and the check says so.
        dirty = subprocess.run(["git", "status", "--porcelain", "--", ".", f":(exclude){LOG}"], cwd=repo, capture_output=True, text=True).stdout.strip()
        if dirty:
            print("Reading the files as they are now, uncommitted changes included. Commit them together with pw-log.jsonl.", flush=True)
    silent = []
    if unread:
        silent += read_blind(kernel, repo, args, unread, args.model, "first")
        report = kernel.recheck(repo)
    if unchecked(report):
        silent += read_blind(kernel, repo, args, unchecked(report), args.model, "pattern")
        report = kernel.recheck(repo)
    if args.second_model:
        # also where the places disagree: before a disagreement is put to a person, the reading that
        # differs should not rest on one reader, who may simply have misread
        st = kernel.state()
        alone = [(d, p["at"]) for d in report["decisions"] if d["state"] in ("current", "re-established", "violated")
                 for p in d["places"] if p["by"] == "stated" and not p["stands"]
                 and args.second_model not in st.models[p["m"]]["asked"].get(
                     question(st.facts[d["h"]], next(x for x in st.facts[d["h"]]["places"] if x["at"] == p["at"]))[1], {}).get("models", ())]
        if alone:
            silent += read_blind(kernel, repo, args, alone, args.second_model, "second")
            report = kernel.recheck(repo)
    bad = show(report)
    failed = [r for r in silent if r.get("error") or r["no answer"]]
    if failed:
        print(f"\n{len(failed)} reader session(s) failed or left a place unanswered (see above). That is not a finding: run this again.")
        if all(r.get("turns") in (None, 1) for r in silent):
            print("Every session ended after one turn without answering. The readers' tools may not have started: "
                  "try `python -m pw.mcp_server` by hand; it should start and wait, not fail.")
    sys.exit(1 if bad or failed else 0)


if __name__ == "__main__":
    main()
