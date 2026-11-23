"""Keep the decisions true of the files as they change.

    python -m pw.maintain [--repo DIR] [--lean-dir DIR] [--threshold 0.9]
                          [--model claude-opus-5-5] [--second-model claude-sonnet-5-5] [--budget 3]

One round of the loop that managing a project comes down to:

  1. hold every decision against the files as they are (what `pw.check` does, mechanically);
  2. have an agent read each place that changed or was never read. The reader is blind: it is
     given the text of that one place and no way to look at anything else, so that its reading
     agreeing with another place means something. It either states what the place says or says
     that the place does not state the thing; a place it does neither for counts as a failed
     session, not as a finding;
  3. have a blind reader look at each place that is read by a pattern and that no reader has
     looked at: a pattern computes a value, it does not show the value is about the thing asked;
  4. where a reading does not stand by the project's rules (pw-rules.json), have a second model
     read the place, blind as well;
  5. hold everything against the files once more and report.

What is left after that is for a person: places that do not say the same thing, readers who
disagree about a place, decisions that are violated or contradict each other. Exit status 1 if
anything is left.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

from .check import FACTS, show
from .kernel import LOG, Kernel, _sha, locate
from .lean_gate import LEAN_DIR, LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BLIND = """Below are passages from a project's files. For each one, state what it says about the thing asked,
as a Lean term of the given type, by calling `read_place(h, place, object, quote)`:

  object  the value the passage states, e.g. "\\"pqd\\"", "14", "[\\"a\\", \\"b\\"]"
  quote   the sentence, table row or line of code of the passage that says it, copied word for word
          (for a list spread over several rows, any one of them)

You can see nothing but these passages, on purpose. Report what each passage itself says. A
passage may be about something else, or mention the thing without saying what its value is:
then do not guess, and call `not_stated(h, place, why)` instead, saying what the passage is
about. A value that only looks like an answer is not one: a version of one thing is not the
version of another. Call exactly one of the two tools for every passage, then reply with one
line per passage.
"""

DECISIONS = """Some files changed, and the decisions below were tied to them only by an agent's reading of the
earlier version. Read each file as it is now and state it again. Do not change any file.

For each decision: write the file's content, as far as the decision is concerned, as a Lean term of
the given type and state it with `model(h, object)`, leaving out setup, call and domains unless the
file is code you can call. Be faithful to the file, not to the decision. Then prove `holds [F]` for
the proposition `model` returns, or `not [F]` if the file as it is now does not satisfy the
specification. In your final message say, for each decision, whether it still holds.

Decisions:
"""


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
    prompt = BLIND
    for h, place, typ, what in items:
        text = locate(place, repo).decode("utf-8", "replace")
        prompt += f"\n=== h: {h}   place: {place}\nAsked: {what} (type {typ})\nPassage:\n<<<\n{text}\n>>>\n"
    r = subprocess.run(["claude", "-p", prompt, "--model", model, "--tools", "", "--mcp-config", cfg, "--strict-mcp-config",
                        "--allowedTools", "mcp__pw__read_place,mcp__pw__not_stated", "--output-format", "json",
                        "--max-budget-usd", str(budget)],
                       cwd=work, capture_output=True, text=True)
    run = {"actor": actor, "model": model, "places": [p for _, p, _, _ in items]}
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
        n = sum(1 for b in batches.values() if any(h == d["h"] for h, _, _, _ in b))
        batches.setdefault(n, []).append((d["h"], at, st.facts[d["h"]]["type"], f'{d["fact"]}: {d["text"]}'))
    tag = _sha(model, label, *[at for _, at in wanted])[:6]
    print(f"{len(wanted)} place(s) to read {label}, blind, by {model} in {len(batches)} session(s)", flush=True)
    with ThreadPoolExecutor(4) as pool:
        runs = list(pool.map(lambda kv: blind_read(repo, args.lean_dir, model, f"{label}-{tag}-{kv[0]}", kv[1], args.budget,
                                                   db=kernel.db_path), sorted(batches.items())))
    for r, (_, batch) in zip(runs, sorted(batches.items())):
        print(f"   {r['actor']}: " + (r.get("error") or f"{r['turns']} turns, ${r['cost_usd']}"), flush=True)
        done = answered(kernel, r["actor"])
        r["no answer"] = [at for h, at, _, _ in batch if (h, at) not in done]
        for at in r["no answer"]:                         # silence is not a finding about the place
            print(f"   {r['actor']}: NO ANSWER for {at}: neither read nor declined; the session failed for this place", flush=True)
    return runs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--threshold", type=float, default=0.9)
    ap.add_argument("--model", default="claude-opus-5-5", help="the model that reads places and re-establishes decisions")
    ap.add_argument("--second-model", default="claude-sonnet-5-5",
                    help='a different model for a second, blind reading where the first stands alone; "" for none')
    ap.add_argument("--budget", type=float, default=3.0)
    ap.add_argument("--again", action="store_true",
                    help="ask about places that do not stand even where a reader already answered "
                         "(after making a fact's description more precise: the earlier answers were to another question)")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="maintain")
    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    report = kernel.recheck(repo)

    def needs_agent(d, u):
        return not next(p for p in kernel.state().facts[d["h"]]["places"] if p["at"] == u["at"])["reader"] and "disagree" not in u["why"]

    def unchecked(report):
        """Computed places no blind reader has looked at: is the pattern reading the thing asked?"""
        return [(d, p["at"]) for d in report["decisions"] if "fact" in d for p in d["places"]
                if p["by"] == "reader" and not p["stands"]
                and (args.again or not (p["read blind as"] or any(x["model"] == args.model for x in p["declined"])))]

    decisions = [d for d in report["decisions"] if d["state"] in ("stale", "unsupported") and "subject" in d]
    unread = [(d, u["at"]) for d in report["decisions"] if "fact" in d for u in d.get("unread", [])
              if needs_agent(d, u) and (args.again or not any(x["model"] == args.model for x in u.get("declined", [])))]
    if decisions or unread or unchecked(report):
        dirty = subprocess.run(["git", "status", "--porcelain", "--", ".", f":(exclude){LOG}"], cwd=repo, capture_output=True, text=True).stdout.strip()
        if dirty:
            show(report, args.threshold)
            sys.exit("\nCommit the changes first: what is read has to be what is committed.")
    silent = []
    if unread:
        silent += read_blind(kernel, repo, args, unread, args.model, "first")
        report = kernel.recheck(repo)
    if unchecked(report):
        silent += read_blind(kernel, repo, args, unchecked(report), args.model, "pattern")
        report = kernel.recheck(repo)
    if args.second_model:
        alone = [(d, p["at"]) for d in report["decisions"] if "fact" in d and d["state"] in ("current", "re-established")
                 for p in d["places"] if p["by"] == "stated" and not p["stands"]]
        if alone:
            silent += read_blind(kernel, repo, args, alone, args.second_model, "second")
            report = kernel.recheck(repo)
    if decisions:
        st = kernel.state()
        prompt = DECISIONS
        for d in decisions:
            pred = st.algebra.preds[st.formal[d["h"]]["pred"]]
            prompt += (f'- {d["h"]}: {d["subject"].split("@")[0]} must satisfy `{pred["text"]}` — {d["text"]}\n'
                       f'  type of the term: {pred["type"]}\n')
        name = "maintain-" + _sha(report["tree"], *[d["h"] for d in decisions])[:6]
        tasks = os.path.join(repo, ".pw", f"tasks-{name}.json")
        os.makedirs(os.path.dirname(tasks), exist_ok=True)
        with open(tasks, "w") as fh:
            json.dump([{"name": name, "prompt": prompt, "requires": []}], fh, ensure_ascii=False)
        print(f"{len(decisions)} decision(s) need a file read again; asking an agent ({name})", flush=True)
        subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", args.lean_dir,
                        "--model", args.model, "--budget", str(args.budget), "--parallel", "1"],
                       cwd=ROOT, capture_output=True, text=True)
        report = kernel.recheck(repo)
    bad = show(report, args.threshold)
    failed = [r for r in silent if r.get("error") or r["no answer"]]
    if failed:
        print(f"\n{len(failed)} reader session(s) failed or left a place unanswered (see above). That is not a finding: run this again.")
    sys.exit(1 if bad or failed else 0)


if __name__ == "__main__":
    main()
