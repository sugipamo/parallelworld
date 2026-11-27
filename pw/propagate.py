"""Write what was laid down into the places that say otherwise: the check, run in reverse.

    python -m pw.propagate [--repo DIR] [--suppose 'FACT NAME=VALUE' ...] [--apply]

`pw.check` reads the places and holds them against what a person laid down. This goes the other
way: for every fact with an instruction, each place that is against it gets the instructed value
written into it. The same for a fact that is a definition: a place that does not say what the
definition gives gets that value.

  - A place read by a simple pattern (one value found by `find`) is written mechanically: the
    piece the pattern matched is replaced, nothing else. What was written is read back with the
    same pattern and has to read as the instructed value; a write the pattern does not confirm
    is not made.
  - Any other place (a list, a rewritten spelling, prose read by an agent, a key inside JSON) is
    not determined by its reading in reverse. It is listed as left to change by hand; or, with
    --agent, an agent is asked for the new text of that place. The agent is shown the passage
    and the value and has no access to any file: it answers through a tool, and what it
    proposes is put into the file only if
      - it changes little (it is an edit, not a rewrite),
      - no other declared place of that file reads differently afterwards,
      - and the place, read again, gives the value: by its pattern, or, where it is read by a
        reader, by a blind reader who is shown the new text and not told what to expect.

Nothing is written unless --apply is given: without it the changes are shown as a diff.

--suppose tries a value nobody has laid down: a hypothesis. "Suppose the default mode were
safe": is that against an instruction that stands, and which places would have to change? The
supposed value is held against the instructions like one more instruction. If Lean shows it to
differ from one, that is reported and nothing is written for the fact. Supposing never adds an
instruction: making it one is for a person, in pw-facts.json.
"""
import argparse
import difflib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

from .check import FACTS
from .core import Kernel
from .kernel import LOG, KernelError, _json_part, _md_section, _py_part, _sha, compute, context, question, write_pattern
from .lean_gate import LEAN_DIR

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUPPOSED = "(supposed)"
UNIT = 8000          # the longest passage an agent is asked to give back whole

EDIT = """Below are passages from a project's files. Each states a value that has to change. Rewrite each
passage so that it states the new value instead, and change nothing else: keep the wording, the
formatting, the order and every other statement exactly as they are.

  - Where the value is a list, the new list is given whole: add, remove or rename entries so that
    the passage states exactly that list. Where the passage is marked as listing only some
    entries, change it only as far as needed for it to list nothing outside the new list.
  - Where the passage writes the value in its own way (py310 for 3.10, a table row per entry),
    keep that way of writing.

Where the new value brings in something the passage did not mention (a new entry of a list), the
passage may describe each entry, as it does the others. Take what you write about it from the
reference given with the passage: the other places of the project that state the same thing.
Write nothing about an entry that the reference does not show; leave out a description rather
than make one up.

Give the complete new text of the passage with `rewrite(id, text)`: every character of it, with
the change made. If the passage cannot be made to say this without changing what else it says,
call `cannot(id, why)` instead. Call exactly one of the two for every passage.
"""


def _part_of(text, at):
    """The part of a file's text a place names, as it stands in the file; None if it cannot be
    pointed at there (a JSON part is not: it is read re-serialised)."""
    path, _, part = at.partition("::")
    if not part:
        return text
    try:
        if path.endswith((".md", ".markdown")):
            return _md_section(text, part)
        if path.endswith(".py"):
            return _py_part(text, part)
        if path.endswith(".json"):
            _json_part(text, part)
            return None
    except (ValueError, SyntaxError, KeyError, IndexError, TypeError):
        return None
    return text


def _read_text(text, at):
    """What the kernel reads for a place, out of a file's text (as `locate` does from the file)."""
    path, _, part = at.partition("::")
    try:
        found = (None if not part else _md_section(text, part) if path.endswith((".md", ".markdown"))
                 else _json_part(text, part) if path.endswith(".json") else _py_part(text, part) if path.endswith(".py") else None)
    except (ValueError, SyntaxError, KeyError, IndexError, TypeError):
        found = None
    return text if found is None else found


def serve():
    """The tool server an editing agent answers through."""
    try:  # mcp 2.x
        from mcp.server.mcpserver import MCPServer as FastMCP
    except ImportError:  # mcp 1.x
        from mcp.server.fastmcp import FastMCP
    out = os.environ["PW_EDIT_OUT"]
    mcp = FastMCP("edit")

    def keep(entry):
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry, ensure_ascii=False) + "\n")

    keep({"started": True})

    @mcp.tool()
    def rewrite(id: int, text: str) -> dict:
        """Give the complete new text of passage `id`, with the value changed and nothing else."""
        keep({"id": id, "text": text})
        return {"noted": id}

    @mcp.tool()
    def cannot(id: int, why: str) -> dict:
        """Say that passage `id` cannot be made to state the new value without changing what else it says."""
        keep({"id": id, "cannot": " ".join(why.split())[:400]})
        return {"noted": id}

    mcp.run()


def ask_editor(model, items, budget):
    """One agent with no access to anything, shown the passages. Returns ({id: new text or None}, problems)."""
    work = tempfile.mkdtemp(prefix="pw-edit-")
    out, cfg = os.path.join(work, "edits.jsonl"), os.path.join(work, "mcp.json")
    with open(cfg, "w") as fh:
        json.dump({"mcpServers": {"edit": {"command": sys.executable, "args": ["-P", "-m", "pw.propagate", "--serve"],
                                           "env": {"PW_EDIT_OUT": out, "PYTHONPATH": ROOT}}}}, fh)
    prompt = EDIT
    for i in items:
        part = "   (this passage lists only some of the entries)" if i["some"] else ""
        prompt += (f"\n=== id: {i['id']}   {i['at']}\nThe value: {i['question']}\nIt reads as: {i['reads as']}\n"
                   f"It has to read as: {i['to']}{part}\n")
        for at, text in i.get("reference", []):
            prompt += f"Reference, not to be edited: {at}\n<<<\n{text}\n>>>\n"
        prompt += f"Passage:\n<<<\n{i['unit']}\n>>>\n"
    r = subprocess.run(["claude", "-p", prompt, "--model", model, "--tools", "", "--mcp-config", cfg, "--strict-mcp-config",
                        "--allowedTools", "mcp__edit__rewrite,mcp__edit__cannot", "--output-format", "json", "--max-budget-usd", str(budget)],
                       cwd=work, capture_output=True, text=True)
    lines = []
    if os.path.exists(out):
        with open(out, encoding="utf-8") as fh:
            lines = [json.loads(line) for line in fh]
    problems = [] if any("started" in x for x in lines) else ["the editing tools never started"]
    try:
        info = json.loads(r.stdout)
        if info.get("is_error") or info.get("subtype", "success") != "success":
            problems.append(f"the session ended with {info.get('subtype') or 'an error'}")
        cost = round(info.get("total_cost_usd", 0), 2)
    except ValueError:
        problems.append("the session gave no result")
        cost = 0
    answers = {x["id"]: x.get("text") for x in lines if "id" in x}
    said = {x["id"]: x["cannot"] for x in lines if "cannot" in x}
    return answers, said, problems, cost


def read_back(kernel, lean_dir, files, wanted, model, budget):
    """Have a blind reader read places whose new text an agent proposed. `files` holds the
    proposed text of each file; the reader is shown the place and not what it should say.
    Returns ({(h, place): term it read, or None}, the reading events, cost)."""
    from .maintain import blind_read
    st = kernel.state()
    batches = {}
    for h, at in wanted:
        n = sum(1 for b in batches.values() if any(item[0] == h for item in b))
        decl = next(p for p in st.facts[h]["places"] if p["at"] == at)
        batches.setdefault(n, []).append((h, at, st.facts[h]["type"], question(st.facts[h], decl)[0], context(at, files)))
    tag = _sha(model, "written", str(time.time_ns()))[:6]
    runs = [blind_read(files, lean_dir, model, f"written-{tag}-{n}", batch, budget, db=kernel.db_path) for n, batch in sorted(batches.items())]
    actors = {r["actor"] for r in runs}
    events = [e for e in kernel.events() if e.get("actor") in actors and e["type"] == "reading"]
    return {(e["h"], e["place"]): e["obj"]["text"] for e in events}, events, round(sum(r.get("cost_usd", 0) for r in runs), 2)


def plan(repo, lean_dir, facts, suppose=None, editor=None, reader=None):
    """What writing the instructed (or supposed) values into the files would change.

    Returns {"files": {path: (old text, new text)}, "written": [...], "by hand": [...],
             "refused": [...], "unread": [...], "readings": [...]}.
    Runs against a copy of the record: looking does not touch the project's.

    `editor(items)` proposes new text for places a pattern cannot write (see `ask_editor`);
    `reader(kernel, files, wanted)` reads proposed prose back blind (see `read_back`). Without
    an editor those places are left by hand.
    """
    suppose = suppose or {}
    unknown = sorted(set(suppose) - {f["name"] for f in facts})
    if unknown:
        raise KernelError(f"no declared fact is named {unknown[0]!r}; the names are {sorted(f['name'] for f in facts)}")
    tried = [{**f, "instructions": [*f.get("instructions", []), {"is": suppose[f["name"]], "by": SUPPOSED}]} if f["name"] in suppose else f
             for f in facts]
    work = tempfile.mkdtemp(prefix="pw-propagate-")
    record = os.path.join(work, LOG)
    if os.path.exists(os.path.join(repo, LOG)):
        shutil.copy(os.path.join(repo, LOG), record)
    with open(os.path.join(work, FACTS), "w", encoding="utf-8") as fh:
        json.dump(tried, fh, ensure_ascii=False)
    kernel = Kernel(record, lean_dir=lean_dir, actor="propagate")
    kernel.sync_facts(os.path.join(work, FACTS))
    st = kernel.state()
    out = {"files": {}, "written": [], "by hand": [], "refused": [], "unread": [], "readings": [], "cost_usd": 0}
    texts = {}
    todo = []                                           # places a pattern cannot write: for an agent, if there is one

    def text_of(path):
        if path not in texts:
            with open(os.path.join(repo, path), encoding="utf-8") as fh:
                texts[path] = [fh.read()] * 2          # as it is, and as it would be
        return texts[path]

    for d in kernel.recheck(repo)["decisions"]:
        said = d.get("instructions", [])
        aside = [i for i in said if "set aside" in i]
        if aside:
            # what was supposed, or what people laid down, cannot all hold: nothing follows, so nothing is written
            out["refused"].append({"fact": d["fact"], "instructions": aside, "supposed": any(i["by"] == SUPPOSED for i in aside)})
            continue
        if not said and not d.get("defined"):
            continue
        # what the places are held against: what a person laid down, or what a definition gives
        target = said[0]["is"] if said else d.get("gives")
        source = [] if said else ["the definition from " + ", ".join(d["defined"]["from"])]
        out["unread"] += [{"fact": d["fact"], "at": u["at"], "why": u["why"]} for u in d.get("unread", [])]
        for p in d.get("places", []):
            if not (p.get("against") or p.get("differs from the definition")):
                continue
            if target is None:
                out["by hand"].append({"fact": d["fact"], "at": p["at"], "reads as": p["reads as"], "to": "(what the definition gives)",
                                       "by": source, "why": "Lean did not evaluate the definition to a value that could be written"})
                continue
            decl = next(x for x in st.facts[d["h"]]["places"] if x["at"] == p["at"])
            path = p["at"].partition("::")[0]
            item = {"fact": d["fact"], "at": p["at"], "reads as": p["reads as"], "to": target, "by": p.get("against") or source}
            try:
                if p.get("some"):
                    raise KernelError("it lists some entries: which to take out or rename is not determined by the instruction")
                if not decl["reader"]:
                    raise KernelError("it is read by a reader, not by a pattern")
                old, new = text_of(path)
                part = _part_of(new, p["at"])
                if part is None or new.count(part) != 1:
                    raise KernelError("the part cannot be pointed at in the file as text")
                texts[path][1] = new.replace(part, write_pattern(decl["reader"], part, target))
                out["written"].append({**item, "how": "read back with its pattern"})
            except KernelError as e:
                todo.append({**item, "why": str(e), "h": d["h"], "decl": decl, "some": bool(p.get("some")),
                             "question": question(st.facts[d["h"]], decl)[0]})
    if editor is None:
        out["by hand"] += [{k: v for k, v in t.items() if k not in ("h", "decl", "some", "question")} for t in todo]
    else:
        _by_agent(kernel, repo, lean_dir, st, text_of, texts, todo, out, editor, reader)
    out["files"] = {path: (old, new) for path, (old, new) in texts.items() if old != new}
    return out


def _same(read, target, some=False):
    try:
        a, b = json.loads(read), json.loads(target)
    except ValueError:
        return read == target
    return set(a) <= set(b) if some and isinstance(a, list) and isinstance(b, list) else a == b


def _by_agent(kernel, repo, lean_dir, st, text_of, texts, todo, out, editor, reader):
    """Ask an agent for the new text of each place left, and take what stands up to being read again."""
    declared = [(h, p) for h, f in st.facts.items() if h not in st.withdrawn for p in f["places"]]
    plain = lambda t: {k: v for k, v in t.items() if k not in ("h", "decl", "some", "question", "unit", "id", "new", "reference")}
    while todo:
        batch, seen = [], set()
        for t in list(todo):                             # one place per file at a time: the next is cut from the text as edited
            path = t["at"].partition("::")[0]
            if path in seen:
                continue
            seen.add(path)
            todo.remove(t)
            text = text_of(path)[1]
            part = _part_of(text, t["at"])
            unit = part if part is not None and text.count(part) == 1 else text
            if len(unit) > UNIT:
                out["by hand"].append({**plain(t), "why": t["why"] + f"; and the passage is longer than {UNIT} characters, too long to have rewritten whole"})
                continue
            # what the project already says about this, where it is read by a pattern: for the agent to
            # take names and wording from, so that it does not make up what it was not told
            reference, room = [], 12000
            for p in st.facts[t["h"]]["places"]:
                if p["reader"] and p["at"] != t["at"] and not p.get("some"):
                    ref = _read_text(text_of(p["at"].partition("::")[0])[0], p["at"])
                    if len(ref) <= room:
                        reference.append((p["at"], ref))
                        room -= len(ref)
            batch.append({**t, "unit": unit, "id": len(batch), "reference": reference})
        if not batch:
            continue
        answers, cannot, problems, cost = editor(batch)
        out["cost_usd"] += cost
        blind = []
        for t in batch:
            path = t["at"].partition("::")[0]
            text, new_unit = texts[path][1], answers.get(t["id"])
            try:
                if new_unit is None:
                    raise KernelError("the agent says it cannot be done: " + cannot[t["id"]] if t["id"] in cannot
                                      else "the agent gave no answer" + (f" ({'; '.join(problems)})" if problems else ""))
                if new_unit.rstrip("\n") == t["unit"].rstrip("\n"):
                    raise KernelError("the agent returned the passage unchanged")
                # the passage ends as it ended: the blank lines before the next part are not the agent's to change
                new_unit = new_unit.rstrip("\n") + t["unit"][len(t["unit"].rstrip("\n")):]
                if difflib.SequenceMatcher(None, t["unit"], new_unit).ratio() < 0.6 and abs(len(new_unit) - len(t["unit"])) + 1 > 200:
                    raise KernelError("the agent rewrote the passage instead of changing the value in it")
                new = text.replace(t["unit"], new_unit)
                for h, p in declared:                    # nothing else that is declared in this file may read differently
                    if p["at"].partition("::")[0] != path or (h == t["h"] and p["at"] == t["at"]):
                        continue
                    if p["reader"]:
                        try:
                            before = compute(p["reader"], _read_text(text, p["at"]))
                        except KernelError:
                            continue                     # (it could not be read before either)
                        try:
                            after = compute(p["reader"], _read_text(new, p["at"]))
                        except KernelError as e:
                            raise KernelError(f"afterwards {p['at']} could no longer be read for {st.facts[h]['name']}: {e}")
                        if after != before:
                            raise KernelError(f"afterwards {p['at']} would read as {after[:60]} for {st.facts[h]['name']}, not {before[:60]}")
                    else:
                        for place, m in st.facts[h]["readings"]:
                            q = st.models[m]
                            if place == p["at"] and q.get("anchor") and q.get("quote") and " ".join(q["quote"].split()) in " ".join(_read_text(text, p["at"]).split()) \
                                    and " ".join(q["quote"].split()) not in " ".join(_read_text(new, p["at"]).split()):
                                raise KernelError(f"afterwards the sentence {st.facts[h]['name']} was read from would be gone from {p['at']}")
                if t["decl"]["reader"]:
                    try:
                        back = compute(t["decl"]["reader"], _read_text(new, t["at"]))
                    except KernelError as e:
                        raise KernelError(f"after the agent's edit the place can no longer be read: {e}")
                    if not _same(back, t["to"], t["some"]):
                        raise KernelError(f"after the agent's edit the place reads as {back[:80]}")
                    texts[path][1] = new
                    out["written"].append({**plain(t), "how": "changed by an agent; read back with its pattern"})
                else:
                    blind.append({**t, "new": new})
            except KernelError as e:
                out["by hand"].append({**plain(t), "why": str(e)})
        if blind and reader is None:
            out["by hand"] += [{**plain(t), "why": "an agent proposed a new text, but nobody is set to read it back"} for t in blind]
        elif blind:
            files = tempfile.mkdtemp(prefix="pw-written-")
            for t in blind:                              # the reader is shown the proposed text, in place of the file
                path = t["at"].partition("::")[0]
                os.makedirs(os.path.dirname(os.path.join(files, path)) or files, exist_ok=True)
                with open(os.path.join(files, path), "w", encoding="utf-8") as fh:
                    fh.write(t["new"])
            read, events, cost = reader(kernel, files, [(t["h"], t["at"]) for t in blind])
            out["cost_usd"] += cost
            for t in blind:
                path = t["at"].partition("::")[0]
                got = read.get((t["h"], t["at"]))
                if got is not None and _same(got, t["to"], t["some"]):
                    texts[path][1] = t["new"]
                    out["written"].append({**plain(t), "how": "changed by an agent; read back by a blind reader"})
                    out["readings"] += [e for e in events if (e["h"], e["place"]) == (t["h"], t["at"])]
                else:
                    out["by hand"].append({**plain(t), "why": "an agent proposed a new text, but a blind reader shown it "
                                           + (f"reads {got[:80]}" if got is not None else "did not read the value off it")})


def diff(files):
    lines = lambda text: [line if line.endswith("\n") else line + "\n" for line in text.splitlines(keepends=True)]   # (a last line without a newline)
    return "".join("".join(difflib.unified_diff(lines(old), lines(new), f"a/{path}", f"b/{path}")) for path, (old, new) in sorted(files.items()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--suppose", action="append", default=[], metavar="'FACT NAME=VALUE'",
                    help='try a value nobody has laid down; the value is JSON ("safe", 14, ["a", "b"]) or, failing that, plain text')
    ap.add_argument("--apply", action="store_true", help="write the changes into the files")
    ap.add_argument("--agent", action="store_true",
                    help="for places a pattern cannot write, ask an agent for the new text and have it read back")
    ap.add_argument("--model", default="claude-opus-5-5", help="the model that proposes new text")
    ap.add_argument("--reader-model", default="claude-sonnet-5-5", help="the model that reads proposed prose back, blind")
    ap.add_argument("--budget", type=float, default=3.0)
    ap.add_argument("--serve", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.serve:
        return serve()
    repo = os.path.abspath(args.repo)
    with open(os.path.join(repo, FACTS), encoding="utf-8") as fh:
        facts = json.load(fh)
    suppose = {}
    for s in args.suppose:
        name, eq, value = s.partition("=")
        if not eq:
            ap.error("--suppose takes 'FACT NAME=VALUE'")
        try:
            suppose[name.strip()] = json.loads(value)
        except ValueError:
            suppose[name.strip()] = value.strip()
    if args.agent:
        from .maintain import ready
        ready(own_tools=True)
    editor = (lambda items: ask_editor(args.model, items, args.budget)) if args.agent else None
    reader = (lambda kernel, files, wanted: read_back(kernel, args.lean_dir, files, wanted, args.reader_model, args.budget)) if args.agent else None
    try:
        got = plan(repo, args.lean_dir, facts, suppose, editor, reader)
    except KernelError as e:
        sys.exit(str(e))

    for r in got["refused"]:
        if r["supposed"]:
            mine = next(i for i in r["instructions"] if i["by"] == SUPPOSED)
            others = [i for i in r["instructions"] if i["by"] != SUPPOSED]
            print(f"{r['fact']}: supposing {mine['is']} is against what was laid down by "
                  + ", ".join(f"{i['by']} ({i['is']})" for i in others) + ". Nothing is written for it.")
        else:
            print(f"{r['fact']}: the instructions of {', '.join(i['by'] for i in r['instructions'])} cannot both hold. Nothing is written for it.")
    for u in got["unread"]:
        print(f"{u['fact']}: {u['at']} is not read ({u['why'][:80]}), so nothing can be said about it")
    for w in got["written"]:
        print(f"{w['fact']}: {w['at']}  {w['reads as'][:60]} -> {w['to'][:60]}   (from {', '.join(w['by'])}; {w['how']})")
    for b in got["by hand"]:
        print(f"{b['fact']}: {b['at']} reads as {b['reads as'][:80]} and is left to change by hand to {b['to'][:80]}: {b['why']}")
    if got["files"]:
        print()
        print(diff(got["files"]), end="")
        if args.apply:
            for path, (_, new) in got["files"].items():
                with open(os.path.join(repo, path), "w", encoding="utf-8") as fh:
                    fh.write(new)
            if got["readings"]:                         # what the blind reader read of the new text holds for the files as written
                Kernel(os.path.join(repo, LOG), lean_dir=args.lean_dir, actor="propagate").adopt(got["readings"])
            print(f"\n{len(got['files'])} file(s) written. Then: python -m pw.check" + (" (and pw.maintain for what an agent changed)" if args.agent else ""))
        else:
            print("\nnothing was written (--apply writes these changes)")
    elif not (got["refused"] or got["by hand"] or got["unread"]):
        print("every place already says what was laid down" if any(f.get("instructions") for f in facts) or suppose
              else "no fact has an instruction: there is nothing to write (--suppose tries a value)")
    sys.exit(1 if got["refused"] or got["by hand"] or got["unread"] else 0)


if __name__ == "__main__":
    from .kernel import cli
    cli(main)
