"""Write what was laid down into the places that say otherwise: the check, run in reverse.

    python -m pw.propagate [--repo DIR] [--suppose 'FACT NAME=VALUE' ...] [--apply]

`pw.check` reads the places and holds them against what a person laid down. This goes the other
way: for every fact with an instruction, each place that is against it gets the instructed value
written into it.

  - A place read by a simple pattern (one value found by `find`) is written mechanically: the
    piece the pattern matched is replaced, nothing else. What was written is read back with the
    same pattern and has to read as the instructed value; a write the pattern does not confirm
    is not made.
  - Any other place (a list, a rewritten spelling, prose read by an agent) is not determined by
    its pattern in reverse. It is listed as left to change by hand.

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
import sys
import tempfile

from .check import FACTS
from .kernel import LOG, Kernel, KernelError, _json_part, _md_section, _py_part, write_pattern
from .lean_gate import LEAN_DIR, LeanGate

SUPPOSED = "(supposed)"


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


def plan(repo, lean_dir, facts, suppose=None):
    """What writing the instructed (or supposed) values into the files would change.

    Returns {"files": {path: (old text, new text)}, "written": [...], "by hand": [...],
             "refused": [...], "unread": [...]}.
    Runs against a copy of the record: looking does not touch the project's.
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
    kernel = Kernel(record, gate=LeanGate(lean_dir), actor="propagate")
    kernel.sync_facts(os.path.join(work, FACTS))
    st = kernel.state()
    out = {"files": {}, "written": [], "by hand": [], "refused": [], "unread": []}
    texts = {}

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
        if not said:
            continue
        target = said[0]["is"]
        out["unread"] += [{"fact": d["fact"], "at": u["at"], "why": u["why"]} for u in d.get("unread", [])]
        for p in d.get("places", []):
            if not p.get("against"):
                continue
            decl = next(x for x in st.facts[d["h"]]["places"] if x["at"] == p["at"])
            path = p["at"].partition("::")[0]
            item = {"fact": d["fact"], "at": p["at"], "reads as": p["reads as"], "to": target, "by": p["against"]}
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
                out["written"].append(item)
            except KernelError as e:
                out["by hand"].append({**item, "why": str(e)})
    out["files"] = {path: (old, new) for path, (old, new) in texts.items() if old != new}
    return out


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
    args = ap.parse_args()
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
    try:
        got = plan(repo, args.lean_dir, facts, suppose)
    except KernelError as e:
        sys.exit(str(e))

    for r in got["refused"]:
        if r["supposed"]:
            mine = next(i for i in r["instructions"] if i["by"] == SUPPOSED)
            others = [i for i in r["instructions"] if i["by"] != SUPPOSED]
            print(f"{r['fact']}: supposing {mine['is']} is against what was laid down by "
                  + ", ".join(f"{i['by']} ({i['is']})" for i in others) + " (verified by Lean). Nothing is written for it.")
        else:
            print(f"{r['fact']}: the instructions of {', '.join(i['by'] for i in r['instructions'])} cannot both hold. Nothing is written for it.")
    for u in got["unread"]:
        print(f"{u['fact']}: {u['at']} is not read ({u['why'][:80]}), so nothing can be said about it")
    for w in got["written"]:
        print(f"{w['fact']}: {w['at']}  {w['reads as']} -> {w['to']}   (laid down by {', '.join(w['by'])}; read back with its pattern)")
    for b in got["by hand"]:
        print(f"{b['fact']}: {b['at']} reads as {b['reads as'][:80]} and is left to change by hand to {b['to'][:80]}: {b['why']}")
    if got["files"]:
        print()
        print(diff(got["files"]), end="")
        if args.apply:
            for path, (_, new) in got["files"].items():
                with open(os.path.join(repo, path), "w", encoding="utf-8") as fh:
                    fh.write(new)
            print(f"\n{len(got['files'])} file(s) written. Then: python -m pw.check")
        else:
            print("\nnothing was written (--apply writes these changes)")
    elif not (got["refused"] or got["by hand"] or got["unread"]):
        print("every place already says what was laid down" if any(f.get("instructions") for f in facts) or suppose
              else "no fact has an instruction: there is nothing to write (--suppose tries a value)")
    sys.exit(1 if got["refused"] or got["by hand"] or got["unread"] else 0)


if __name__ == "__main__":
    main()
