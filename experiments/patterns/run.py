"""How do the declared patterns hold up when the text around a value is rewritten?

    python experiments/patterns/run.py REPO [REPO ...] [--out FILE]

Every place of a repository's pw-facts.json that is read by a pattern is put through two
kinds of edit, each made on a copy of its file:

  A  rewrites that leave the value as it is (line ends, indentation, quotes, spacing, a
     comment, a commented-out copy of the line, a list joined onto one line or split over
     several, entries in another order, a constant pulled out, Markdown re-wrapped ...).
     The pattern should read the same value. It can instead stop reading the place
     ("loud": the check fails and says the declaration has to be repaired) or read
     another value ("other value": the fact is then reported as violated, a false alarm;
     for a place that states only some entries, it can go unnoticed).

  B  edits that change the value, written the way a later hand might write them: the old
     line commented out and a new one added, or a new entry added to a list in a slightly
     different form. The pattern should read the new value. It can instead be loud, or
     read the old value ("missed": the place changed and the check does not see it).

Where the file's language can be parsed here (Python, TOML, JSON), a rewrite of kind A is
kept only if the file still parses and means the same; other files are not checked, and the
edits made to them are the ones that are plainly harmless (see `SAFE`).
"""
import argparse
import ast
import json
import os
import re
import shutil
import sys
import tempfile
import tomllib
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)

from pw.kernel import KernelError, compute, locate, pattern, reader      # noqa: E402

HASH = (".py", ".toml", ".yml", ".yaml", ".lock", ".sh", ".cfg", ".ini")
SLASH = (".rs", ".js", ".ts", ".go", ".c", ".h", ".java")
SAFE = ("line ends", "trailing comment", "commented-out copy", "blank line", "table padding", "bullets", "re-wrapped", "heading level")


def comment(ext):
    return "#" if ext in HASH else "//" if ext in SLASH else None


def spans(rd, text):
    """Where the pattern matches in `text`: [(start, end)] of whole matches and of the values."""
    start = 0
    for step in rd.get("within", []):
        found = list(re.finditer(step, text, re.M))
        if len(found) != 1:
            return [], []
        a, b = found[0].span(1)
        start, text = start + a, text[a:b]
    found = list(re.finditer(rd.get("find") or rd["find_all"], text, re.M))
    return [(start + m.start(), start + m.end()) for m in found], [(start + m.start(1), start + m.end(1)) for m in found]


def line_spans(text, where):
    """The lines (start, end without the newline) that the given spans touch, in order, once each."""
    out = []
    for a, b in where:
        i = text.rfind("\n", 0, a) + 1
        while True:
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            if (i, j) not in out:
                out.append((i, j))
            if j >= b - 1 or j >= len(text):
                break
            i = j + 1
    return sorted(out)


def per_line(text, lines, change):
    """`text` with `change(line)` applied to each of the given lines (None: leave the line)."""
    for i, j in reversed(lines):
        new = change(text[i:j])
        if new is not None:
            text = text[:i] + new + text[j:]
    return text


def swap_quotes(line):
    if "\\" in line or "'" in line or '"' not in line:
        return None
    return line.replace('"', "'")


def rewrites(P, rd, ext):
    """Kind A: (name, new text of the place) pairs that should leave the value alone."""
    full, groups = spans(rd, P)
    if not full:
        return
    lines = line_spans(P, full)
    c = comment(ext)
    code = ext != ".md" and ext != ".json"
    if code and ext in (".py", ".toml", ".yml", ".yaml"):
        yield "quotes", per_line(P, lines, swap_quotes)
    if code:
        yield "spacing tight", per_line(P, lines, lambda s: re.sub(r" = ", "=", s) if ext not in (".yml", ".yaml") else None)
        yield "spacing wide", per_line(P, lines, lambda s: re.sub(r"(\S) = (\S)", r"\1  =  \2", re.sub(r"(\w): (\S)", r"\1:  \2", s)))
        yield "after colon tight", per_line(P, lines, lambda s: re.sub(r'(["\w]): (\S)', r"\1:\2", s) if ext not in (".yml", ".yaml") else None)
    if c:
        yield "trailing comment", per_line(P, lines, lambda s: s + f"  {c} checked" if s.strip() else None)
        i, j = lines[0]
        pad = re.match(r"\s*", P[i:j]).group(0)
        yield "commented-out copy", P[:i] + f"{pad}{c} {P[i:j].strip()}\n" + P[i:]
    if code:
        yield "blank line", per_line(P, lines, lambda s: "\n" + s)
        if len(lines) > 1 and all(P[i:j].rstrip().endswith(",") for i, j in lines[:-1]):
            a, b = lines[0][0], lines[-1][1]
            body = P[a:b]
            yield "list joined", P[:a] + re.sub(r",\s*\n\s*", ", ", body) + P[b:]
            if rd.get("sort"):
                rows = [P[i:j] for i, j in lines]
                if all(r.rstrip().endswith(",") for r in rows):
                    out = P
                    for (i, j), r in zip(reversed(lines), rows):          # last line gets the first row, and so on
                        out = out[:i] + r + out[j:]
                    yield "entries reversed", out
        for i, j in lines:
            inside = [g for g in groups if i <= g[0] < j]
            if len(inside) > 1 and ", " in P[i:j]:
                pad = re.match(r"\s*", P[i:j]).group(0) + "    "
                yield "list split", P[:i] + P[i:j].replace(", ", f",\n{pad}") + P[j:]
                break
    if ext == ".py" and "find" in rd and len(groups) == 1:
        a, b = groups[0]
        if P[a - 1:a] in ('"', "'") and P[b:b + 1] == P[a - 1:a]:
            a, b = a - 1, b + 1
        i = P.rfind("\n", 0, a) + 1
        pad = re.match(r"\s*", P[i:]).group(0)
        yield "constant pulled out", P[:i] + f"{pad}PW_PULLED_OUT = {P[a:b]}\n" + P[i:a] + "PW_PULLED_OUT" + P[b:]
    if ext == ".md":
        yield "table padding", per_line(P, lines, lambda s: re.sub(r"\s*\|\s*", "|", s) if s.lstrip().startswith("|") else None)
        yield "bullets", re.sub(r"^(\s*)- ", r"\1* ", P, flags=re.M)
        yield "emphasis for code", per_line(P, lines, lambda s: re.sub(r"`([^`]+)`", r"**\1**", s) if "`" in s else None)
        yield "re-wrapped", re.sub(r"([^\n|#>*\-\s][^\n]*[^\n|.。:：])\n(?=[^\n|#>*\-\s`])", r"\1 ", P)
        yield "heading level", re.sub(r"^(#+ )", r"#\1", P, count=1) if P.startswith("#") else P


def other_value(rd, P, span):
    """Another value the pattern can read where it reads `P[span]` now: the first candidate
    that, written in its place, is what the pattern then reads. None if none is."""
    a, b = span
    old = P[a:b]
    if re.fullmatch(r"\d+", old):
        cands = [str(int(old) + 1)]
    elif re.fullmatch(r"[\d.]*\d", old):
        cands = [re.sub(r"\d$", lambda m: str((int(m.group(0)) + 1) % 10), old)]
    else:
        last = old[-1:]
        cands = [old[:-1] + ("Q" if last.isupper() else "q" if last != "q" else "z"), old + "_x", old + "_X", old + "x", old + "X", old + "9"]
    for new in cands:
        try:
            got = json.loads(compute(rd, P[:a] + new + P[b:]))
        except KernelError:
            continue
        if rd.get("rewrite"):
            return new
        want = int(new) if rd["as"] in ("nat", "int") else new
        if rd["as"] == "permille":
            want = int(round(float(new) * 1000))
        if got == want or (isinstance(got, list) and want in got):
            return new
    return None


def changes(P, rd, ext):
    """Kind B: (name, new text of the place, what the new value should be or contain)."""
    full, groups = spans(rd, P)
    if not full:
        return
    c = comment(ext)
    lines = line_spans(P, full[:1])
    i, j = lines[0][0], lines[-1][1]
    block = P[i:j]
    a, b = groups[0][0] - i, groups[0][1] - i
    new = other_value(rd, P, groups[0])
    if new is None:
        return
    renewed = block[:a] + new + block[b:]
    forms = [("", renewed)]
    if swap_quotes(renewed):
        forms.append((", other quotes", swap_quotes(renewed)))
    if " = " in renewed:
        forms.append((", no spaces at =", renewed.replace(" = ", "=")))
    if re.search(r'["\w]: \S', renewed):
        forms.append((", no space after colon", re.sub(r'(["\w]): (\S)', r"\1:\2", renewed)))
    if ext != ".md":
        forms.append((", indented further", re.sub(r"^", "    ", renewed, flags=re.M)))
    if "find" in rd:
        if c:
            pad = re.match(r"\s*", block).group(0)
            old_out = "\n".join(f"{pad}{c} {x.strip()}" for x in block.split("\n"))
            for label, form in forms:
                yield "old line commented out, new line added" + label, P[:i] + old_out + "\n" + form + P[j:], ("is", new)
        for label, form in forms[1:]:
            yield "value changed and the line rewritten" + label, P[:i] + form + P[j:], ("is", new)
    elif len([g for g in groups if i <= g[0] < j]) > 1:        # several entries on the line: the new one goes among them
        g, h = groups[0], groups[1]
        yield "entry added", P[:g[0]] + new + P[g[1]:h[0]] + P[g[0]:], ("has", new)
    else:
        for label, form in forms:
            yield "entry added" + label, P[:j] + "\n" + form + P[j:], ("has", new)
        if block.rstrip().endswith(",") and "\n" not in block:
            yield "entry added on the same line", P[:j] + " " + renewed.strip() + P[j:], ("has", new)


def means(path, text):
    """What a file means, where that can be told here; None where it cannot; raises if it does not parse."""
    if path.endswith(".py"):
        return ast.dump(ast.parse(text))
    if path.endswith(".toml"):
        return tomllib.loads(text)
    if path.endswith(".json"):
        return json.loads(text)
    return None


def read(repo, path, at, rd, text):
    """The value the pattern reads off the place when the file's text is `text`."""
    work = tempfile.mkdtemp(prefix="pw-patterns-")
    try:
        full = os.path.join(work, path)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, "w", encoding="utf-8", newline="") as fh:
            fh.write(text)
        found = locate(at, work)
        return compute(rd, found.decode("utf-8"))
    except (KernelError, AttributeError, UnicodeDecodeError) as e:
        return {"loud": str(e)[:160]}
    finally:
        shutil.rmtree(work, ignore_errors=True)


def trial(repo, fact, place, other=None):
    """`other`: another way of reading the same thing ({"at", "read"}), put through the same edits."""
    at = place["at"]
    path, ext = at.partition("::")[0], os.path.splitext(at.partition("::")[0])[1]
    r = place["read"]
    rd = pattern(r.get("find"), r.get("find_all"), r.get("as", "string"), r.get("sort", False), r.get("unique", False), r.get("within"), r.get("rewrite"))
    with open(os.path.join(repo, path), encoding="utf-8", newline="") as fh:
        F = fh.read()
    P = locate(at, repo).decode("utf-8")
    base = read(repo, path, at, rd, F)
    if isinstance(base, dict):
        return [{"fact": fact["name"], "at": at, "kind": "-", "edit": "as it is", "outcome": "loud", "detail": base["loud"]}]
    rd2 = base2 = None
    if other:
        rd2 = reader(other["read"], other["at"])
        base2 = read(repo, path, other["at"], rd2, F)
        assert not isinstance(base2, dict) and json.loads(base2) == json.loads(base), (at, base, base2)

    def second(text, kind, expect=None):
        """The outcome for the other way of reading, for the same edited text."""
        if rd2 is None:
            return {}
        got = read(repo, path, other["at"], rd2, text)
        if isinstance(got, dict):
            return {"structured": "loud", "structured detail": got["loud"]}
        val, was = json.loads(got), json.loads(base2)
        if kind == "A":
            return {"structured": "same" if val == was else "other value", **({} if val == was else {"structured detail": got[:80]})}
        how, want = expect
        seen = val == want if how == "is" else isinstance(val, list) and want in val
        return {"structured": "seen" if seen else "missed" if val == was else "other value"}

    # (a JSON part is not a piece of the file's text: only the file as a whole is edited then)
    target = F if P == F else P if F.count(P) == 1 else None
    put = (lambda new: new) if P == F else (lambda new: F.replace(P, new))
    row = lambda kind, edit, outcome, **more: {"fact": fact["name"], "at": at, "some": bool(place.get("some")), "kind": kind, "edit": edit, "outcome": outcome, **more}
    out = []
    try:
        meant = means(path, F)
    except Exception:
        meant = None
    cands = list(rewrites(target, rd, ext)) if target is not None else []
    cands.append(("line ends", None))
    if ext in (".py", ".yml", ".yaml", ".toml", ".rs"):
        cands.append(("indentation", None))
    if ext == ".json":
        cands += [("JSON compact", None), ("JSON indented", None), ("JSON keys sorted", None)]
    for name, new in cands:
        if new is None:
            text = {"line ends": lambda: F.replace("\r\n", "\n").replace("\n", "\r\n"),
                    "indentation": lambda: re.sub(r"^( {4})+", lambda m: "  " * (len(m.group(0)) // 4), F, flags=re.M),
                    "JSON compact": lambda: json.dumps(json.loads(F), ensure_ascii=False, separators=(",", ":")),
                    "JSON indented": lambda: json.dumps(json.loads(F), ensure_ascii=False, indent=4),
                    "JSON keys sorted": lambda: json.dumps(json.loads(F), ensure_ascii=False, indent=1, sort_keys=True)}[name]()
        elif new == target:
            continue
        else:
            text = put(new)
        if text == F:
            continue
        try:
            now = means(path, text)
        except Exception:
            continue                                      # the rewrite broke the file: not a rewrite anyone would keep
        if now is None and name not in SAFE:
            verified = False                              # cannot be checked here that the file means the same
        elif now is not None and name != "constant pulled out" and now != meant:
            continue                                      # it changed what the file means: not of kind A
        else:
            verified = True
        got = read(repo, path, at, rd, text)
        if isinstance(got, dict):
            out.append(row("A", name, "loud", detail=got["loud"], verified=verified, **second(text, "A")))
        elif json.loads(got) == json.loads(base):
            out.append(row("A", name, "same", verified=verified, **second(text, "A")))
        else:
            out.append(row("A", name, "other value", detail=f"{base[:70]} -> {got[:70]}", verified=verified, **second(text, "A")))
    for name, new, (how, value) in (changes(target, rd, ext) if target is not None else []):
        text = put(new)
        try:
            means(path, text)
        except Exception:
            continue
        got = read(repo, path, at, rd, text)
        want = int(value) if rd["as"] in ("nat", "int") else int(round(float(value) * 1000)) if rd["as"] == "permille" else value
        if isinstance(got, dict):
            out.append(row("B", name, "loud", detail=got["loud"], **second(text, "B", (how, want))))
            continue
        val, was = json.loads(got), json.loads(base)
        if rd.get("rewrite"):
            seen = val != was
        else:
            seen = val == want if how == "is" else isinstance(val, list) and want in val
        out.append(row("B", name, "seen" if seen else "missed" if val == was else "other value", detail=f"{base[:60]} -> {got[:60]}",
                       **second(text, "B", (how, want))))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("repos", nargs="+")
    ap.add_argument("--structured", metavar="FILE", help='another way of reading some of the places, by structure: {"repo|at[|fact]": {"at", "read"}}; '
                    "it is put through the same edits and reported next to the pattern")
    ap.add_argument("--out")
    args = ap.parse_args()
    alt = {}
    if args.structured:
        with open(args.structured, encoding="utf-8") as fh:
            alt = json.load(fh)
    rows = []
    for repo in map(os.path.abspath, args.repos):
        with open(os.path.join(repo, "pw-facts.json"), encoding="utf-8") as fh:
            facts = json.load(fh)
        for fact in facts:
            for place in fact["places"]:
                if isinstance(place, dict) and "read" in place:
                    name = os.path.basename(repo)
                    other = alt.get(f"{name}|{place['at']}|{fact['name']}") or alt.get(f"{name}|{place['at']}")
                    for r in trial(repo, fact, place, other):
                        rows.append({"repo": os.path.basename(repo), **r})
    for kind, title in (("A", "A: the value is left as it is"), ("B", "B: the value is changed")):
        part = [r for r in rows if r["kind"] == kind]
        tally = Counter((r["edit"].split(",")[0], r["outcome"]) for r in part)
        outcomes = sorted({o for _, o in tally})
        print(f"\n{title}: {len(part)} edits over {len({(r['repo'], r['at'], r['fact']) for r in part})} places")
        print(f"  {'edit':<42}" + "".join(f"{o:>13}" for o in outcomes))
        for edit in sorted({e for e, _ in tally}):
            print(f"  {edit:<42}" + "".join(f"{tally[(edit, o)]:>13}" for o in outcomes))
        print(f"  {'all':<42}" + "".join(f"{sum(1 for r in part if r['outcome'] == o):>13}" for o in outcomes))
    both = [r for r in rows if "structured" in r]
    if both:
        print(f"\nThe {len({(r['repo'], r['at'], r['fact']) for r in both})} places that can also be read by structure, the same edits:")
        for kind in ("A", "B"):
            part = [r for r in both if r["kind"] == kind]
            outcomes = sorted({r["outcome"] for r in part} | {r["structured"] for r in part})
            print(f"  {kind}: {len(part)} edits   " + "".join(f"{o:>13}" for o in outcomes))
            print("     by pattern      " + "".join(f"{sum(1 for r in part if r['outcome'] == o):>13}" for o in outcomes))
            print("     by structure    " + "".join(f"{sum(1 for r in part if r['structured'] == o):>13}" for o in outcomes))
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(rows, fh, ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
