"""The names Python uses for the kernel's ways of reading a place, and the constants of a project.

A project states some things in more than one place. A *fact* names such a thing and the places
that state it, and the decision is that all its places read as the same value. That decision, the
record it rests on, the Lean gate and the ways of reading a place are the Rust build's (rust/);
nothing in Python judges, reads a place or writes the record. The functions here ask the build
(`pw kernel`, see pw/core.py) and keep the names the agent tools use:

    pattern, reader          a way of reading, as a declaration describes it, in the form the record keeps
    compute                  what a way of reading reads off a text
    write_pattern            the text with the value a pattern reads replaced (pw propagate)
    locate, subject_id       the content a place names, and the place plus a hash of it
    unreadable, _anchored    why a declared place cannot be found; is a quote in a place
    _md_section, _json_part, _py_part    the part of a text a place names
    excerpt, context         what a blind reader is shown of a long place, and around a small one
    question                 what a reader of a place is asked, and the identity of that question
    reader_measurements, interval        what calibration measured about readers, with its bounds
"""
import hashlib
import os
import sys


class KernelError(Exception):
    pass


def _sha(*parts):
    return hashlib.sha256("\x00".join(parts).encode()).hexdigest()[:10]


LOG = "pw-log.jsonl"     # the record, kept in the repository it is about
RULES = "pw-rules.json"              # a project's own decision about when a reading stands
CALIBRATION = "pw-calibration.json"  # what pw calibrate measured about the readers

# What a blind reader is told. A reader is a model together with these instructions: what was
# measured about a model under other instructions says nothing about this reader.
with open(os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), "pw", "reader.txt"), encoding="utf-8") as _fh:
    READER = _fh.read()
INSTRUCTIONS = _sha(READER)


def cli(main):
    """Run a command; say what is wrong with the declaration or the setup in a line, not a traceback.
    Exit status 2: the check could not be made (1 is for a check that was made and failed)."""
    from .core import GateError
    try:
        main()
    except (KernelError, GateError) as e:
        print(f"pw: {e}", file=sys.stderr)
        sys.exit(2)


def _ask(op, **args):
    from .core import _ask as ask
    return ask("kernel", {"op": op, **args})


# ---- ways of reading -----------------------------------------------------------------------------

def pattern(find=None, find_all=None, kind="string", sort=False, unique=False, within=None, rewrite=None):
    """A way to read a place by a regular expression (see README: `find`, `find_all`, `within`,
    `rewrite`, `as`, `sort`, `unique`), in the form the record keeps."""
    read = {"find": find} if find is not None else {}
    if find_all is not None:
        read["find_all"] = find_all
    read["as"] = kind
    for key, value in (("sort", sort), ("unique", unique), ("within", within), ("rewrite", rewrite)):
        if value:
            read[key] = value
    return _ask("reader", read=read, at="(a pattern)")


def reader(read, at):
    """The way of reading a place that its declaration describes ("read" in pw-facts.json)."""
    return _ask("reader", read=read, at=at)


def compute(rd, text):
    """What a way of reading (in the record's form) reads off a text, as a Lean term."""
    return _ask("compute", reader=rd, text=text)


_read_pattern = compute


def write_pattern(rd, text, term):
    """The text with the value a pattern reads replaced by `term`; what was written has to read back as `term`."""
    return _ask("write_pattern", reader=rd, text=text, term=term)


# ---- places --------------------------------------------------------------------------------------

def locate(subject, cwd):
    """The content a subject (`path` or `path::part`) names, as bytes; None if the file is not there."""
    found = _ask("locate", subject=subject, cwd=cwd)
    return None if found is None else found.encode("utf-8")


def subject_id(subject, cwd):
    return _ask("subject_id", subject=subject, cwd=cwd)


def unreadable(subject, cwd):
    return _ask("unreadable", subject=subject, cwd=cwd)


def _anchored(quote, subject, cwd):
    return _ask("anchored", quote=quote, subject=subject, cwd=cwd)


def _md_section(text, title):
    """The section under the heading `title`, or None."""
    return _ask("part", kind="md", text=text, part=title)


def _json_part(text, keys):
    found = _ask("part", kind="json", text=text, part=keys)
    if found is None:
        raise ValueError(f"{keys} is not in this JSON")
    return found


def _py_part(text, name):
    """The source of a definition or assignment, by dotted name (Class.method), or None."""
    return _ask("part", kind="py", text=text, part=name)


# ---- what a reader is shown and asked ------------------------------------------------------------

def excerpt(rd, text, least=1500):
    """The part of a long place its way of reading looks at, as it stands; None to show the whole place."""
    return _ask("excerpt", reader=rd, text=text, least=least)


def context(subject, cwd, small=300, lines=8):
    """What surrounds a place too small to tell what it belongs to; None otherwise."""
    return _ask("context", subject=subject, cwd=cwd, small=small, lines=lines)


def question(fact, place):
    """What a reader of this place is asked, and the identity of that question."""
    text, asked = _ask("question", fact={k: fact.get(k) for k in ("name", "text", "asked")}, place={"some": bool(place.get("some"))})
    return text, asked


# ---- readers, as measured ------------------------------------------------------------------------

def interval(k, n, level=0.95):
    """Clopper-Pearson interval for a proportion: what the counts allow, with no prior."""
    if level != 0.95:
        raise ValueError("the kernel's intervals are at 95%")
    return tuple(_ask("interval", k=k, n=n))


def reader_measurements(cwd, instructions=INSTRUCTIONS):
    """Per reader model: every measurement made in this repository under the given instructions,
    added up, with the bounds the counts allow. With instructions=None: per (model, instructions)."""
    out = {}
    for m in _ask("measurements", cwd=cwd, instructions=instructions):
        who = m.pop("model") if instructions is not None else (m.pop("model"), m["instructions"])
        m.pop("instructions")
        out[who] = {k: tuple(v) if isinstance(v, list) else v for k, v in m.items()}
    return out
