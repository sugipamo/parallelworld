//! Look after the places of the facts a project has declared (pw discover).
//!
//!     pw discover [--repo DIR] [--model claude-opus-5-5] [--budget 5] [--apply] [--new]
//!
//! The scope is what has been declared in pw-facts.json. For those facts an agent, which can read
//! files and nothing else, is asked two things:
//!
//!   repair    a declared place that can no longer be read as declared (its file or part was
//!             removed or renamed, its pattern does not find what it should): where is that
//!             statement now?
//!   further   which other places of the repository state the fact, that the declaration misses?
//!
//! What nobody declared is not looked at. Only with --new is the agent also asked to propose things
//! stated in several places that are not declared yet: bringing something into scope is a step of
//! its own, taken on request.
//!
//! The agent reports through tools (`pw mcp` with PW_TOOLS=find), and each report is checked
//! against the files before it is kept: the place has to exist, the quote has to be in it word for
//! word, the value has to be in the quote, and a pattern has to compute the value. What passes is
//! a proposal, not a reading: the agent saw every place at once, so nothing it says about what a
//! place reads as is recorded.
//!
//! Is a proposed place about the same thing? The searcher is the wrong one to ask: it has seen the
//! other places, and a number that happens to be the same looks like the same thing. So every
//! proposed place is shown, alone, to a blind reader with the fact's one-sentence description. A
//! place is kept if that reader reads a value off it (for a place with a pattern: the value the
//! pattern computes). A place the reader says does not state the thing is dropped, with the
//! reader's reason. A place whose reading differs from the other places is kept: that is a finding.
//! The agent may say a declared place is gone for good; taking it out of the declaration is left
//! to a person.
//!
//! A search that failed must not look like a search that found nothing:
//!   - the agent has to say, per fact, that it finished searching; a session that does not is
//!     reported as incomplete, as is one whose tools never started or that ended in an error;
//!   - one known place of each declared fact is left out of what the agent is told. If the search
//!     does not come back with it, the search for that fact is reported as doubtful;
//!   - a proposed place the blind reader neither read nor declined is reported as unanswered and
//!     is not written.
//!
//! With --apply the kept places are written into pw-facts.json and their blind readings are in the
//! record. Without it everything runs against a copy of the record and is only printed. How many
//! missing places this finds was measured by hiding declared ones: experiments/discovery/RESULTS.md.
//! (Ported from pw/discover.py: the same prompts, tools, refusals and printed lines.)
use crate::agent::{self, list, s};
use crate::calibrate::Rng;
use crate::kernel::{self, Judge};
use crate::lean::Gate;
use crate::read::{anchored, compute, json_part, locate, md_section, py_part, reader, rx};
use crate::util::*;
use serde_json::{json, Map, Value};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

const FACTS: &str = "pw-facts.json";
const LOG: &str = "pw-log.jsonl";
const CALIBRATION: &str = "pw-calibration.json";
const OWN: [&str; 3] = [FACTS, LOG, CALIBRATION];      // the list of places, the record and the measurements are not places themselves
const TYPES: [&str; 5] = ["Int", "List Nat", "List String", "Nat", "String"];      // (sorted, as they are named in a refusal)

const HOW: &str = r#"You are looking through a project's files for places that state the same thing, so that the
project can be told when they stop agreeing. You change nothing: you can read files (Read, Grep,
Glob) and report with the tools named below.

What a place is
  A place is where a file states the thing as it is now in this project: a default or constant in
  code, a pinned version in a configuration file, a sentence or table row in documentation that
  says what the value is.
  The test: if the value were changed on purpose, would this place have to change with it for the
  project to stay consistent? If yes, it is a place.
  Not a place: a dated record of what was the case once (results of an experiment, a changelog
  entry, a log), an example that merely happens to use the value, a test's input data.

  A list can also be stated in part. An example configuration uses some of the keys there are; a
  list of highlights names some of the commands. Such a place does not have to list everything,
  but whatever it lists has to exist: report it with `some` set to true, and as its value give
  the entries it mentions. An example that uses a key the code does not know is exactly what
  the project wants to hear about.

How to name a place
  "path" for a whole file, or "path::part" for the smallest part that holds the statement:
    Markdown   the text of a heading, exactly as written, without the #'s    docs/guide.md::3. Limits
    Python     the dotted name of a function, class, method or assignment    app/server.py::Server.__init__
    JSON       a dotted key                                                  package.json::engines.node
  Any other kind of file is named whole.

What to report for a place
  value   what the place says, as JSON: "fast", 14, ["a", "b"]
  quote   the line or sentence of the place that says it, copied character for character
  For code and configuration, also give a pattern that reads the value off the place, so that
  nobody has to read it again:
    find      a regular expression with exactly one group that matches exactly once in the place;
              the group is the value
    find_all  the same, where every match is one entry of a list
    kind      "string", "nat", "int", or "permille" (a decimal such as 0.9, read as 900)
    within    optional: a regular expression with one group that matches exactly once; `find` or
              `find_all` then looks only inside that group. Use it when the place holds several
              things of the same shape and you mean one of them (the choices next to "--format",
              the fields of one struct, the entries of one list).
    rewrite   optional: [pattern, replacement], applied to each piece found. The pattern has to
              match the piece as a whole; the replacement may use \1 ... \9. Use it when the
              place writes the value another way than the other places (["py(\d)(\d+)", "\1.\2"]
              turns py310 into 3.10).
  No look-around, back-references or named groups. Leave the pattern out for prose.
  For a Python or Rust file, a TOML, JSON or YAML file, and a Markdown table, prefer `structure` to a pattern: it reads the
  place by what it is, so quotes, spacing and line breaks do not matter and an entry added in
  another style is still seen. Give it instead of find/find_all, as an object:
    {"python": "value"}     the literal a name is assigned (name the assignment: path::NAME)
    {"python": "strings"}   every string literal in what a name is assigned (a set, a tuple, ...)
    {"python": "keys"}      the keys of the dictionary a name is assigned
    {"python": "names"}     the functions defined directly in the place (a module, or path::Class);
                            add "public": true to leave out _names, "decorator": "app.route" to keep
                            only those carrying that decorator
    {"python": "keyword", "call": "add_argument", "with": "--mode", "keyword": "default"}
                            the literal passed as that keyword to the one such call
    {"data": "package.version"}   a dotted path into a .toml, .json or .yaml file, named whole; a step
                            may be * (every entry) or name[key=value]; add "keys": true for the keys
    {"rust": "value", "item": "LIMIT"}   the literal of a const or static in a .rs file, named whole
                            (inside a mod: "tools::LIMIT"); "strings" for every string literal in an
                            item (macros included; "item": "impl Status" for a type's impl blocks);
                            "names" for an enum's variants, a struct's fields, the items of a mod
                            ("impl Config": the fns of its impls); "fields" for a struct's fields as
                            serde has them (rename applied, skip left out: configuration keys);
                            "arms" for the strings the arms of a match in the item take
    {"table": "Mode"}       every cell of that column of the one table in a Markdown place that has
                            it; with "row": "safe", the one cell of the row whose first cell is safe
  with "as" (string, nat, int, permille), and "sort": true for a list, as needed.
  Read the place that really determines the thing, even if it writes the value differently:
  do not settle for another line that merely happens to spell it the same way.
  Never spell the value itself in the pattern. Write what stands around it, and let the group
  take any value of its kind: "topic == "([a-z.]+)"", not "topic == "(system\.return)"". A pattern
  that fits only the present value cannot tell that the value has changed.

Each report is checked against the file, and you are told what is wrong: fix it and report again.
Ignore pw-facts.json, pw-log.jsonl, pw-calibration.json and anything under .git.
"#;

const FURTHER: &str = r#"
Task. The project has declared the things below, and for each the places known to state it. The
lists may be incomplete. For each thing, search the whole repository for every further place that
states it and report each one with `add_place(fact, at, value, quote, ...)`. Report a place even
if it states a different value from the known ones: that is exactly what the project wants to
hear about. Search for the value itself, for other ways of writing it, and for the words that
describe it; look in documentation, code, configuration and build files alike. Do not report a
place that is already listed. When you have finished searching for a thing, call
`finished(fact, searched)` for it, whether or not you found anything: a thing you do not call
it for counts as not searched. Then reply with one line per thing: how you searched and what
you found.

Declared:
"#;

const REPAIR: &str = r#"
Task. The project declared the things below and where each is stated. Some of those places can
no longer be read as declared: the file or the part was removed or renamed, or the pattern does
not find exactly what it should any more. They are marked CANNOT BE READ. For each of them, find
where that same statement is now and report it with `replace_place(fact, old, at, value, quote, ...)`:
`old` is the place as it is listed, `at` where the statement is now (the same place, if only
the pattern has to change). It has to be the statement that was declared, moved or reworded,
not another one that happens to give the same value. If the project no longer makes that
statement anywhere, say so with `gone(fact, old, why)`; do not put something else in its
place. When you are done with a thing, call `finished(fact, searched)`. Then reply with one
line per place.

Declared:
"#;

const NEW: &str = r#"
Task. Find things this project states in two or more places and has not declared yet, and report
each with `new_fact(name, type, gloss, places)`. Where to look: defaults, limits and thresholds
that documentation describes and code sets; versions pinned in more than one configuration file;
lists (of commands, options, names, states) that documentation enumerates and code defines;
constants copied between files. Report a thing even if its places do not agree right now: that is
exactly what the project wants to hear about. Prefer things whose places could really drift
apart and would mislead someone if they did; leave out anything stated only once.

  name   a short name for the thing
  type   one of String, Nat, Int, List String, List Nat
  gloss  one sentence saying exactly what the value is, precise enough that someone shown a
         single place and nothing else could read the value off it (for a list: what the entries
         are, and that they are sorted). Say what the value is, not how it is used elsewhere:
         each place is shown alone to a reader who has to recognise it as stating this, and
         "the words a response starts with, which the client parses" cannot be checked from
         the one file that defines the words. "the status words of a response" can.
  places at least two, each {"at", "value", "quote"} and, for code and configuration, a pattern

When you have finished, call `finished("", searched)` saying where you looked, whether or not
you found anything, and reply with one line per thing you reported.
"#;

// ---- small things ------------------------------------------------------------------------------

/// The first n characters (Python's s[:n]).
fn cut(text: &str, n: usize) -> String {
    text.chars().take(n).collect()
}

/// Python's truth of a value: null, false, 0, "", [] and {} are false.
fn truthy(v: Option<&Value>) -> bool {
    match v {
        None | Some(Value::Null) => false,
        Some(Value::Bool(b)) => *b,
        Some(Value::Number(n)) => n.as_f64().map_or(true, |x| x != 0.0),
        Some(Value::String(x)) => !x.is_empty(),
        Some(Value::Array(a)) => !a.is_empty(),
        Some(Value::Object(o)) => !o.is_empty(),
    }
}

/// Where a declared place is: a place is "path::part", or {"at": ..., ...}.
fn at_of(p: &Value) -> String {
    p.as_str().map(String::from).unwrap_or_else(|| s(p, "at").to_string())
}

fn places_of(f: &Value) -> Vec<String> {
    list(f, "places").iter().map(at_of).collect()
}

/// A list's entries in one order, for comparing lists as sets with repetition (sorted(a) == sorted(b)).
fn sorted(v: &[Value]) -> Vec<Value> {
    let mut v = v.to_vec();
    v.sort_by_key(|x| x.to_string());
    v
}

fn contains_bytes(hay: &[u8], needle: &[u8]) -> bool {
    needle.is_empty() || hay.windows(needle.len()).any(|w| w == needle)
}

/// A directory of its own for one run of something (several run at once in this process).
fn scratch(prefix: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static N: AtomicUsize = AtomicUsize::new(0);
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
    let dir = std::env::temp_dir().join(format!("{}{}-{}-{}", prefix, std::process::id(), now, N.fetch_add(1, Ordering::SeqCst)));
    let _ = std::fs::create_dir_all(&dir);
    dir
}

fn write_json(path: &Path, v: &Value) -> R<()> {
    std::fs::write(path, pyjson(v, false)).map_err(|e| format!("{}: {}", path.display(), e))
}

// ---- screening a reported place ----------------------------------------------------------------

/// The text a place names. Unlike `locate`, a part that cannot be found is an error.
fn part(at: &str, repo: &Path) -> R<String> {
    let (path, part) = at.split_once("::").unwrap_or((at, ""));
    if path.starts_with('/') || path.split('/').any(|c| c == "..") || path.split('/').next() == Some(".git") || OWN.contains(&path) {
        return Err(format!("{} is not a file of the project that can be a place", path));
    }
    let full = repo.join(path);
    if !full.is_file() {
        return Err(format!("there is no file {}", path));
    }
    let raw = std::fs::read(&full).map_err(|_| format!("there is no file {}", path))?;
    let text = String::from_utf8(raw).map_err(|_| format!("{} is not text", path))?;
    if part.is_empty() {
        return Ok(text);
    }
    let found = if path.ends_with(".md") || path.ends_with(".markdown") {
        let found = md_section(&text, part);
        if found.is_none() {
            let heads: Vec<String> = rx(r"^#+\s+(.*?)\s*#*\s*$")?.captures_iter(&text).take(60).map(|c| c[1].to_string()).collect();
            return Err(format!("{} has no heading {}; its headings are {}", path, pyrepr(part), pylist(&heads)));
        }
        found
    } else if path.ends_with(".json") {
        json_part(&text, part)
    } else if path.ends_with(".py") {
        py_part(&text, part)
    } else {
        return Err(format!("only Markdown, JSON and Python files have parts; name {} whole", path));
    };
    found.ok_or_else(|| format!("{} has no part {}", path, pyrepr(part)))
}

/// The value as data, checked against the fact's type.
fn json_value(typ: &str, value: &Value) -> R<Value> {
    if !TYPES.contains(&typ) {
        return Err(format!("a type is one of {}, not {}", pylist(&TYPES), pyrepr(typ)));
    }
    let mut value = value.clone();
    if let Value::String(text) = &value {
        match serde_json::from_str::<Value>(text) {
            Ok(v) => value = v,
            Err(_) if typ != "String" => {
                return Err(format!("the value has to be JSON of type {}, e.g. {}", typ, if typ.contains("List") { r#"["a", "b"]"# } else { "14" }))
            }
            Err(_) => {}
        }
    }
    let items = value.as_array().cloned().unwrap_or_else(|| vec![value.clone()]);
    let base = typ.strip_prefix("List ").unwrap_or(typ);
    let of_type = |x: &Value| if base == "String" { x.is_string() } else { x.is_i64() || x.is_u64() };
    if value.is_array() != typ.starts_with("List") || !items.iter().all(of_type) {
        return Err(format!("{} is not a value of type {}", cut(&pyjson(&value, false), 80), typ));
    }
    if typ.ends_with("Nat") && items.iter().any(|x| x.as_i64().map_or(false, |n| n < 0)) {
        return Err("a Nat is not negative".into());
    }
    Ok(value)
}

/// Does the pattern still read the place when the value there is another one of its kind?
/// A pattern that spells the value out can only ever find that one value.
fn reads_another(read: &Value, text: &str) -> bool {
    let mut steps: Vec<String> = list(read, "within").iter().filter_map(|x| x.as_str().map(String::from)).collect();
    steps.push(read.get("find").and_then(Value::as_str).filter(|x| !x.is_empty()).unwrap_or_else(|| s(read, "find_all")).to_string());
    let (mut found, mut start) = (text.to_string(), 0usize);
    for step in &steps {
        let Some(g) = rx(step).ok().and_then(|re| re.captures(&found).and_then(|c| c.get(1).map(|g| (g.start(), g.as_str().to_string())))) else {
            return true;                                 // (not for this check to say)
        };
        start += g.0;
        found = g.1;
    }
    let old = found;
    let digits = |x: &str| !x.is_empty() && x.chars().all(|c| c.is_ascii_digit());
    let others: Vec<String> = if digits(&old) {
        let Ok(n) = old.parse::<u128>() else { return true };
        vec![(n + 1).to_string(), (n + 10).to_string()]
    } else if old.chars().last().map_or(false, |c| c.is_ascii_digit()) && old.chars().all(|c| c.is_ascii_digit() || c == '.') {
        let last = old.chars().last().unwrap().to_digit(10).unwrap();
        vec![format!("{}{}", &old[..old.len() - 1], (last + 1) % 10)]
    } else {
        let last = old.chars().last();
        let stem: String = old.chars().take(old.chars().count().saturating_sub(1)).collect();
        let swap = match last { Some(c) if c.is_uppercase() => "Q", Some('q') => "z", _ => "q" };
        let letters: String = old.chars().map(|c| if c.is_ascii_uppercase() { 'Q' } else if c.is_ascii_lowercase() { 'q' } else { c }).collect();
        vec![stem + swap, format!("{}x", old), format!("{}X", old), format!("{}_x", old), format!("{}9", old), letters]
    };
    for new in others {
        let changed = format!("{}{}{}", &text[..start], new, &text[start + old.len()..]);
        let Ok(term) = compute(read, &changed) else { continue };
        if s(read, "as") != "string" {
            return true;
        }
        let want = json!(new);
        match serde_json::from_str::<Value>(&term) {
            Ok(got) if got == want || got.as_array().map_or(false, |a| a.contains(&want)) => return true,
            _ => {}
        }
    }
    false
}

/// How a reported place is to be read: a pattern, or a way of reading by structure.
pub struct How<'a> {
    pub find: &'a str,
    pub find_all: &'a str,
    pub kind: &'a str,
    pub within: &'a Value,
    pub rewrite: &'a Value,
    pub structure: &'a Value,
}

impl<'a> How<'a> {
    fn of(args: &'a Value) -> How<'a> {
        let text = |k: &str| args.get(k).and_then(Value::as_str).unwrap_or("");
        How { find: text("find"), find_all: text("find_all"), kind: text("kind"), within: &args["within"], rewrite: &args["rewrite"], structure: &args["structure"] }
    }
}

/// Check one reported place against the files. Returns the place as pw-facts.json lists it, with
/// the value and quote kept alongside for whoever looks at the proposal.
pub fn screen(repo: &Path, typ: &str, at: &str, value: &Value, quote: &str, how: &How) -> R<Value> {
    let text = part(at, repo)?;
    let value = json_value(typ, value)?;
    if quote.is_empty() || !anchored(quote, at, repo) {
        return Err("the quote is not in the place word for word".into());
    }
    let mut read = Value::Null;
    if truthy(Some(how.structure)) {
        if !how.find.is_empty() || !how.find_all.is_empty() {
            return Err("give a pattern or `structure`, not both".into());
        }
        let Some(structure) = how.structure.as_object() else {
            return Err(r#"`structure` is an object such as {"python": "keys"} or {"data": "package.version"}"#.into());
        };
        let term = reader(how.structure, at).and_then(|rd| compute(&rd, &text))
            .map_err(|e| format!("this way of reading does not work on the place: {}", e.replace(kernel::GATE, "")))?;
        let unparen = regex::Regex::new(r"\((-\d+)\)").unwrap().replace_all(&term, "$1").into_owned();
        let computed: Value = serde_json::from_str(&unparen).map_err(|e| format!("this way of reading does not work on the place: {}", e))?;
        let same = match (&value, &computed) {
            (Value::Array(a), Value::Array(b)) => sorted(a) == sorted(b),
            _ => computed == value,
        };
        if !same {
            return Err(format!("read that way the place gives {}, not the value you gave", cut(&pyjson(&computed, false), 200)));
        }
        let mut kept = structure.clone();
        if computed.is_array() {
            kept.insert("sort".into(), json!(true));      // (a list is compared in one order, as with find_all)
        }
        read = Value::Object(kept);
    } else if !how.find.is_empty() || !how.find_all.is_empty() {
        let kind = if !how.kind.is_empty() { how.kind } else if typ.ends_with("Nat") { "nat" } else if typ == "Int" { "int" } else { "string" };
        // the pattern as the agent gave it, in the form the record keeps (pw/kernel.py pattern())
        let mut given = Map::new();
        if !how.find.is_empty() {
            given.insert("find".into(), json!(how.find));
        }
        if !how.find_all.is_empty() {
            given.insert("find_all".into(), json!(how.find_all));
            given.insert("sort".into(), json!(true));
        }
        given.insert("as".into(), json!(kind));
        if truthy(Some(how.within)) {
            given.insert("within".into(), how.within.clone());
        }
        if truthy(Some(how.rewrite)) {
            given.insert("rewrite".into(), how.rewrite.clone());
        }
        let worked = reader(&Value::Object(given), "(a pattern)").and_then(|rd| {
            let term = compute(&rd, &text)?;
            let term = if s(&rd, "as") == "int" { term.replace(['(', ')'], "") } else { term };
            Ok((rd, serde_json::from_str::<Value>(&term).map_err(|e| e.to_string())?))
        });
        let (rd, computed) = worked.map_err(|e| format!("the pattern does not work on this place: {}", e.replace(kernel::GATE, "")))?;
        let same = match (&value, &computed) {
            (Value::Array(a), Value::Array(b)) => sorted(a) == sorted(b),
            (Value::Array(_), _) => false,
            _ => computed == value,
        };
        if !same {
            return Err(format!("the pattern reads {} off the place, not the value you gave", cut(&pyjson(&computed, false), 200)));
        }
        if !truthy(Some(how.rewrite)) && !reads_another(&rd, &text) {
            return Err("the pattern fits only the value that is there now: were the value to change, the place would count as \
                        unreadable instead of as saying something else. Do not spell the value in the pattern; write what is \
                        around it and let the group take any value of its kind, e.g. \"([a-z.]+)\" or (\\d+)".into());
        }
        let kept: Map<String, Value> = rd.as_object().unwrap().iter()
            .filter(|(k, v)| ["find", "find_all", "as", "within", "rewrite"].contains(&k.as_str()) || (k.as_str() == "sort" && truthy(Some(v))))
            .map(|(k, v)| (k.clone(), v.clone())).collect();
        read = Value::Object(kept);
    } else {
        let items = value.as_array().cloned().unwrap_or_else(|| vec![value.clone()]);
        let where_ = if value.is_array() { text.as_str() } else { quote };
        let missing: Vec<Value> = items.into_iter().filter(|x| !where_.contains(&x.as_str().map(String::from).unwrap_or_else(|| x.to_string()))).collect();
        if !missing.is_empty() {
            return Err(format!("{} does not occur in the {}; a value that has to be computed from the text needs a pattern",
                               cut(&pyjson(&json!(missing), false), 120), if value.is_array() { "place" } else { "quote" }));
        }
    }
    Ok(json!({ "at": at, "read": read, "value": value, "quote": norm(quote) }))
}

/// Do the places state one value (a list in any order)?
pub fn agree(places: &[Value]) -> bool {
    let key = |v: &Value| match v {
        Value::Array(a) => json!(sorted(a)).to_string(),
        other => other.to_string(),
    };
    places.iter().map(|p| key(&p["value"])).collect::<HashSet<_>>().len() == 1
}

/// Screening, as `pw kernel` offers it ({"op": "screen_place", "cwd", "type", "at", "value",
/// "quote", and find, find_all, kind, within, rewrite, structure as an agent gives them}): what
/// the find tools do with a place before they keep it. No record is involved.
pub fn op(req: &Value) -> Option<R<Value>> {
    match s(req, "op") {
        "screen_place" => {
            let cwd = Path::new(req.get("cwd").and_then(Value::as_str).unwrap_or("."));
            Some(screen(cwd, s(req, "type"), s(req, "at"), &req["value"], s(req, "quote"), &How::of(req)))
        }
        _ => None,
    }
}

// ---- the tools the agent reports through -------------------------------------------------------

const FINISHED: &str = r#"Say that you have finished searching: for one declared fact (its name exactly as
listed), or, with `fact` empty, for things not declared yet. `searched` says what you
searched for and where. Call it even when you found nothing."#;

const ADD_PLACE: &str = r#"Report a further place that states a declared fact. `fact` is the fact's name exactly
as listed, `at` the place ("path" or "path::part"), `value` what the place says as JSON
text ("\"fast\"", "14", "[\"a\", \"b\"]"), `quote` the line of the place that says it,
copied character for character. For code and configuration give `find` (or `find_all`
for a list) and `kind` as well, and `within` or `rewrite` where needed; or, for Python, TOML
and JSON, `structure` instead of a pattern. Set `some` for a
place that lists only some entries of a list (an example, an excerpt): `value` is then
the entries it mentions."#;

const REPLACE_PLACE: &str = r#"Report where a declared place that can no longer be read is now. `old` is the place
exactly as listed; `at`, `value`, `quote` and the pattern are as for `add_place`. `at`
may equal `old` when only the pattern has to change."#;

const GONE: &str = r#"Say that a declared place cannot be repaired because the project no longer makes that
statement there or anywhere it moved to. `why` says what happened to it."#;

const NEW_FACT: &str = r#"Report a thing stated in two or more places that is not declared yet. Each place is
{"at": ..., "value": ..., "quote": ...} plus, for code and configuration, "find" or
"find_all" and "kind" (and "within", "rewrite" where needed) or "structure", and "some": true for a place
that lists only some entries of a list. `value` is what that place says, as JSON; places that state different values are
reported as they are. At least one place has to state the whole of it."#;

/// The parameters of a tool, as the Python server's schemas had them: (name, schema, required).
fn params(tool: &str, ps: &[(&str, Value, bool)]) -> Value {
    let title = |n: &str| n.split('_').map(|w| w.chars().take(1).flat_map(char::to_uppercase).chain(w.chars().skip(1)).collect::<String>()).collect::<Vec<_>>().join(" ");
    let mut props = Map::new();
    for (n, schema, _) in ps {
        let mut p = schema.as_object().cloned().unwrap_or_default();
        p.insert("title".into(), json!(title(n)));
        props.insert(n.to_string(), Value::Object(p));
    }
    let required: Vec<&str> = ps.iter().filter(|p| p.2).map(|p| p.0).collect();
    let mut out = Map::new();
    out.insert("properties".into(), Value::Object(props));
    if !required.is_empty() {
        out.insert("required".into(), json!(required));
    }
    out.insert("type".into(), json!("object"));
    out.insert("title".into(), json!(format!("{}Arguments", tool)));
    Value::Object(out)
}

/// The tools a searching agent answers through (PW_TOOLS=find).
pub fn find_tools() -> Value {
    let text = || json!({ "type": "string" });
    let opt_text = || json!({ "default": "", "type": "string" });
    let value = || json!({ "anyOf": [{ "type": "string" }, { "type": "integer" }, { "items": {}, "type": "array" }] });
    let rewrite = || json!({ "anyOf": [{ "items": { "type": "string" }, "type": "array" }, { "type": "null" }], "default": null });
    let structure = || json!({ "anyOf": [{ "additionalProperties": true, "type": "object" }, { "type": "null" }], "default": null });
    let pattern = |some: bool| {
        let mut ps = vec![("find", opt_text(), false), ("find_all", opt_text(), false), ("kind", opt_text(), false)];
        if some {
            ps.push(("some", json!({ "default": false, "type": "boolean" }), false));
        }
        ps.extend([("within", opt_text(), false), ("rewrite", rewrite(), false), ("structure", structure(), false)]);
        ps
    };
    let tool = |name: &str, description: &str, ps: Vec<(&str, Value, bool)>| json!({ "name": name, "description": description, "inputSchema": params(name, &ps) });
    let mut add = vec![("fact", text(), true), ("at", text(), true), ("value", value(), true), ("quote", text(), true)];
    add.extend(pattern(true));
    let mut replace = vec![("fact", text(), true), ("old", text(), true), ("at", text(), true), ("value", value(), true), ("quote", text(), true)];
    replace.extend(pattern(false));
    json!([
        tool("finished", FINISHED, vec![("fact", opt_text(), false), ("searched", opt_text(), false)]),
        tool("add_place", ADD_PLACE, add),
        tool("replace_place", REPLACE_PLACE, replace),
        tool("gone", GONE, vec![("fact", text(), true), ("old", text(), true), ("why", text(), true)]),
        tool("new_fact", NEW_FACT, vec![("name", text(), true), ("type", text(), true), ("gloss", text(), true),
                                        ("places", json!({ "items": { "additionalProperties": true, "type": "object" }, "type": "array" }), true)]),
    ])
}

/// What the tools know while the server runs: the repository, and the facts as the session was
/// told them, with what it has reported since (a place added, a fact proposed), so that the same
/// place is not reported twice and further places can be added to a proposed fact.
struct Find {
    repo: PathBuf,
    facts: Map<String, Value>,
}

fn find_state() -> &'static Mutex<Find> {
    static STATE: OnceLock<Mutex<Find>> = OnceLock::new();
    STATE.get_or_init(|| {
        let repo = PathBuf::from(std::env::var("PW_WORKDIR").unwrap_or_else(|_| ".".into()));
        let told: Value = std::env::var("PW_DISCOVER_FACTS").ok().and_then(|p| std::fs::read_to_string(p).ok())
            .and_then(|t| serde_json::from_str(&t).ok()).unwrap_or(json!([]));
        let facts = told.as_array().into_iter().flatten().map(|f| (s(f, "name").to_string(), f.clone())).collect();
        Mutex::new(Find { repo, facts })
    })
}

fn error(e: impl Into<String>) -> Value {
    json!({ "error": e.into() })
}

/// One tool call: what it says back to the agent. What is kept goes to PW_OUT, one line each.
pub fn call_find(name: &str, args: &Value) -> Value {
    let required: &[&str] = match name {
        "finished" => &[],
        "add_place" => &["fact", "at", "value", "quote"],
        "replace_place" => &["fact", "old", "at", "value", "quote"],
        "gone" => &["fact", "old", "why"],
        "new_fact" => &["name", "type", "gloss", "places"],
        other => return error(format!("ValueError: no tool {}", other)),
    };
    let lacking: Vec<&str> = required.iter().filter(|k| args.get(**k).map_or(true, Value::is_null)).copied().collect();
    if !lacking.is_empty() {
        return error(format!("{} needs {}", name, lacking.join(", ")));
    }
    let mut st = find_state().lock().unwrap_or_else(|e| e.into_inner());
    let st = &mut *st;
    let (repo, facts) = (st.repo.as_path(), &mut st.facts);
    let arg = |k: &str| args.get(k).and_then(Value::as_str).unwrap_or("").to_string();
    let names = |facts: &Map<String, Value>| {
        let mut n: Vec<&String> = facts.keys().collect();
        n.sort();
        pylist(&n)
    };
    let fact = arg("fact");
    let unknown = |facts: &Map<String, Value>| error(format!("no declared fact is named {}; the names are {}", pyrepr(&fact), names(facts)));
    let note = crate::mcp::note;
    match name {
        "finished" => {
            let searched = arg("searched");
            if !fact.is_empty() && !facts.contains_key(&fact) {
                return unknown(facts);
            }
            if searched.trim().is_empty() {
                return error("say what you searched for and where");
            }
            note(&json!({ "finished": fact, "searched": cut(&norm(&searched), 600) }));
            json!({ "noted": if fact.is_empty() { "new facts" } else { fact.as_str() } })
        }
        "add_place" => {
            let Some(f) = facts.get(&fact) else { return unknown(facts) };
            let at = arg("at");
            if places_of(f).contains(&at) {
                return error(format!("{} is already listed for this fact", at));
            }
            let some = args.get("some").and_then(Value::as_bool).unwrap_or(false);
            if some && !s(f, "type").starts_with("List ") {
                return error("only a list can be stated in part");
            }
            let mut place = match screen(repo, s(f, "type"), &at, &args["value"], &arg("quote"), &How::of(args)) {
                Ok(p) => p,
                Err(e) => return error(e),
            };
            place["some"] = json!(some);
            note(&json!({ "fact": fact, "place": place }));
            if let Some(Value::Array(ps)) = facts.get_mut(&fact).and_then(|f| f.get_mut("places")) {
                ps.push(json!(at));
            }
            json!({ "kept": at })
        }
        "replace_place" => {
            let Some(f) = facts.get(&fact) else { return unknown(facts) };
            let (old, at) = (arg("old"), arg("at"));
            let listed = list(f, "places");
            let Some(was) = listed.iter().find(|p| at_of(p) == old) else {
                let mut ats: Vec<String> = listed.iter().map(at_of).collect();
                ats.sort();
                ats.dedup();
                return error(format!("{} is not listed for this fact; its places are {}", old, pylist(&ats)));
            };
            if at != old && listed.iter().any(|p| at_of(p) == at) {
                return error(format!("{} is already listed for this fact", at));
            }
            let some = was.is_object() && truthy(was.get("some"));
            let mut place = match screen(repo, s(f, "type"), &at, &args["value"], &arg("quote"), &How::of(args)) {
                Ok(p) => p,
                Err(e) => return error(e),
            };
            place["some"] = json!(some);
            note(&json!({ "replace": { "fact": fact, "old": old }, "place": place }));
            json!({ "kept": format!("{} -> {}", old, at) })
        }
        "gone" => {
            let Some(f) = facts.get(&fact) else { return unknown(facts) };
            let (old, why) = (arg("old"), arg("why"));
            if !places_of(f).contains(&old) {
                return error(format!("{} is not listed for this fact", old));
            }
            if why.trim().is_empty() {
                return error("say what happened to the statement");
            }
            note(&json!({ "gone": { "fact": fact, "old": old, "why": cut(&norm(&why), 400) } }));
            json!({ "noted": old })
        }
        _ => {
            let (fname, typ, gloss) = (arg("name"), arg("type"), arg("gloss"));
            if facts.contains_key(&fname) {
                return error(format!("{} is already declared; use add_place for further places", pyrepr(&fname)));
            }
            if gloss.trim().is_empty() {
                return error("say in one sentence exactly what the value is");
            }
            let (mut kept, mut wrong) = (vec![], Map::new());
            for p in list(args, "places") {
                let one = || -> R<Value> {
                    let keys: Vec<String> = p.as_object().map(|o| o.keys().cloned().collect()).unwrap_or_default();
                    let mut extra: Vec<&String> = keys.iter().filter(|k| !["at", "value", "quote", "find", "find_all", "kind", "some", "within", "rewrite", "structure"].contains(&k.as_str())).collect();
                    extra.sort();
                    if !extra.is_empty() || !["at", "value", "quote"].iter().all(|k| keys.iter().any(|x| x == k)) {
                        return Err(format!("a place has at, value, quote and optionally find, find_all, kind, within, rewrite, structure, some; not {}", pylist(&extra)));
                    }
                    if truthy(p.get("some")) && !typ.starts_with("List ") {
                        return Err("only a list can be stated in part".into());
                    }
                    let mut place = screen(repo, &typ, s(&p, "at"), &p["value"], s(&p, "quote"), &How::of(&p))?;
                    place["some"] = json!(truthy(p.get("some")));
                    Ok(place)
                };
                match one() {
                    Ok(place) => kept.push(place),
                    Err(e) => {
                        let at = match p.get("at") { Some(Value::String(x)) => x.clone(), None | Some(Value::Null) => "None".into(), Some(other) => other.to_string() };
                        wrong.insert(at, json!(e));
                    }
                }
            }
            if !wrong.is_empty() {
                return json!({ "error": "nothing was kept; fix these places and report the thing again", "places": wrong });
            }
            if kept.iter().map(|p| s(p, "at")).collect::<BTreeSet<_>>().len() < 2 {
                return error("a thing stated in one place has nothing to disagree with; give at least two different places");
            }
            if kept.iter().all(|p| truthy(p.get("some"))) {
                return error("every place is marked as stating only some entries; one place has to state the whole list");
            }
            note(&json!({ "new": { "name": fname, "type": typ, "gloss": norm(&gloss) }, "places": kept }));
            facts.insert(fname.clone(), json!({ "type": typ, "places": kept.iter().map(|p| p["at"].clone()).collect::<Vec<_>>() }));   // further places can be added to it
            let whole: Vec<Value> = kept.iter().filter(|p| !truthy(p.get("some"))).cloned().collect();
            json!({ "kept": fname, "the places that state the whole agree": agree(&whole) })
        }
    }
}

// ---- running the agent -------------------------------------------------------------------------

/// Same file, and one part contains the other.
fn same_place(a: &str, b: &str, repo: &Path) -> bool {
    let file = |x: &str| x.split("::").next().unwrap_or("").to_string();
    if file(a) != file(b) {
        return false;
    }
    match (locate(a, repo), locate(b, repo)) {
        (Some(x), Some(y)) => contains_bytes(&y, &x) || contains_bytes(&x, &y),
        _ => false,
    }
}

/// How one search session went. `problems` is empty only if the tools started, the session ended
/// normally and everything expected was finished: only then does "nothing proposed" mean nothing
/// was found.
struct Search {
    problems: Vec<String>,
    turns: String,
    cost: String,
    controls: Vec<(String, String, bool)>,        // (fact, the place hidden from the agent, did it come back)
}

/// One agent with read access to `repo`. Returns what it proposed and how the session went.
/// `expect` lists what the agent has to say it finished ("" stands for the search for new facts).
fn session(repo: &Path, model: &str, prompt: &str, facts: &[Value], budget: f64, expect: &[String]) -> (Vec<Value>, Search) {
    let work = scratch("pw-discover-");
    let (out, known) = (work.join("proposals.jsonl"), work.join("facts.json"));
    let _ = write_json(&known, &json!(facts));
    let env = [("PW_TOOLS", "find".to_string()), ("PW_OUT", out.display().to_string()), ("PW_WORKDIR", repo.display().to_string()),
               ("PW_DISCOVER_FACTS", known.display().to_string())];
    let (info, raw) = agent::session_reading(prompt, model, budget, &env, &["add_place", "new_fact", "replace_place", "gone", "finished"], Some(repo), &["Read", "Grep", "Glob"]);
    let lines: Vec<Value> = std::fs::read_to_string(&out).unwrap_or_default().lines().filter_map(|l| serde_json::from_str(l).ok()).collect();
    let _ = std::fs::remove_dir_all(&work);
    let proposals: Vec<Value> = lines.iter().filter(|x| ["fact", "new", "replace", "gone"].iter().any(|k| x.get(*k).is_some())).cloned().collect();
    let done: HashSet<String> = lines.iter().filter_map(|x| x.get("finished").map(|f| f.as_str().unwrap_or("").to_string())).collect();
    let mut run = Search { problems: vec![], turns: "None".into(), cost: "None".into(), controls: vec![] };
    if !lines.iter().any(|x| x.get("started").is_some()) {
        run.problems.push("the reporting tools never started, so the agent could not report anything".into());
    }
    match info.filter(Value::is_object) {
        Some(info) => {
            run.turns = info.get("num_turns").map(|t| if t.is_null() { "None".into() } else { t.to_string() }).unwrap_or_else(|| "None".into());
            run.cost = match info.get("total_cost_usd") {
                None => "0".into(),
                Some(c) if c.is_i64() || c.is_u64() => c.to_string(),
                Some(c) => agent::cents(c.as_f64().unwrap_or(0.0)),
            };
            let subtype = info.get("subtype");
            if truthy(info.get("is_error")) || subtype.map_or(false, |x| x.as_str() != Some("success")) {
                run.problems.push(format!("the session ended with {}", subtype.and_then(Value::as_str).filter(|x| !x.is_empty()).unwrap_or("an error")));
            }
        }
        None => {
            let n = raw.chars().count();
            run.problems.push(format!("the session gave no result: {}", raw.chars().skip(n.saturating_sub(300)).collect::<String>()));
        }
    }
    let missing: Vec<&String> = expect.iter().filter(|e| !done.contains(*e)).collect();
    if !missing.is_empty() {
        run.problems.push(format!("the agent did not say it finished searching for: {}",
                                  missing.iter().map(|e| if e.is_empty() { "new facts" } else { e.as_str() }).collect::<Vec<_>>().join(", ")));
    }
    (proposals, run)
}

fn gloss(f: &Value) -> String {
    f.get("gloss").and_then(Value::as_str).filter(|g| !g.is_empty()).unwrap_or(s(f, "name")).to_string()
}

fn listing(facts: &[Value], places: bool) -> String {
    let mut out = String::new();
    for f in facts {
        out += &format!("\n- \"{}\" (type {}): {}\n", s(f, "name"), s(f, "type"), gloss(f));
        if places {
            let known: String = places_of(f).iter().map(|at| format!("    known place: {}\n", at)).collect();
            out += if known.is_empty() { "    known places: none yet\n" } else { &known };
        }
    }
    out
}

/// Search for further places of the declared facts.
///
/// `hide` maps a fact's name to one of its places: that place is left out of what the agent is
/// told, as a control with a known answer. A proposal that names it shows the search works and is
/// not returned; the run's controls say which came back.
fn further(repo: &Path, model: &str, facts: &[Value], budget: f64, hide: &[(String, String)]) -> (Vec<Value>, Search) {
    let hidden = |name: &str| hide.iter().find(|(n, _)| n == name).map(|(_, at)| at.clone());
    let shown: Vec<Value> = facts.iter().map(|f| {
        let mut f = f.clone();
        let gone = hidden(s(&f, "name"));
        let kept: Vec<Value> = list(&f, "places").into_iter().filter(|p| Some(at_of(p)) != gone).collect();
        f["places"] = json!(kept);
        f
    }).collect();
    let names: Vec<String> = facts.iter().map(|f| s(f, "name").to_string()).collect();
    let (proposals, mut run) = session(repo, model, &format!("{}{}{}", HOW, FURTHER, listing(&shown, true)), &shown, budget, &names);
    let back = |p: &Value| p.get("fact").is_some() && hidden(s(p, "fact")).map_or(false, |at| same_place(&at, s(&p["place"], "at"), repo));
    run.controls = hide.iter().map(|(name, at)| (name.clone(), at.clone(), proposals.iter().any(|p| back(p) && s(p, "fact") == name))).collect();
    (proposals.into_iter().filter(|p| !back(p)).collect(), run)
}

/// Look for where declared places that can no longer be read have gone.
/// `broken` is [(fact name, place, why it cannot be read)]. Only the facts concerned are shown.
fn repair(repo: &Path, model: &str, facts: &[Value], broken: &[(String, String, String)], budget: f64) -> (Vec<Value>, Search) {
    let why = |name: &str, at: &str| broken.iter().find(|(n, a, _)| n == name && a == at).map(|b| b.2.clone());
    let shown: Vec<Value> = facts.iter().filter(|f| broken.iter().any(|(n, _, _)| n == s(f, "name"))).cloned().collect();
    let mut text = String::new();
    for f in &shown {
        text += &format!("\n- \"{}\" (type {}): {}\n", s(f, "name"), s(f, "type"), gloss(f));
        for p in list(f, "places") {
            let at = at_of(&p);
            let read = if p.is_object() && truthy(p.get("read")) { format!("   read by: {}", pyjson(&p["read"], false)) } else { String::new() };
            let part = if p.is_object() && truthy(p.get("some")) { "   (states only some entries)" } else { "" };
            text += &match why(s(f, "name"), &at) {
                Some(w) => format!("    CANNOT BE READ: {}\n      listed as: {}{}{}\n", w, at, read, part),
                None => format!("    place: {}{}\n", at, part),
            };
        }
    }
    let names: Vec<String> = shown.iter().map(|f| s(f, "name").to_string()).collect();
    session(repo, model, &format!("{}{}{}", HOW, REPAIR, text), &shown, budget, &names)
}

fn new(repo: &Path, model: &str, facts: &[Value], budget: f64) -> (Vec<Value>, Search) {
    let declared = if facts.is_empty() { String::new() } else { format!("\nAlready declared (do not report these again):\n{}", listing(facts, false)) };
    session(repo, model, &format!("{}{}{}", HOW, NEW, declared), facts, budget, &[String::new()])
}

// ---- what is kept ------------------------------------------------------------------------------

/// A place as pw-facts.json lists it: its name alone, or with its way of reading and "some".
fn entry(place: &Value) -> Value {
    let mut e = Map::new();
    e.insert("at".into(), place["at"].clone());
    if truthy(place.get("read")) {
        e.insert("read".into(), place["read"].clone());
    }
    if truthy(place.get("some")) {
        e.insert("some".into(), json!(true));
    }
    if e.len() > 1 { Value::Object(e) } else { place["at"].clone() }
}

/// The declared facts with the proposals added. Returns (facts, what was added: (fact, place)).
pub fn merge(facts: &[Value], proposals: &[Value]) -> (Vec<Value>, Vec<(String, Value)>) {
    let mut facts = facts.to_vec();
    let mut added: Vec<(String, Value)> = vec![];
    let find = |facts: &[Value], name: &str| facts.iter().rposition(|f| s(f, "name") == name);
    fn put(f: &mut Value, place: &Value, added: &mut Vec<(String, Value)>) {
        if places_of(f).contains(&s(place, "at").to_string()) {
            return;
        }
        if let Some(Value::Array(ps)) = f.get_mut("places") {
            ps.push(entry(place));
        }
        added.push((s(f, "name").to_string(), place.clone()));
    }
    for p in proposals {
        if p.get("gone").is_some() {
            continue;                               // taking a declared place away is for a person
        }
        if let Some(r) = p.get("replace") {
            let Some(i) = find(&facts, s(r, "fact")) else { continue };
            let (place, old) = (&p["place"], s(r, "old"));
            let at = places_of(&facts[i]);
            if let Some(k) = at.iter().position(|x| x == old) {
                if s(place, "at") == old || !at.iter().any(|x| x == s(place, "at")) {
                    facts[i]["places"][k] = entry(place);
                    added.push((s(&facts[i], "name").to_string(), place.clone()));
                }
            }
        } else if p.get("fact").is_some() {
            if let Some(i) = find(&facts, s(p, "fact")) {
                put(&mut facts[i], &p["place"], &mut added);
            }
        } else if let Some(n) = p.get("new") {
            if find(&facts, s(n, "name")).is_some() {
                continue;
            }
            let mut f = n.as_object().cloned().unwrap_or_default();
            f.insert("places".into(), json!([]));
            let mut f = Value::Object(f);
            for place in list(p, "places") {
                put(&mut f, &place, &mut added);
            }
            facts.push(f);
        }
    }
    (facts, added)
}

/// What a blind reader said of a proposed place. `answered` is false where the reader did neither
/// read nor decline, which says nothing about the place.
struct Verdict {
    fact: String,
    at: String,
    kept: bool,
    answered: bool,
    why: String,
}

fn same_term(a: &str, b: &str) -> bool {
    match (serde_json::from_str::<Value>(a), serde_json::from_str::<Value>(b)) {
        (Ok(x), Ok(y)) => x == y,
        _ => norm(a) == norm(b),
    }
}

/// Sync a declaration into a record and hold it against the files, as `actor`; what has to be
/// worked out is not judged without Lean (as `pw kernel`'s recheck).
fn hold(repo: &Path, db: &Path, facts_path: &Path, judge: &Judge) -> R<Value> {
    if kernel::needs_lean(&kernel::declared(facts_path)?, judge.always) {
        judge.gate.usable()?;
    }
    agent::recheck(repo, db, facts_path, judge, "discover")
}

fn decisions(report: &Value) -> HashMap<String, Value> {
    list(report, "decisions").into_iter().map(|d| (s(&d, "fact").to_string(), d)).collect()
}

/// Show every proposed place, alone, to a blind reader, and keep what it reads.
/// Returns (facts with the kept places, one verdict per proposed place, reader sessions).
fn confirm(repo: &Path, lean_dir: &Path, facts: &[Value], proposals: &[Value], model: &str, budget: f64, record: &Path) -> R<(Vec<Value>, Vec<Verdict>, Vec<agent::Run>)> {
    let (merged, added) = merge(facts, proposals);
    if added.is_empty() {
        return Ok((facts.to_vec(), vec![], vec![]));
    }
    let work = scratch("pw-confirm-");
    let path = work.join(FACTS);
    write_json(&path, &json!(merged))?;
    let judge = Judge { always: false, gate: Gate::new(lean_dir.to_path_buf()) };
    let before = decisions(&hold(repo, record, &path, &judge)?);
    let wanted: Vec<(String, String)> = added.iter().map(|(name, place)| (s(&before[name], "h").to_string(), s(place, "at").to_string())).collect();
    let runs = agent::read_blind(repo, lean_dir, record, &wanted, model, "proposed", budget)?;
    let actors: HashSet<&str> = runs.iter().map(|r| r.actor.as_str()).collect();
    let mut said: HashMap<(String, String), Value> = HashMap::new();
    for e in std::fs::read_to_string(record).unwrap_or_default().lines().filter_map(|l| serde_json::from_str::<Value>(l).ok()) {
        if actors.contains(s(&e, "actor")) && ["reading", "decline"].contains(&s(&e, "type")) {
            said.insert((s(&e, "h").to_string(), s(&e, "place").to_string()), e);
        }
    }
    let now = decisions(&hold(repo, record, &path, &judge)?);
    let _ = std::fs::remove_dir_all(&work);
    let mut verdicts = vec![];
    for (name, place) in &added {
        let d = &now[name];
        let at = s(place, "at").to_string();
        let e = said.get(&(s(d, "h").to_string(), at.clone()));
        let mut v = Verdict { fact: name.clone(), at: at.clone(), kept: false, answered: e.is_some(), why: String::new() };
        match e {
            None => v.why = "the blind reader neither read it nor declined: not checked".into(),
            Some(e) if s(e, "type") == "decline" => v.why = format!("a blind reader says the place does not state this: {}", s(e, "why")),
            Some(e) => {
                let read = s(&e["obj"], "text");
                let computed = list(d, "places").into_iter().find(|p| s(p, "at") == at && s(p, "by") == "reader").map(|p| s(&p, "reads as").to_string());
                let agrees = computed.as_deref().map_or(true, |c| same_term(read, c));
                v.kept = agrees;
                v.why = format!("a blind reader reads {} off it{}", cut(read, 80), match &computed {
                    Some(c) if !agrees => format!(", but the pattern computes {}: the pattern is not reading what the place says", cut(c, 80)),
                    _ => String::new(),
                });
            }
        }
        verdicts.push(v);
    }
    let kept: HashSet<(String, String)> = verdicts.iter().filter(|v| v.kept).map(|v| (v.fact.clone(), v.at.clone())).collect();
    let name_of = |p: &Value| if let Some(r) = p.get("replace") { s(r, "fact").to_string() } else { s(p, "fact").to_string() };
    let chosen: Vec<Value> = proposals.iter().filter_map(|p| {
        if let Some(n) = p.get("new") {
            let mut p = p.clone();
            let ps: Vec<Value> = list(&p, "places").into_iter().filter(|q| kept.contains(&(s(n, "name").to_string(), s(q, "at").to_string()))).collect();
            p["places"] = json!(ps);
            Some(p)
        } else if p.get("place").is_some() && kept.contains(&(name_of(p), s(&p["place"], "at").to_string())) {
            Some(p.clone())
        } else {
            None
        }
    }).collect();
    let (mut fin, _) = merge(facts, &chosen);
    let declared: HashSet<&str> = facts.iter().map(|f| s(f, "name")).collect();
    let partial = |p: &Value| p.is_object() && truthy(p.get("some"));
    let lone: Vec<String> = fin.iter().filter(|f| !declared.contains(s(f, "name")) && {
        let ps = list(f, "places");
        ps.len() < 2 || ps.iter().all(partial)
    }).map(|f| s(f, "name").to_string()).collect();
    for name in lone {
        fin.retain(|f| s(f, "name") != name);       // nothing left to compare, or nothing that states the whole of it
        for v in verdicts.iter_mut().filter(|v| v.fact == name && v.kept) {
            v.kept = false;
            v.why += "; but what was kept of this thing is one place, or only places that state it in part";
        }
    }
    Ok((fin, verdicts, runs))
}

/// The declared places that can no longer be read as declared: [(fact name, place, why)].
/// Found by holding the facts against the files, on a copy of the record.
fn broken_places(repo: &Path, lean_dir: &Path, facts: &[Value]) -> R<Vec<(String, String, String)>> {
    let work = scratch("pw-discover-");
    let record = work.join(LOG);
    if repo.join(LOG).exists() {
        std::fs::copy(repo.join(LOG), &record).map_err(|e| format!("{}: {}", LOG, e))?;
    }
    let path = work.join(FACTS);
    write_json(&path, &json!(facts))?;
    let report = hold(repo, &record, &path, &Judge { always: false, gate: Gate::new(lean_dir.to_path_buf()) });
    let _ = std::fs::remove_dir_all(&work);
    Ok(list(&report?, "decisions").iter()
        .flat_map(|d| list(d, "unread").into_iter().filter(|u| truthy(u.get("broken"))).map(move |u| (s(d, "fact").to_string(), s(&u, "at").to_string(), s(&u, "why").to_string())))
        .collect())
}

/// pw-facts.json as Python's json.dump(..., ensure_ascii=False, indent=1) wrote it, and a newline.
fn pretty(v: &Value) -> String {
    use serde::Serialize;
    let mut out = vec![];
    let mut ser = serde_json::Serializer::with_formatter(&mut out, serde_json::ser::PrettyFormatter::with_indent(b" "));
    v.serialize(&mut ser).expect("JSON values serialize");
    String::from_utf8(out).expect("JSON is UTF-8") + "\n"
}

const USAGE: &str = "pw discover [--repo DIR] [--lean-dir DIR] [--model M] [--confirm-model M] [--budget 5] [--new] [--only repair|further|new] [--no-controls] [--seed N] [--apply]";

const HELP: &str = "pw discover: have an agent look after the places of the declared facts

  --repo DIR             the repository (default: .); its pw-facts.json and pw-log.jsonl
  --lean-dir DIR         the Lean project (default: the one next to this tool, or PW_LEAN_DIR)
  --model M              the model that searches (default: claude-opus-5-5)
  --confirm-model M      the model that is shown each proposed place alone; it should be a measured
                         reader (default: claude-sonnet-5-5)
  --budget DOLLARS       per session (default: 5)
  --new                  also have the agent propose things that are not declared yet. Without this,
                         only what is declared is looked after
  --only repair|further|new
                         do one thing only: repair declared places that cannot be read, look for
                         further places of declared facts, or propose new facts
  --no-controls          tell the agent every known place, hiding none as a control
  --seed N               which known places are hidden as controls
  --apply                write the places a blind reader confirmed into pw-facts.json
";

pub fn command(args: &[String]) -> R<i32> {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print!("{}", HELP);
        return Ok(0);
    }
    let (o, rest) = crate::agent_opts(args, USAGE)?;
    let budget = if args.iter().any(|a| a == "--budget") { o.budget } else { 5.0 };
    let (mut want_new, mut only, mut controls, mut seed, mut apply) = (false, None::<String>, true, None::<u64>, false);
    for (k, v) in rest {
        let flag = |on: &mut bool, to: bool| if v.is_empty() { *on = to; Ok(()) } else { Err(format!("unknown argument {}; {}", v, USAGE)) };
        match k.as_str() {
            "--new" => flag(&mut want_new, true)?,
            "--no-controls" => flag(&mut controls, false)?,
            "--apply" => flag(&mut apply, true)?,
            "--only" if ["repair", "further", "new"].contains(&v.as_str()) => only = Some(v),
            "--only" => return Err(format!("--only is one of repair, further, new; {}", USAGE)),
            "--seed" => seed = Some(v.parse::<i64>().map_err(|_| "--seed is a number".to_string())? as u64),
            _ => return Err(format!("unknown argument {}; {}", k, USAGE)),
        }
    }
    agent::ready()?;
    let (repo, lean_dir, model) = (&o.repo, &o.lean_dir, &o.model);
    let path = repo.join(FACTS);
    let facts: Vec<Value> = if path.exists() {
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {}", FACTS, e))?;
        let all: Value = serde_json::from_str(&text).map_err(|e| format!("{} is not JSON: {}", FACTS, e))?;
        all.as_array().cloned().ok_or_else(|| format!("{} is a list of facts: [{{\"name\": ..., \"type\": ..., \"places\": [...]}}, ...]", FACTS))?
    } else {
        vec![]
    };
    let only = only.as_deref();
    want_new = want_new || only == Some("new");
    if facts.is_empty() && !want_new {
        println!("No facts are declared in {}, so there is nothing to look after. With --new the agent proposes some.", FACTS);
        return Ok(0);
    }
    let broken = if !facts.is_empty() && matches!(only, None | Some("repair")) { broken_places(repo, lean_dir, &facts)? } else { vec![] };
    for (name, at, why) in &broken {
        println!("cannot be read as declared: {} at {}: {}", name, at, cut(why, 160));
    }
    let lost: HashSet<(&str, &str)> = broken.iter().map(|(n, a, _)| (n.as_str(), a.as_str())).collect();
    // a known place that can be read, left out as a control
    let mut rng = Rng::new(seed.unwrap_or_else(|| {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos() as u64).unwrap_or(0) ^ std::process::id() as u64
    }));
    let mut hide: Vec<(String, String)> = vec![];
    if controls {
        for f in &facts {
            let good: Vec<String> = places_of(f).into_iter().filter(|at| !lost.contains(&(s(f, "name"), at.as_str()))).collect();
            if good.len() > 1 {
                hide.push((s(f, "name").to_string(), rng.choice(&good).clone()));
            }
        }
    }
    let mut jobs: Vec<&str> = vec![];
    if !broken.is_empty() {
        jobs.push("repair");
    }
    if !facts.is_empty() && matches!(only, None | Some("further")) {
        jobs.push("further");
    }
    if want_new && matches!(only, None | Some("new")) {
        jobs.push("new");
    }
    if jobs.is_empty() {
        println!("nothing to do: every declared place can be read");
        return Ok(0);
    }
    let what = |n: &str| match n { "repair" => "where unreadable places went", "further" => "further places of declared facts", _ => "new facts" };
    println!("looking for {} with {}", jobs.iter().map(|n| what(n)).collect::<Vec<_>>().join(", "), model);
    let ran: Vec<(Vec<Value>, Search)> = std::thread::scope(|sc| {
        let handles: Vec<_> = jobs.iter().map(|job| {
            let (facts, broken, hide) = (&facts, &broken, &hide);
            sc.spawn(move || match *job {
                "repair" => repair(repo, model, facts, broken, budget),
                "further" => further(repo, model, facts, budget, hide),
                _ => new(repo, model, facts, budget),
            })
        }).collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let proposals: Vec<Value> = ran.iter().flat_map(|(ps, _)| ps.iter().cloned()).collect();
    let mut failed = false;
    for (name, (_, run)) in jobs.iter().zip(&ran) {
        println!("   {}: {} turns, ${}", name, run.turns, run.cost);
        for problem in &run.problems {
            failed = true;
            println!("   {}: INCOMPLETE: {}", name, problem);
        }
        if !run.controls.is_empty() {
            let missed: Vec<String> = run.controls.iter().filter(|c| !c.2).map(|(n, at, _)| format!("{} at {}", n, at)).collect();
            println!("   {}: {} of {} hidden known places came back", name, run.controls.len() - missed.len(), run.controls.len());
            for m in missed {
                println!("   {}: the search did not come back with {}: it may have missed other places of that fact too", name, m);
            }
        }
    }

    let was: HashMap<(String, String), String> = proposals.iter().filter_map(|p| p.get("replace").map(|r| ((s(r, "fact").to_string(), s(&p["place"], "at").to_string()), s(r, "old").to_string()))).collect();
    for g in proposals.iter().filter_map(|p| p.get("gone")) {
        println!("\nthe agent says the project no longer states {} at {}: {}\n   taking a declared place away is for a person: remove it from {} if that is so",
                 s(g, "fact"), s(g, "old"), cut(s(g, "why"), 300), FACTS);
    }
    let (_, added) = merge(&facts, &proposals);
    let mut kept: Vec<(String, String)> = vec![];
    if !added.is_empty() {
        let mut record = repo.join(LOG);
        if !apply {                                      // look, but leave the project's record alone
            record = scratch("pw-discover-").join(LOG);
            if repo.join(LOG).exists() {
                std::fs::copy(repo.join(LOG), &record).map_err(|e| format!("{}: {}", LOG, e))?;
            }
        }
        let (fin, verdicts, runs) = confirm(repo, lean_dir, &facts, &proposals, &o.second, budget, &record)?;
        let by: HashMap<(&str, &str), &Verdict> = verdicts.iter().map(|v| ((v.fact.as_str(), v.at.as_str()), v)).collect();
        let declared: HashSet<&str> = facts.iter().map(|f| s(f, "name")).collect();
        let mut names: Vec<&str> = vec![];
        for (n, _) in &added {
            if !names.contains(&n.as_str()) {
                names.push(n);
            }
        }
        for name in names {
            let places: Vec<&Value> = added.iter().filter(|(n, _)| n == name).map(|(_, p)| p).collect();
            println!("\n{}: {}", if declared.contains(name) { "place(s) of" } else { "new fact" }, name);
            for p in &places {
                let v = by[&(name, s(p, "at"))];
                let mark = if v.kept { "keep" } else if v.answered { "drop" } else { "????" };
                let moved = was.get(&(name.to_string(), s(p, "at").to_string())).map(|old| format!("  (instead of {})", old)).unwrap_or_default();
                println!("   {} {}{}  {} {}{}", mark, s(p, "at"), moved, if truthy(p.get("some")) { "lists in part" } else { "says" },
                         cut(&pyjson(&p["value"], false), 100), if truthy(p.get("read")) { "  (computed)" } else { "" });
                println!("        {}", cut(s(p, "quote"), 160));
                println!("        {}", cut(&v.why, 300));
            }
            let whole: Vec<Value> = places.iter().filter(|p| by[&(name, s(p, "at"))].kept && !truthy(p.get("some"))).map(|p| (*p).clone()).collect();
            if !declared.contains(name) && !agree(&whole) {
                println!("   the kept places do not state the same value");
            }
        }
        let unanswered = verdicts.iter().filter(|v| !v.answered).count();
        kept = verdicts.iter().filter(|v| v.kept).map(|v| (v.fact.clone(), v.at.clone())).collect();
        failed = failed || unanswered > 0 || runs.iter().any(|r| r.error.is_some());
        println!("\n{} of {} proposed place(s) kept, {} dropped, {} not checked", kept.len(), verdicts.len(), verdicts.len() - kept.len() - unanswered, unanswered);
        if apply && !kept.is_empty() {
            std::fs::write(&path, pretty(&json!(fin))).map_err(|e| format!("{}: {}", path.display(), e))?;
            let declared = kernel::declared(&path)?;
            let judge = Judge { always: false, gate: Gate::new(lean_dir.clone()) };
            kernel::premises(&declared, &judge, FACTS)?;
            kernel::with_record(&record, "discover", |st| { kernel::sync(st, &declared, FACTS); Ok(()) })?;
            println!("written to {}; their blind readings are in the record. Then: python -m pw.maintain", FACTS);
        } else if !apply {
            println!("nothing was written (--apply writes the kept places to {})", FACTS);
        }
    } else {
        println!("\nnothing proposed{}", if failed { " (but the search was incomplete: this does not mean there is nothing)" } else { "" });
    }
    let repaired: HashSet<(String, String)> = kept.iter().filter_map(|k| was.get(k).map(|old| (k.0.clone(), old.clone()))).collect();
    let still: Vec<&(String, String, String)> = broken.iter().filter(|(n, a, _)| !repaired.contains(&(n.clone(), a.clone()))).collect();
    for (name, at, _) in &still {
        println!("still cannot be read as declared: {} at {}", name, at);
    }
    if failed {
        println!("part of this run failed (marked INCOMPLETE or ???? above): that is not a finding, run it again");
    }
    Ok(if failed || !still.is_empty() { 1 } else { 0 })
}
