//! Measure how well a blind reader reads, by planting changes whose answer is known (pw calibrate).
//!
//! For every place an agent has read, the value it states is replaced in the text of the place by
//! another value of the same kind (another word, another number, a renamed or removed list entry).
//! A blind reader is shown only the changed text, so the right answer is known without anyone
//! judging it:
//!
//!   read      the reader reports the planted value
//!   stuck     the reader reports the value that was there before the change
//!   other     anything else
//!
//! Unchanged texts are mixed in as controls. A decoy is a place of one fact shown with the question
//! of another fact (whose value it does not contain): the right answer is to decline. A passage
//! that says two things (the line repeated with another value) has to be declined too: reading one
//! of the two is "picked". A trial the reader neither read nor declined is "no answer" and is in no
//! rate. Nothing is written to the project's record; the counts are appended to
//! pw-calibration.json with the identity of the instructions the reader was given.
//!
//! A repository with little text cannot supply enough trials for a reader to meet the bar (27
//! planted changes read, all of them, to show a read rate above 0.85). Passages that come with this
//! tool (calibration/passages.json) are used then as well, or alone (--passages): what is measured
//! is the reader, a model with its instructions, and it is measured here, in this repository.
use crate::agent::{self, s, Item};
use crate::kernel::{self, Judge};
use crate::lean::Gate;
use crate::read::locate;
use crate::text;
use crate::util::*;
use serde_json::{json, Map, Value};
use std::path::{Path, PathBuf};

const PASSAGES: &str = include_str!("../calibration/passages.json");

/// A small deterministic generator: the same seed gives the same trials.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    pub fn choice<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
    fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            let j = self.below(i + 1);
            xs.swap(i, j);
        }
    }
}

fn edge(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.'
}

/// Where `tok` occurs in `text` as a whole word (so that `claim` is not found inside `claim_formal`).
fn whole(text: &str, tok: &str) -> Vec<(usize, usize)> {
    if tok.is_empty() {
        return vec![];
    }
    text.match_indices(tok).filter(|(i, _)| {
        let before = text[..*i].chars().next_back().map_or(false, edge);
        let after = text[i + tok.len()..].chars().next().map_or(false, edge);
        !before && !after
    }).map(|(i, _)| (i, i + tok.len())).collect()
}

fn has(text: &str, tok: &str) -> bool {
    !whole(text, tok).is_empty()
}

fn replace_whole(text: &str, tok: &str, new: &str) -> String {
    let mut out = String::new();
    let mut at = 0;
    for (a, b) in whole(text, tok) {
        out.push_str(&text[at..a]);
        out.push_str(new);
        at = b;
    }
    out.push_str(&text[at..]);
    out
}

fn token(v: &Value) -> String {
    v.as_str().map(String::from).unwrap_or_else(|| v.to_string())
}

/// A value of the same kind as `like` that the text does not contain.
fn fresh(like: &Value, text: &str, rng: &mut Rng) -> R<Value> {
    for _ in 0..200 {
        let new = match like {
            Value::Number(n) if n.is_i64() => json!(n.as_i64().unwrap() + *rng.choice(&[1, 2, 3, 5, 7, 10])),
            Value::String(x) if !x.is_empty() && x.chars().all(|c| c.is_ascii_lowercase()) => {
                let (cons, vow) = ("bcdfghjklmnprstvwz".as_bytes(), "aeiou".as_bytes());
                let w: String = (0..(x.len() / 2).max(2)).map(|_| format!("{}{}", *rng.choice(cons) as char, *rng.choice(vow) as char)).collect();
                json!(w.chars().take(x.len().max(3)).collect::<String>())
            }
            other => {
                let c = "bcdfgklmnprst".as_bytes();
                json!(format!("{}_{}{}{}", token(other), *rng.choice(c) as char, *rng.choice("aeiou".as_bytes()) as char, *rng.choice(c) as char))
            }
        };
        if !has(text, &token(&new)) {
            return Ok(new);
        }
    }
    Err("no fresh value found".into())
}

/// Up to n changed versions of `text`, each with the value it now states: (kind, text, planted).
fn mutants(text: &str, value: &Value, rng: &mut Rng, n: usize) -> Vec<(String, String, Value)> {
    let mut out = vec![];
    if let Value::Array(entries) = value {
        let mut present: Vec<&Value> = entries.iter().filter(|e| has(text, &token(e))).collect();
        rng.shuffle(&mut present);
        for e in present {
            if out.len() >= n {
                break;
            }
            let te = token(e);
            let lines: Vec<&str> = text.split_inclusive('\n').filter(|l| has(l, &te)).collect();
            // where the passage also says how many entries there are, taking a row out leaves it at odds with itself
            let alone = lines.len() == 1 && lines[0].trim_start().starts_with('|') && !entries.iter().any(|o| o != e && has(lines[0], &token(o)))
                && !has(text, &entries.len().to_string());
            if alone && out.len() % 2 == 1 {
                let mut rest: Vec<Value> = entries.iter().filter(|x| *x != e).cloned().collect();
                rest.sort_by_key(token);
                out.push(("row removed".into(), text.replacen(lines[0], "", 1), json!(rest)));
            } else if let Ok(new) = fresh(e, text, rng) {
                // the word may also be part of another entry ("blind" in "read blind"): that entry changes with it
                let mut renamed: Vec<Value> = entries.iter().map(|x| match x {
                    Value::String(xs) => json!(replace_whole(xs, &te, &token(&new))),
                    other if other == e => new.clone(),
                    other => other.clone(),
                }).collect();
                renamed.sort_by_key(token);
                out.push(("entry renamed".into(), replace_whole(text, &te, &token(&new)), json!(renamed)));
            }
        }
        return out;
    }
    let tv = token(value);
    if !has(text, &tv) {
        return out;
    }
    let mut seen = vec![];
    while out.len() < n {
        let Ok(new) = fresh(value, text, rng) else { break };
        if seen.contains(&new) {
            break;
        }
        seen.push(new.clone());
        out.push(("value replaced".into(), replace_whole(text, &tv, &token(&new)), new));
    }
    out
}

/// Up to n versions of `text` that say two things: the line stating the value, and right after it
/// the same line with another value. Returns (text, the other value).
fn doubled(text: &str, value: Option<&Value>, rng: &mut Rng, n: usize, span: Option<(usize, usize)>) -> Vec<(String, String)> {
    let span = match (span, value) {
        (Some(sp), _) => sp,
        (None, Some(v)) if !v.is_array() => match whole(text, &token(v)).first() { Some(sp) => *sp, None => return vec![] },
        _ => return vec![],
    };
    let (a, b) = span;
    let start = text[..a].rfind('\n').map_or(0, |i| i + 1);
    let end = text[b..].find('\n').map_or(text.len(), |i| b + i);
    let (line, old) = (&text[start..end], &text[a..b]);
    if line.trim().is_empty() || line.trim_start().starts_with('#') {
        return vec![];                                  // (a heading said twice is two sections, not two claims)
    }
    let (mut out, mut seen): (Vec<(String, String)>, Vec<String>) = (vec![], vec![]);
    for _ in 0..n * 4 {
        if out.len() >= n {
            break;
        }
        let new = if !old.is_empty() && old.chars().all(|c| c.is_ascii_digit()) {
            (old.parse::<i64>().unwrap_or(0) + *rng.choice(&[1, 2, 3, 5, 7, 10])).to_string()
        } else if old.chars().all(|c| c.is_ascii_digit() || c == '.') && old.ends_with(|c: char| c.is_ascii_digit()) {
            let last = old.chars().last().unwrap().to_digit(10).unwrap() as i64;
            format!("{}{}", &old[..old.len() - 1], (last + *rng.choice(&[1, 2, 3, 4])) % 10)
        } else {
            match fresh(&json!(old), text, rng) { Ok(v) => token(&v), Err(_) => continue }
        };
        if new == old || seen.contains(&new) || has(text, &new) {
            continue;
        }
        seen.push(new.clone());
        out.push((format!("{}\n{}{}{}{}", &text[..end], &line[..a - start], new, &line[b - start..], &text[end..]), new));
    }
    out
}

/// Where a pattern finds its one value in a text: (start, end), or None.
fn value_span(rd: &Value, text: &str) -> Option<(usize, usize)> {
    if s(rd, "language") != "pattern" || rd.get("find").and_then(Value::as_str).is_none() || rd.get("rewrite").map_or(false, |r| !r.is_null()) {
        return None;
    }
    let steps: Vec<&str> = rd.get("within").and_then(Value::as_array).into_iter().flatten().filter_map(Value::as_str).chain([s(rd, "find")]).collect();
    let (mut start, mut piece) = (0usize, text);
    for step in steps {
        let found: Vec<_> = crate::read::rx(step).ok()?.captures_iter(piece).collect();
        if found.len() != 1 {
            return None;
        }
        let g = found[0].get(1)?;
        start += g.start();
        piece = &piece[g.start()..g.end()];
    }
    Some((start, start + piece.len()))
}

fn same(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Array(x), Value::Array(y)) => {
            let (mut x, mut y) = (x.clone(), y.clone());
            x.sort_by_key(token);
            y.sort_by_key(token);
            x == y
        }
        _ => a == b,
    }
}

fn trial(fact: &str, asked: &str, typ: &str, place: &str, kind: &str, text: String, planted: Value, before: Value, about: &str) -> Map<String, Value> {
    let mut t = Map::new();
    for (k, v) in [("fact", json!(fact)), ("asked", json!(asked)), ("type", json!(typ)), ("place", json!(place)), ("kind", json!(kind)),
                   ("text", json!(text)), ("planted", planted), ("before", before), ("about", json!(about))] {
        t.insert(k.into(), v);
    }
    t
}

/// A place that states a fact, as a trial can be made from it.
pub struct Source {
    pub fact: String,
    pub asked: String,
    pub typ: String,
    pub place: String,
    pub text: String,
    /// what it states, if a reader stated it; None for a place a pattern reads
    pub value: Option<Value>,
    pub span: Option<(usize, usize)>,
    pub around: Option<String>,
}

/// Per source: the planted changes, then a control, then the passages that say two things; then the decoys.
fn trials(sources: &[Source], per_place: usize, rng: &mut Rng, n_decoys: usize, twice: usize) -> Vec<Map<String, Value>> {
    let mut out = vec![];
    for src in sources {
        match &src.value {
            None => {
                // prose that a pattern reads is also shown to readers: a passage for the "said twice" trials, nothing else
                for (changed, other) in doubled(&src.text, None, rng, twice, src.span) {
                    let mut t = trial(&src.fact, &src.asked, &src.typ, &src.place, "said twice", changed, Value::Null,
                                      json!(&src.text[src.span.unwrap().0..src.span.unwrap().1]), &src.fact);
                    t.insert("other".into(), json!(other));
                    out.push(t);
                }
            }
            Some(value) => {
                let mut made = mutants(&src.text, value, rng, per_place);
                made.push(("unchanged".into(), src.text.clone(), value.clone()));
                for (kind, changed, planted) in made {
                    out.push(trial(&src.fact, &src.asked, &src.typ, &src.place, &kind, changed, planted, value.clone(), &src.fact));
                }
                for (changed, other) in doubled(&src.text, Some(value), rng, twice, None) {
                    let mut t = trial(&src.fact, &src.asked, &src.typ, &src.place, "said twice", changed, Value::Null, value.clone(), &src.fact);
                    t.insert("other".into(), json!(other));
                    out.push(t);
                }
            }
        }
    }
    out.extend(decoys(sources, rng, n_decoys));
    out
}

/// Up to n (place of one fact, question of another) pairs whose right answer is to decline.
fn decoys(sources: &[Source], rng: &mut Rng, n: usize) -> Vec<Map<String, Value>> {
    let file = |at: &str| at.split("::").next().unwrap_or("").to_string();
    let mut found: std::collections::BTreeMap<String, Vec<Map<String, Value>>> = Default::default();
    for a in sources {
        for b in sources.iter().filter(|b| b.fact != a.fact && b.typ == a.typ) {
            let Some(value) = sources.iter().find(|x| x.fact == b.fact && x.value.is_some()).and_then(|x| x.value.clone()) else { continue };
            // (of a list, one entry is enough: a place that names an entry does state part of the thing)
            let stated = match &value { Value::Array(es) => es.iter().any(|e| has(&a.text, &token(e))), v => has(&a.text, &token(v)) };
            let overlap = sources.iter().filter(|q| q.fact == b.fact).any(|q| file(&q.place) == file(&a.place) && (q.text.contains(&a.text) || a.text.contains(&q.text)));
            if stated || overlap {
                continue;                       // the place may well state it: not a decoy
            }
            let mut t = trial(&b.fact, &b.asked, &b.typ, &a.place, "decoy", a.text.clone(), Value::Null, Value::Null, &a.fact);
            t.insert("around".into(), json!(a.around));        // shown as a real reader would be shown it
            found.entry(b.fact.clone()).or_default().push(t);
        }
    }
    for v in found.values_mut() {
        rng.shuffle(v);
    }
    let (mut out, mut used): (Vec<Map<String, Value>>, std::collections::HashMap<String, usize>) = (vec![], Default::default());
    while out.len() < n && found.values().any(|v| !v.is_empty()) {
        for v in found.values_mut() {                    // in turn over the facts asked about, each place at most twice
            if out.len() >= n {
                break;
            }
            if let Some(t) = v.pop() {
                let place = s(&Value::Object(t.clone()), "place").to_string();
                if *used.get(&place).unwrap_or(&0) < 2 {
                    *used.entry(place).or_default() += 1;
                    out.push(t);
                }
            }
        }
    }
    out
}

/// The places of this repository an agent has read (and the prose a pattern reads), as sources of trials.
fn repo_sources(repo: &Path, lean_dir: &Path) -> R<Vec<Source>> {
    let scratch = std::env::temp_dir().join(format!("pw-calibrate-{}", std::process::id()));
    std::fs::create_dir_all(&scratch).map_err(|e| e.to_string())?;
    let db = scratch.join("pw-log.jsonl");
    if repo.join("pw-log.jsonl").exists() {
        std::fs::copy(repo.join("pw-log.jsonl"), &db).map_err(|e| e.to_string())?;       // the project's record is only read
    }
    let judge = Judge { always: false, gate: Gate::new(lean_dir.to_path_buf()) };
    let facts_path = repo.join("pw-facts.json");
    if kernel::needs_lean(&kernel::declared(&facts_path)?, false) {
        judge.gate.usable()?;
    }
    let report = agent::recheck(repo, &db, &facts_path, &judge, "calibrate")?;
    let st = kernel::replay(&db)?;
    let _ = std::fs::remove_dir_all(&scratch);
    let mut out = vec![];
    for d in agent::list(&report, "decisions").iter().filter(|d| !agent::list(d, "places").is_empty() && d.get("unread").is_none()) {
        let fact = st.fact(s(d, "h")).cloned().unwrap_or_default();
        for p in agent::list(d, "places") {
            let at = s(&p, "at").to_string();
            let text = String::from_utf8_lossy(&locate(&at, repo).unwrap_or_default()).into_owned();
            let decl = agent::list(&fact, "places").into_iter().find(|x| s(x, "at") == at).unwrap_or_default();
            let (value, span) = if s(&p, "by") == "stated" {
                match serde_json::from_str::<Value>(s(&p, "reads as")) { Ok(v) => (Some(v), None), Err(_) => continue }
            } else {
                let prose = [".md", ".markdown", ".txt", ".rst"].iter().any(|e| at.split("::").next().unwrap_or("").ends_with(e));
                match decl.get("reader").filter(|_| prose).and_then(|rd| value_span(rd, &text)) { Some(sp) => (None, Some(sp)), None => continue }
            };
            out.push(Source { fact: s(d, "fact").to_string(), asked: s(&p, "question").to_string(), typ: s(&fact, "type").to_string(), place: at.clone(),
                              text, value, span, around: text::context(&at, repo, 300, 8) });
        }
    }
    Ok(out)
}

/// The passages that come with this tool, as sources of trials.
fn bundled() -> Vec<Source> {
    let all: Value = serde_json::from_str(PASSAGES).expect("calibration/passages.json is JSON");
    all.as_array().into_iter().flatten().map(|p| Source {
        fact: format!("{} (bundled)", s(p, "name")),
        asked: format!("{}: {}", s(p, "name"), s(p, "gloss")),
        typ: s(p, "type").to_string(),
        place: s(p, "place").to_string(),
        text: s(p, "text").to_string(),
        value: Some(p["value"].clone()),
        span: None,
        around: None,
    }).collect()
}

/// One blind reader, one scratch project holding one changed text per fact.
fn run_session(lean_dir: &Path, model: &str, budget: f64, number: usize, batch: &mut [Map<String, Value>]) -> (f64, Option<String>) {
    let work = std::env::temp_dir().join(format!("pw-calibrate-{}-{}", std::process::id(), number));
    let _ = std::fs::remove_dir_all(&work);
    let _ = std::fs::create_dir_all(&work);
    let db = work.join("pw-log.jsonl");
    let judge = Judge { always: false, gate: Gate::new(lean_dir.to_path_buf()) };
    let mut items = vec![];
    for (i, t) in batch.iter_mut().enumerate() {
        let tv = Value::Object(t.clone());
        let ext = Path::new(s(&tv, "place").split("::").next().unwrap_or("")).extension().and_then(|e| e.to_str()).map(|e| format!(".{}", e)).unwrap_or(".txt".into());
        let name = format!("passage{}{}", i, ext);
        let _ = std::fs::write(work.join(&name), s(&tv, "text"));
        let h = kernel::with_record(&db, "calibrate", |st| kernel::claim_fact(st, &judge, &format!("trial {}", i), s(&tv, "type"), &[json!(name)], s(&tv, "asked"), &[], None));
        let Ok(h) = h else { continue };
        t.insert("h".into(), json!(h));
        let around = t.remove("around").and_then(|a| a.as_str().map(String::from));
        items.push(Item { h, at: name, typ: s(&tv, "type").to_string(), asked: s(&tv, "asked").to_string(), around, shown: None });
    }
    let run = agent::blind_read(&work, lean_dir, model, &format!("calibrate-{}", number), &items, budget, &db);
    let st = kernel::replay(&db).unwrap_or_default();
    for t in batch.iter_mut() {
        let tv = Value::Object(t.clone());
        let (said, declined) = st.said(s(&tv, "h"));
        let read = said.last().map(|x| serde_json::from_str::<Value>(x).unwrap_or_else(|_| json!(x))).unwrap_or(Value::Null);
        let kind = s(&tv, "kind").to_string();
        let outcome = if read.is_null() {                   // silence is a failed session, not something the reader did
            t.insert("why".into(), json!(declined.last()));
            if declined.is_empty() { "no answer" } else { "declined" }
        } else if kind == "decoy" {
            "accepted"
        } else if kind == "said twice" {
            "picked"
        } else if same(&read, &tv["planted"]) {
            "read"
        } else if kind != "unchanged" && same(&read, &tv["before"]) {
            "stuck"
        } else {
            "other"
        };
        t.insert("read".into(), read);
        t.insert("outcome".into(), json!(outcome));
        t.remove("h");
        t.remove("text");
    }
    let _ = std::fs::remove_dir_all(&work);
    (run.cost, run.error)
}

pub struct CalOpts {
    pub repo: PathBuf,
    pub lean_dir: PathBuf,
    pub model: String,
    pub per_place: usize,
    pub decoys: usize,
    pub twice: usize,
    pub seed: u64,
    pub budget: f64,
    pub parallel: usize,
    /// "auto": this repository's places, and the bundled passages too where those are too few; "repo"; "bundled"
    pub passages: String,
}

/// Planted changes a run has to have for a reader that reads them all to meet the bar (0.85).
pub const ENOUGH: usize = 27;

pub fn calibrate(o: &CalOpts) -> R<i32> {
    agent::ready()?;
    let mut rng = Rng::new(o.seed);
    let mut sources = if o.passages == "bundled" { vec![] } else { repo_sources(&o.repo, &o.lean_dir)? };
    let mut todo = trials(&sources, o.per_place, &mut rng, o.decoys, o.twice);
    let planted_n = |todo: &[Map<String, Value>]| todo.iter().filter(|t| !["unchanged", "decoy", "said twice"].contains(&s(&Value::Object((*t).clone()), "kind"))).count();
    let mut used = if o.passages == "bundled" { "bundled" } else { "repo" };
    if o.passages == "bundled" || (o.passages == "auto" && planted_n(&todo) < ENOUGH) {
        if o.passages == "auto" {
            println!("this repository gives {} planted change(s), fewer than the {} a reader needs to meet the bar: the passages that come with this tool are used as well",
                     planted_n(&todo), ENOUGH);
            used = "repo and bundled";
        }
        sources.extend(bundled());
        let mut rng = Rng::new(o.seed);
        todo = trials(&sources, o.per_place.min(2).max(if o.passages == "bundled" { 2 } else { 1 }), &mut rng, o.decoys, o.twice);
    }
    if todo.is_empty() {
        return Err("no place read by an agent whose value occurs literally in it: nothing to plant (--passages bundled measures on the passages that come with this tool)".into());
    }
    // a reader never sees two versions of one fact, nor one place twice, in a session: at most one
    // trial per fact, counting both the fact asked about and the fact the place belongs to
    let mut sessions: Vec<Vec<Map<String, Value>>> = vec![];
    for t in todo {
        let tv = Value::Object(t.clone());
        let mine = [s(&tv, "fact").to_string(), s(&tv, "about").to_string()];
        let at = sessions.iter().position(|ss| ss.iter().all(|x| { let xv = Value::Object(x.clone()); !mine.contains(&s(&xv, "fact").to_string()) && !mine.contains(&s(&xv, "about").to_string()) }));
        match at { Some(i) => sessions[i].push(t), None => sessions.push(vec![t]) }
    }
    let total: usize = sessions.iter().map(Vec::len).sum();
    let places: std::collections::BTreeSet<String> = sessions.iter().flatten().map(|t| s(&Value::Object(t.clone()), "place").to_string()).collect();
    println!("{} trials on {} place(s), {} blind session(s), {} (at most ${} a session)", total, places.len(), sessions.len(), o.model, agent::cents(o.budget));
    let mut ran: Vec<(f64, Option<String>)> = vec![];
    let mut k = 0;
    for group in sessions.chunks_mut(o.parallel.max(1)) {
        let out: Vec<(f64, Option<String>)> = std::thread::scope(|sc| {
            let hs: Vec<_> = group.iter_mut().enumerate().map(|(j, batch)| {
                let n = k + j;
                sc.spawn(move || run_session(&o.lean_dir, &o.model, o.budget, n, batch))
            }).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        k += group.len();
        ran.extend(out);
    }
    for (_, e) in &ran {
        if let Some(e) = e {
            println!("   a session failed: {}", e.chars().take(200).collect::<String>());
        }
    }
    let todo: Vec<Value> = sessions.into_iter().flatten().map(Value::Object).collect();
    let answered: Vec<&Value> = todo.iter().filter(|t| s(t, "outcome") != "no answer").collect();       // a rate is over the trials answered
    let of = |kinds: &[&str], neg: bool| -> Vec<&Value> { answered.iter().filter(|t| kinds.contains(&s(t, "kind")) != neg).cloned().collect() };
    let planted = of(&["unchanged", "decoy", "said twice"], true);
    let (two, controls, baits) = (of(&["said twice"], false), of(&["unchanged"], false), of(&["decoy"], false));
    let count = |ts: &[&Value], out: &str| ts.iter().filter(|t| s(t, "outcome") == out).count();
    let rate = |k: usize, n: usize| { let (lo, hi) = kernel::interval(k as f64, n as f64); json!([(lo * 1000.0).round() / 1000.0, (hi * 1000.0).round() / 1000.0]) };
    let silent = todo.len() - answered.len();
    let mut summary = Map::new();
    for (k, v) in [
        ("model", json!(o.model)), ("instructions", json!(kernel::instructions_id())), ("date", json!(today())), ("seed", json!(o.seed)),
        ("passages", json!(used)), ("cost_usd", json!((ran.iter().map(|r| r.0).sum::<f64>() * 100.0).round() / 100.0)), ("no answer", json!(silent)),
        ("planted", json!({ "n": planted.len(), "read": count(&planted, "read"), "stuck": count(&planted, "stuck"), "other": count(&planted, "other"), "declined": count(&planted, "declined") })),
        ("unchanged", json!({ "n": controls.len(), "read": count(&controls, "read") })),
        ("decoys", json!({ "n": baits.len(), "declined": count(&baits, "declined"), "accepted": count(&baits, "accepted") })),
        ("twice", json!({ "n": two.len(), "declined": count(&two, "declined"), "picked": count(&two, "picked") })),
    ] {
        summary.insert(k.into(), v);
    }
    if !planted.is_empty() {
        summary.insert("read rate".into(), rate(count(&planted, "read"), planted.len()));
        summary.insert("stuck rate".into(), rate(count(&planted, "stuck"), planted.len()));
    }
    if !baits.is_empty() {
        summary.insert("accept rate".into(), rate(count(&baits, "accepted"), baits.len()));
    }
    if !two.is_empty() {
        summary.insert("pick rate".into(), rate(count(&two, "picked"), two.len()));
    }
    let outcomes = ["read", "stuck", "other", "declined", "accepted", "picked"];
    let kinds: std::collections::BTreeSet<&str> = todo.iter().map(|t| s(t, "kind")).collect();
    println!("\n{:<16} {:>3} {} {:>10}", "kind of trial", "n", outcomes.iter().map(|o| format!("{:>8}", o)).collect::<Vec<_>>().join(" "), "no answer");
    for k in &kinds {
        let ts: Vec<&Value> = todo.iter().filter(|t| s(t, "kind") == *k).collect();
        println!("{:<16} {:>3} {} {:>10}", k, ts.len(), outcomes.iter().map(|o| format!("{:>8}", count(&ts, o))).collect::<Vec<_>>().join(" "), count(&ts, "no answer"));
    }
    let shown = |k: &str| summary.get(k).map(|v| v.to_string().replace(',', ", ")).unwrap_or_default();
    if !planted.is_empty() {
        println!("\nplanted changes read: {}/{}   95% interval for the rate: {}", count(&planted, "read"), planted.len(), shown("read rate"));
        println!("stuck on the old value: {}/{}   95% interval for the rate: {}", count(&planted, "stuck"), planted.len(), shown("stuck rate"));
    }
    if !baits.is_empty() {
        println!("decoys read as if they stated the thing: {}/{}   95% interval for the rate: {}", count(&baits, "accepted"), baits.len(), shown("accept rate"));
    }
    if !two.is_empty() {
        println!("passages saying two things, read as one of them: {}/{}   95% interval for the rate: {}", count(&two, "picked"), two.len(), shown("pick rate"));
    }
    println!("unchanged texts read as before: {}/{}   cost ${}", count(&controls, "read"), controls.len(), agent::cents(summary["cost_usd"].as_f64().unwrap_or(0.0)));
    if silent > 0 {
        println!("{} trial(s) got no answer and are in no rate: the session failed for them", silent);
    }
    for t in &todo {
        let (out, kind) = (s(t, "outcome"), s(t, "kind"));
        if !["read", "declined"].contains(&out) || (out == "declined" && !["decoy", "said twice"].contains(&kind)) {
            println!("   {}: {} ({}, asked: {}) planted {} read {}", out, s(t, "place"), kind, s(t, "fact"),
                     t["planted"].to_string().chars().take(60).collect::<String>(), t.get("read").map(|r| r.to_string()).unwrap_or_default().chars().take(80).collect::<String>());
        }
    }
    // appended to what was measured before: whether a reader counts is decided from all runs together
    let path = o.repo.join("pw-calibration.json");
    let mut runs: Vec<Value> = std::fs::read_to_string(&path).ok().and_then(|t| serde_json::from_str(&t).ok()).unwrap_or_default();
    summary.insert("trials".into(), json!(todo));
    runs.push(Value::Object(summary));
    let mut out = Vec::new();
    let mut ser = serde_json::Serializer::with_formatter(&mut out, serde_json::ser::PrettyFormatter::with_indent(b" "));
    serde::Serialize::serialize(&runs, &mut ser).map_err(|e| e.to_string())?;
    std::fs::write(&path, out).map_err(|e| format!("{}: {}", path.display(), e))?;
    let pooled = text::measurements(&o.repo, Some(&kernel::instructions_id()))?;
    if let Some(m) = pooled.iter().find(|m| s(m, "model") == o.model) {
        let n = |k: &str| m[k].as_i64().unwrap_or(0);
        println!("\nall {} run(s) of {} under the instructions readers are given now, added up:", n("runs"), o.model);
        println!("   planted changes read {}/{}, stuck {}/{}, decoys read {}/{}, one of two values picked {}/{}", n("read"), n("planted"), n("stuck"), n("planted"),
                 n("accepted"), n("decoys"), n("picked"), n("twice"));
        let bounds: Vec<String> = ["read rate", "stuck rate", "accept rate", "pick rate"].iter().filter_map(|k| m.get(*k).map(|v| {
            let r: Vec<f64> = v.as_array().unwrap().iter().map(|x| (x.as_f64().unwrap_or(0.0) * 1000.0).round() / 1000.0).collect();
            format!("{} [{}, {}]", k, r[0], r[1])
        })).collect();
        println!("   95% bounds: {}", bounds.join(", "));
    }
    Ok(0)
}

fn today() -> String {
    let days = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs() / 86400).unwrap_or(0) as i64;
    // civil date from days since 1970-01-01 (Howard Hinnant's algorithm)
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + if m <= 2 { 1 } else { 0 };
    format!("{:04}-{:02}-{:02}", y, m, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn src(fact: &str, typ: &str, place: &str, text: &str, value: Value) -> Source {
        Source { fact: fact.into(), asked: fact.into(), typ: typ.into(), place: place.into(), text: text.into(), value: Some(value), span: None, around: None }
    }

    #[test]
    fn planted_changes_have_known_answers() {
        for seed in 0..20 {
            let mut rng = Rng::new(seed);
            let text = "## Model\n\nThe default class is `pqd`; `pqd` is positive dependence. Not `pqdx`.\nAt most 14 atoms, range 0-15, 114 in total.\n";
            let made = mutants(text, &json!("pqd"), &mut rng, 3);
            assert!(!made.is_empty() && made.len() <= 3 && made.iter().all(|(k, _, _)| k == "value replaced"));
            for (_, changed, planted) in &made {
                let p = planted.as_str().unwrap();
                assert!(p != "pqd" && changed.matches(&format!("`{}`", p)).count() == 2 && changed.contains("`pqdx`") && !changed.contains("`pqd`"));
            }
            let made = mutants(text, &json!(14), &mut rng, 1);
            let (_, changed, planted) = &made[0];
            assert!(planted != &json!(14) && changed.contains(&format!("At most {} atoms", planted)) && changed.contains("114 in total") && changed.contains("0-15"));
            assert!(mutants(text, &json!("frechet"), &mut rng, 3).is_empty());         // not in the words: cannot be planted

            let table = "| `claim(text)` | registers |\n| `prove(r)` | proves |\n| `claim_formal` | other |\n| `status()` | shows |\n";
            for (kind, changed, planted) in mutants(table, &json!(["claim", "prove", "status"]), &mut rng, 3) {
                let p = planted.as_array().unwrap();
                assert!(["entry renamed", "row removed"].contains(&kind.as_str()));
                assert!(p.len() == if kind == "row removed" { 2 } else { 3 } && changed.contains("claim_formal"));
                assert!(p.iter().all(|e| changed.contains(&format!("`{}", e.as_str().unwrap()))));      // every planted entry is in the changed text
            }
            for (_, changed, planted) in mutants("`blind` and `read blind` and `computed`", &json!(["blind", "computed", "read blind"]), &mut rng, 1) {
                let p = planted.as_array().unwrap();
                assert!(p.len() == 3 && p.iter().all(|e| changed.contains(&format!("`{}`", e.as_str().unwrap()))));   // an entry inside another changes with it
            }
        }
        assert!(same(&json!(["b", "a"]), &json!(["a", "b"])) && !same(&json!(["a"]), &json!(["a", "b"])) && same(&json!(14), &json!(14)) && !same(&json!("14"), &json!(14)));
    }

    /// A place that names one entry of a list states part of it: showing it with that list's
    /// question is not a decoy, and a reader who reads the entry off it is right.
    #[test]
    fn a_decoy_is_a_place_that_states_none_of_it() {
        let sources = [
            src("methods", "List String", "methods.md::Methods", "`send`, `receive`.", json!(["receive", "send"])),
            src("methods", "List String", "methods.md::Start", "Call `connect()` first, then `send`.", json!(["send"])),
            src("functions", "List String", "functions.md::Functions", "`connect`, `version`.", json!(["connect", "version"])),
        ];
        let got: Vec<(String, String)> = decoys(&sources, &mut Rng::new(0), 10).iter()
            .map(|t| (t["place"].as_str().unwrap().to_string(), t["fact"].as_str().unwrap().to_string())).collect();
        assert!(!got.contains(&("methods.md::Start".into(), "functions".into())));     // it names `connect`, which is one of the functions
        assert!(got.contains(&("methods.md::Methods".into(), "functions".into())) && got.contains(&("functions.md::Functions".into(), "methods".into())));
    }
}
