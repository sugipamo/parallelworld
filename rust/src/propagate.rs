//! Write what was laid down into the places that say otherwise: the check, run in reverse (pw propagate).
//!
//! For every fact with an instruction, each place that is against it gets the instructed value;
//! for a definition, a place that does not say what the definition gives gets that value.
//!
//!   - A place read by a simple pattern (one value found by `find`) is written mechanically: the
//!     piece the pattern matched is replaced, nothing else, and read back with the same pattern.
//!   - Any other place is listed as left to change by hand; or, with --agent, an agent is asked for
//!     the new text of that place (shown the passage and the value, with no access to any file).
//!     What it proposes is taken only if it is an edit and not a rewrite, no other declared place
//!     of that file reads differently afterwards, and the place, read again, gives the value: by
//!     its pattern, or by a blind reader shown the new text and not told what to expect.
//!
//! Nothing is written without --apply. --suppose tries a value nobody has laid down: it is held
//! against the instructions like one more instruction, and never becomes one.
use crate::agent::{self, list, s, Item};
use crate::kernel::{self, Judge};
use crate::lean::Gate;
use crate::read::{compute, json_part, md_section, py_part};
use crate::text;
use crate::util::*;
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

pub const SUPPOSED: &str = "(supposed)";
const UNIT: usize = 8000;          // the longest passage an agent is asked to give back whole

const EDIT: &str = "Below are passages from a project's files. Each states a value that has to change. Rewrite each
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
";

/// The part of a file's text a place names, as it stands in the file; None if it cannot be
/// pointed at there (a JSON part is not: it is read re-serialised).
fn part_of(text: &str, at: &str) -> Option<String> {
    let (path, part) = at.split_once("::").unwrap_or((at, ""));
    if part.is_empty() {
        return Some(text.to_string());
    }
    if path.ends_with(".md") || path.ends_with(".markdown") {
        return md_section(text, part);
    }
    if path.ends_with(".py") {
        return py_part(text, part);
    }
    if path.ends_with(".json") {
        return None;
    }
    Some(text.to_string())
}

/// What the kernel reads for a place, out of a file's text (as `locate` does from the file).
fn read_text(text: &str, at: &str) -> String {
    let (path, part) = at.split_once("::").unwrap_or((at, ""));
    let found = if part.is_empty() { None }
        else if path.ends_with(".md") || path.ends_with(".markdown") { md_section(text, part) }
        else if path.ends_with(".json") { json_part(text, part) }
        else if path.ends_with(".py") { py_part(text, part) }
        else { None };
    found.unwrap_or_else(|| text.to_string())
}

/// How much two texts have in common, 0 to 1 (twice the longest common subsequence over both lengths).
fn ratio(a: &str, b: &str) -> f64 {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    if a.is_empty() && b.is_empty() {
        return 1.0;
    }
    let mut prev = vec![0u32; b.len() + 1];
    for x in &a {
        let mut cur = vec![0u32; b.len() + 1];
        for (j, y) in b.iter().enumerate() {
            cur[j + 1] = if x == y { prev[j] + 1 } else { cur[j].max(prev[j + 1]) };
        }
        prev = cur;
    }
    2.0 * prev[b.len()] as f64 / (a.len() + b.len()) as f64
}

fn same(read: &str, target: &str, some: bool) -> bool {
    match (serde_json::from_str::<Value>(read), serde_json::from_str::<Value>(target)) {
        (Ok(Value::Array(a)), Ok(Value::Array(b))) if some => a.iter().all(|x| b.contains(x)),
        (Ok(a), Ok(b)) => a == b,
        _ => read == target,
    }
}

/// A unified diff of the files changed, as `diff -u` writes it (three lines of context).
pub fn diff(files: &BTreeMap<String, (String, String)>) -> String {
    let mut out = String::new();
    for (path, (old, new)) in files {
        let lines = |t: &str| -> Vec<String> { t.split_inclusive('\n').map(|l| if l.ends_with('\n') { l.to_string() } else { format!("{}\n", l) }).collect() };
        let (a, b) = (lines(old), lines(new));
        // the longest common subsequence of lines, as a list of (i, j) matches
        let mut t = vec![vec![0u32; b.len() + 1]; a.len() + 1];
        for i in (0..a.len()).rev() {
            for j in (0..b.len()).rev() {
                t[i][j] = if a[i] == b[j] { t[i + 1][j + 1] + 1 } else { t[i + 1][j].max(t[i][j + 1]) };
            }
        }
        let (mut ops, mut i, mut j) = (vec![], 0, 0);           // (' ' | '-' | '+', line)
        while i < a.len() || j < b.len() {
            if i < a.len() && j < b.len() && a[i] == b[j] { ops.push((' ', i, j)); i += 1; j += 1; }
            else if j < b.len() && (i == a.len() || t[i][j + 1] >= t[i + 1][j]) { ops.push(('+', i, j)); j += 1; }
            else { ops.push(('-', i, j)); i += 1; }
        }
        let changed: Vec<usize> = ops.iter().enumerate().filter(|(_, o)| o.0 != ' ').map(|(k, _)| k).collect();
        if changed.is_empty() {
            continue;
        }
        out.push_str(&format!("--- a/{}\n+++ b/{}\n", path, path));
        let mut k = 0;
        while k < changed.len() {
            let start = changed[k].saturating_sub(3);
            let mut end = changed[k];
            while k + 1 < changed.len() && changed[k + 1] <= end + 7 { k += 1; end = changed[k]; }
            let end = (end + 4).min(ops.len());
            let hunk = &ops[start..end];
            let (a0, b0) = (hunk[0].1, hunk[0].2);
            let (na, nb) = (hunk.iter().filter(|o| o.0 != '+').count(), hunk.iter().filter(|o| o.0 != '-').count());
            let range = |s0: usize, n: usize| if n == 1 { format!("{}", s0 + 1) } else if n == 0 { format!("{},0", s0) } else { format!("{},{}", s0 + 1, n) };
            out.push_str(&format!("@@ -{} +{} @@\n", range(a0, na), range(b0, nb)));
            for (op, i, j) in hunk {
                out.push(*op);
                out.push_str(if *op == '+' { &b[*j] } else { &a[*i] });
            }
            k += 1;
        }
    }
    out
}

/// One agent with no access to anything, shown the passages: ({id: new text}, {id: why not}, problems, cost).
fn ask_editor(model: &str, items: &[Map<String, Value>], budget: f64) -> (HashMap<i64, String>, HashMap<i64, String>, Vec<String>, f64) {
    let out = std::env::temp_dir().join(format!("pw-edit-{}-{}.jsonl", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0)));
    let mut prompt = EDIT.to_string();
    for i in items {
        let v = Value::Object(i.clone());
        let part = if v["some"].as_bool().unwrap_or(false) { "   (this passage lists only some of the entries)" } else { "" };
        prompt += &format!("\n=== id: {}   {}\nThe value: {}\nIt reads as: {}\nIt has to read as: {}{}\n", v["id"], s(&v, "at"), s(&v, "question"), s(&v, "reads as"), s(&v, "to"), part);
        for r in list(&v, "reference") {
            prompt += &format!("Reference, not to be edited: {}\n<<<\n{}\n>>>\n", r[0].as_str().unwrap_or(""), r[1].as_str().unwrap_or(""));
        }
        prompt += &format!("Passage:\n<<<\n{}\n>>>\n", s(&v, "unit"));
    }
    let (info, _) = agent::session(&prompt, model, budget, &[("PW_TOOLS", "edit".into()), ("PW_OUT", out.display().to_string())], &["rewrite", "cannot"], None);
    let lines: Vec<Value> = std::fs::read_to_string(&out).unwrap_or_default().lines().filter_map(|l| serde_json::from_str(l).ok()).collect();
    let _ = std::fs::remove_file(&out);
    let mut problems = vec![];
    if !lines.iter().any(|x| x.get("started").is_some()) {
        problems.push("the editing tools never started".to_string());
    }
    let cost = match &info {
        Some(i) => {
            if i.get("is_error").and_then(Value::as_bool).unwrap_or(false) || i.get("subtype").and_then(Value::as_str).map_or(false, |x| x != "success") {
                problems.push(format!("the session ended with {}", i.get("subtype").and_then(Value::as_str).unwrap_or("an error")));
            }
            i.get("total_cost_usd").and_then(Value::as_f64).unwrap_or(0.0)
        }
        None => { problems.push("the session gave no result".into()); 0.0 }
    };
    let id = |x: &Value| x.get("id").and_then(Value::as_i64);
    let answers = lines.iter().filter_map(|x| Some((id(x)?, x.get("text")?.as_str()?.to_string()))).collect();
    let cannot = lines.iter().filter_map(|x| Some((id(x)?, x.get("cannot")?.as_str()?.to_string()))).collect();
    (answers, cannot, problems, cost)
}

/// Have a blind reader read places whose new text an agent proposed. `files` holds the proposed
/// text of each file; the reader is shown the place and not what it should say.
fn read_back(db: &Path, lean_dir: &Path, files: &Path, wanted: &[(String, String)], model: &str, budget: f64) -> R<(HashMap<(String, String), String>, Vec<Value>, f64)> {
    let st = kernel::replay(db)?;
    let mut batches: Vec<Vec<Item>> = vec![];
    for (h, at) in wanted {
        let fact = st.fact(h).ok_or_else(|| format!("{} is not a fact", h))?;
        let decl = list(fact, "places").into_iter().find(|p| s(p, "at") == at).unwrap_or_default();
        let item = Item { h: h.clone(), at: at.clone(), typ: s(fact, "type").to_string(), asked: text::question(fact, &decl).0, around: text::context(at, files, 300, 8), shown: None };
        let n = batches.iter().filter(|b| b.iter().any(|i| i.h == *h)).count();
        if n == batches.len() { batches.push(vec![]); }
        batches[n].push(item);
    }
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0).to_string();
    let tag = sha(&[model, "written", &now])[..6].to_string();
    let mut cost = 0.0;
    let mut actors = vec![];
    for (n, batch) in batches.iter().enumerate() {
        let actor = format!("written-{}-{}", tag, n);
        cost += agent::blind_read(files, lean_dir, model, &actor, batch, budget, db).cost;
        actors.push(actor);
    }
    let events: Vec<Value> = std::fs::read_to_string(db).unwrap_or_default().lines().filter_map(|l| serde_json::from_str::<Value>(l).ok())
        .filter(|e| s(e, "type") == "reading" && actors.contains(&s(e, "actor").to_string())).collect();
    let read = events.iter().map(|e| ((s(e, "h").to_string(), s(e, "place").to_string()), e["obj"]["text"].as_str().unwrap_or("").to_string())).collect();
    Ok((read, events, (cost * 100.0).round() / 100.0))
}

pub struct Agents {
    pub editor: String,
    pub reader: String,
    pub budget: f64,
}

/// What writing the instructed (or supposed) values into the files would change:
/// {"files": {path: [old, new]}, "written", "by hand", "refused", "unread", "readings", "cost_usd"}.
/// Runs against a copy of the record: looking does not touch the project's.
pub fn plan(repo: &Path, lean_dir: &Path, facts: &[Value], suppose: &Map<String, Value>, agents: Option<&Agents>) -> R<Value> {
    let names: Vec<&str> = facts.iter().map(|f| s(f, "name")).collect();
    if let Some(unknown) = suppose.keys().find(|k| !names.contains(&k.as_str())) {
        let mut sorted: Vec<&str> = names.clone();
        sorted.sort();
        return Err(format!("no declared fact is named {}; the names are {}", pyrepr(unknown), pylist(&sorted)));
    }
    let tried: Vec<Value> = facts.iter().map(|f| match suppose.get(s(f, "name")) {
        Some(v) => { let mut f = f.clone(); let mut said = list(&f, "instructions"); said.push(json!({ "is": v, "by": SUPPOSED })); f["instructions"] = json!(said); f }
        None => f.clone(),
    }).collect();
    let work = std::env::temp_dir().join(format!("pw-propagate-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0)));
    std::fs::create_dir_all(&work).map_err(|e| e.to_string())?;
    let db = work.join("pw-log.jsonl");
    if repo.join("pw-log.jsonl").exists() {
        std::fs::copy(repo.join("pw-log.jsonl"), &db).map_err(|e| e.to_string())?;
    }
    std::fs::write(work.join("pw-facts.json"), serde_json::to_string(&tried).unwrap()).map_err(|e| e.to_string())?;
    let judge = Judge { always: false, gate: Gate::new(lean_dir.to_path_buf()) };
    let report = agent::recheck(repo, &db, &work.join("pw-facts.json"), &judge, "propagate")?;
    let st = kernel::replay(&db)?;
    let mut texts: BTreeMap<String, (String, String)> = BTreeMap::new();
    let text_of = |path: &str, texts: &mut BTreeMap<String, (String, String)>| -> String {
        texts.entry(path.to_string()).or_insert_with(|| { let t = std::fs::read_to_string(repo.join(path)).unwrap_or_default(); (t.clone(), t) }).1.clone()
    };
    let (mut written, mut by_hand, mut refused, mut unread) = (vec![], vec![], vec![], vec![]);
    let mut todo: Vec<Map<String, Value>> = vec![];
    for d in list(&report, "decisions") {
        let said = list(&d, "instructions");
        let aside: Vec<Value> = said.iter().filter(|i| i.get("set aside").is_some()).cloned().collect();
        if !aside.is_empty() {
            // what was supposed, or what people laid down, cannot all hold: nothing follows, so nothing is written
            refused.push(json!({ "fact": s(&d, "fact"), "instructions": aside, "supposed": aside.iter().any(|i| s(i, "by") == SUPPOSED) }));
            continue;
        }
        if said.is_empty() && d.get("defined").is_none() {
            continue;
        }
        // what the places are held against: what a person laid down, or what a definition gives
        let target = if let Some(i) = said.first() { json!(s(i, "is")) } else { d.get("gives").cloned().unwrap_or(Value::Null) };
        let source: Vec<String> = if said.is_empty() {
            vec![format!("the definition from {}", list(&d["defined"], "from").iter().filter_map(Value::as_str).collect::<Vec<_>>().join(", "))]
        } else { vec![] };
        for u in list(&d, "unread") {
            unread.push(json!({ "fact": s(&d, "fact"), "at": s(&u, "at"), "why": s(&u, "why") }));
        }
        for p in list(&d, "places") {
            if p.get("against").is_none() && p.get("differs from the definition").is_none() {
                continue;
            }
            let by = p.get("against").cloned().unwrap_or(json!(source));
            let Some(to) = target.as_str() else {
                by_hand.push(json!({ "fact": s(&d, "fact"), "at": s(&p, "at"), "reads as": s(&p, "reads as"), "to": "(what the definition gives)",
                                     "by": source, "why": "Lean did not evaluate the definition to a value that could be written" }));
                continue;
            };
            let fact = st.fact(s(&d, "h")).cloned().unwrap_or_default();
            let decl = list(&fact, "places").into_iter().find(|x| s(x, "at") == s(&p, "at")).unwrap_or_default();
            let path = s(&p, "at").split("::").next().unwrap_or("").to_string();
            let mut item = Map::new();
            for (k, v) in [("fact", json!(s(&d, "fact"))), ("at", json!(s(&p, "at"))), ("reads as", json!(s(&p, "reads as"))), ("to", json!(to)), ("by", by)] {
                item.insert(k.into(), v);
            }
            let tried: R<String> = (|| {
                if p.get("some").is_some() {
                    return Err("it lists some entries: which to take out or rename is not determined by the instruction".into());
                }
                let rd = decl.get("reader").filter(|r| !r.is_null()).ok_or("it is read by a reader, not by a pattern")?;
                let new = text_of(&path, &mut texts);
                let part = part_of(&new, s(&p, "at")).filter(|x| new.matches(x.as_str()).count() == 1).ok_or("the part cannot be pointed at in the file as text")?;
                Ok(new.replacen(&part, &text::write_pattern(rd, &part, to)?, 1))
            })();
            match tried {
                Ok(new) => {
                    texts.get_mut(&path).unwrap().1 = new;
                    item.insert("how".into(), json!("read back with its pattern"));
                    written.push(Value::Object(item));
                }
                Err(e) => {
                    item.insert("why".into(), json!(e));
                    item.insert("h".into(), json!(s(&d, "h")));
                    item.insert("decl".into(), decl.clone());
                    item.insert("some".into(), json!(p.get("some").is_some()));
                    item.insert("question".into(), json!(text::question(&fact, &decl).0));
                    todo.push(item);
                }
            }
        }
    }
    let plain = |t: &Map<String, Value>| -> Map<String, Value> {
        t.iter().filter(|(k, _)| !["h", "decl", "some", "question", "unit", "id", "new", "reference"].contains(&k.as_str())).map(|(k, v)| (k.clone(), v.clone())).collect()
    };
    let mut readings: Vec<Value> = vec![];
    let mut cost = 0.0;
    match agents {
        None => by_hand.extend(todo.iter().map(|t| Value::Object(plain(t)))),
        Some(ag) => {
            // what is declared, and read how, in the files an agent may edit
            let declared: Vec<(String, Value)> = kernel::declared(&work.join("pw-facts.json"))?.iter()
                .flat_map(|f| st.fact(&f.h).map(|x| list(x, "places").into_iter().map(|p| (f.h.clone(), p)).collect::<Vec<_>>()).unwrap_or_default()).collect();
            while !todo.is_empty() {
                let (mut batch, mut seen, mut rest): (Vec<Map<String, Value>>, Vec<String>, Vec<Map<String, Value>>) = (vec![], vec![], vec![]);
                for t in std::mem::take(&mut todo) {      // one place per file at a time: the next is cut from the text as edited
                    let tv = Value::Object(t.clone());
                    let path = s(&tv, "at").split("::").next().unwrap_or("").to_string();
                    if seen.contains(&path) { rest.push(t); continue; }
                    seen.push(path.clone());
                    let text = text_of(&path, &mut texts);
                    let unit = part_of(&text, s(&tv, "at")).filter(|p| text.matches(p.as_str()).count() == 1).unwrap_or_else(|| text.clone());
                    if unit.chars().count() > UNIT {
                        let mut b = plain(&t);
                        b.insert("why".into(), json!(format!("{}; and the passage is longer than {} characters, too long to have rewritten whole", s(&tv, "why"), UNIT)));
                        by_hand.push(Value::Object(b));
                        continue;
                    }
                    // what the project already says about this, where read by a pattern: to take names and wording from
                    let (mut reference, mut room) = (vec![], 12000usize);
                    let fact = st.fact(s(&tv, "h")).cloned().unwrap_or_default();
                    for p in list(&fact, "places") {
                        if p.get("reader").map_or(false, |r| !r.is_null()) && s(&p, "at") != s(&tv, "at") && !p.get("some").and_then(Value::as_bool).unwrap_or(false) {
                            let file = s(&p, "at").split("::").next().unwrap_or("").to_string();
                            text_of(&file, &mut texts);
                            let r = read_text(&texts[&file].0, s(&p, "at"));
                            if r.chars().count() <= room {
                                room -= r.chars().count();
                                reference.push(json!([s(&p, "at"), r]));
                            }
                        }
                    }
                    let mut t = t;
                    t.insert("unit".into(), json!(unit));
                    t.insert("id".into(), json!(batch.len()));
                    t.insert("reference".into(), json!(reference));
                    batch.push(t);
                }
                todo = rest;
                if batch.is_empty() { continue; }
                let (answers, cannot, problems, c) = ask_editor(&ag.editor, &batch, ag.budget);
                cost += c;
                let mut blind: Vec<Map<String, Value>> = vec![];
                for t in batch {
                    let tv = Value::Object(t.clone());
                    let (at, path) = (s(&tv, "at").to_string(), s(&tv, "at").split("::").next().unwrap_or("").to_string());
                    let id = tv["id"].as_i64().unwrap_or(-1);
                    let unit = s(&tv, "unit").to_string();
                    let text = texts[&path].1.clone();
                    let outcome: R<Option<String>> = (|| {
                        let new_unit = answers.get(&id).cloned().ok_or_else(|| match cannot.get(&id) {
                            Some(why) => format!("the agent says it cannot be done: {}", why),
                            None => format!("the agent gave no answer{}", if problems.is_empty() { String::new() } else { format!(" ({})", problems.join("; ")) }),
                        })?;
                        if new_unit.trim_end_matches('\n') == unit.trim_end_matches('\n') {
                            return Err("the agent returned the passage unchanged".into());
                        }
                        // the passage ends as it ended: the blank lines before the next part are not the agent's to change
                        let new_unit = format!("{}{}", new_unit.trim_end_matches('\n'), &unit[unit.trim_end_matches('\n').len()..]);
                        if ratio(&unit, &new_unit) < 0.6 && (new_unit.chars().count() as i64 - unit.chars().count() as i64).abs() + 1 > 200 {
                            return Err("the agent rewrote the passage instead of changing the value in it".into());
                        }
                        let new = text.replacen(&unit, &new_unit, 1);
                        for (h, p) in &declared {             // nothing else that is declared in this file may read differently
                            if s(p, "at").split("::").next() != Some(path.as_str()) || (h == s(&tv, "h") && s(p, "at") == at) {
                                continue;
                            }
                            let name = st.fact(h).map(|f| s(f, "name").to_string()).unwrap_or_default();
                            if let Some(rd) = p.get("reader").filter(|r| !r.is_null()) {
                                let Ok(before) = compute(rd, &read_text(&text, s(p, "at"))) else { continue };       // (it could not be read before either)
                                let after = compute(rd, &read_text(&new, s(p, "at"))).map_err(|e| format!("afterwards {} could no longer be read for {}: {}", s(p, "at"), name, e))?;
                                if after != before {
                                    return Err(format!("afterwards {} would read as {} for {}, not {}", s(p, "at"), after.chars().take(60).collect::<String>(), name, before.chars().take(60).collect::<String>()));
                                }
                            } else {
                                for q in st.quotes(h, s(p, "at")) {
                                    if norm(&read_text(&text, s(p, "at"))).contains(&norm(&q)) && !norm(&read_text(&new, s(p, "at"))).contains(&norm(&q)) {
                                        return Err(format!("afterwards the sentence {} was read from would be gone from {}", name, s(p, "at")));
                                    }
                                }
                            }
                        }
                        if let Some(rd) = tv["decl"].get("reader").filter(|r| !r.is_null()) {
                            let back = compute(rd, &read_text(&new, &at)).map_err(|e| format!("after the agent's edit the place can no longer be read: {}", e))?;
                            if !same(&back, s(&tv, "to"), tv["some"].as_bool().unwrap_or(false)) {
                                return Err(format!("after the agent's edit the place reads as {}", back.chars().take(80).collect::<String>()));
                            }
                            texts.get_mut(&path).unwrap().1 = new;
                            return Ok(None);
                        }
                        Ok(Some(new))
                    })();
                    match outcome {
                        Ok(None) => { let mut w = plain(&t); w.insert("how".into(), json!("changed by an agent; read back with its pattern")); written.push(Value::Object(w)); }
                        Ok(Some(new)) => { let mut b = t.clone(); b.insert("new".into(), json!(new)); blind.push(b); }
                        Err(e) => { let mut b = plain(&t); b.insert("why".into(), json!(e)); by_hand.push(Value::Object(b)); }
                    }
                }
                if blind.is_empty() { continue; }
                let files = work.join("written");
                for t in &blind {                        // the reader is shown the proposed text, in place of the file
                    let tv = Value::Object(t.clone());
                    let path = files.join(s(&tv, "at").split("::").next().unwrap_or(""));
                    let _ = std::fs::create_dir_all(path.parent().unwrap());
                    let _ = std::fs::write(&path, s(&tv, "new"));
                }
                let wanted: Vec<(String, String)> = blind.iter().map(|t| (s(&Value::Object(t.clone()), "h").to_string(), s(&Value::Object(t.clone()), "at").to_string())).collect();
                let (read, events, c) = read_back(&db, lean_dir, &files, &wanted, &ag.reader, ag.budget)?;
                cost += c;
                for t in blind {
                    let tv = Value::Object(t.clone());
                    let key = (s(&tv, "h").to_string(), s(&tv, "at").to_string());
                    let path = s(&tv, "at").split("::").next().unwrap_or("").to_string();
                    match read.get(&key) {
                        Some(got) if same(got, s(&tv, "to"), tv["some"].as_bool().unwrap_or(false)) => {
                            texts.get_mut(&path).unwrap().1 = s(&tv, "new").to_string();
                            let mut w = plain(&t);
                            w.insert("how".into(), json!("changed by an agent; read back by a blind reader"));
                            written.push(Value::Object(w));
                            readings.extend(events.iter().filter(|e| (s(e, "h"), s(e, "place")) == (key.0.as_str(), key.1.as_str())).cloned());
                        }
                        got => {
                            let mut b = plain(&t);
                            b.insert("why".into(), json!(format!("an agent proposed a new text, but a blind reader shown it {}",
                                match got { Some(g) => format!("reads {}", g.chars().take(80).collect::<String>()), None => "did not read the value off it".into() })));
                            by_hand.push(Value::Object(b));
                        }
                    }
                }
            }
        }
    }
    let _ = std::fs::remove_dir_all(&work);
    let files: Map<String, Value> = texts.iter().filter(|(_, (o, n))| o != n).map(|(p, (o, n))| (p.clone(), json!([o, n]))).collect();
    Ok(json!({ "files": files, "written": written, "by hand": by_hand, "refused": refused, "unread": unread, "readings": readings,
               "cost_usd": (cost * 100.0).round() / 100.0 }))
}

pub fn command(args: &[String]) -> R<i32> {
    let usage = "pw propagate [--repo DIR] [--suppose 'FACT NAME=VALUE' ...] [--apply] [--agent [--model M] [--reader-model M] [--budget DOLLARS]] [--json]";
    let (mut repo, mut lean_dir, mut suppose, mut apply, mut use_agent, mut as_json) = (PathBuf::from("."), crate::lean::lean_dir(), Map::new(), false, false, false);
    let mut ag = Agents { editor: agent::MODEL.into(), reader: agent::SECOND.into(), budget: 3.0 };
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--repo" => repo = PathBuf::from(value("a directory")?),
            "--lean-dir" => lean_dir = PathBuf::from(value("a directory")?),
            "--suppose" => {
                let v = value("'FACT NAME=VALUE'")?;
                let (name, val) = v.split_once('=').ok_or("--suppose takes 'FACT NAME=VALUE'")?;
                suppose.insert(name.trim().to_string(), serde_json::from_str(val).unwrap_or_else(|_| json!(val.trim())));
            }
            "--apply" => apply = true,
            "--agent" => use_agent = true,
            "--json" => as_json = true,
            "--model" => ag.editor = value("a model")?,
            "--reader-model" => ag.reader = value("a model")?,
            "--budget" => ag.budget = value("an amount")?.parse().map_err(|_| "--budget is an amount in dollars".to_string())?,
            other => return Err(format!("unknown argument {}; {}", other, usage)),
        }
        i += 1;
    }
    let repo = std::fs::canonicalize(&repo).map_err(|e| format!("{}: {}", repo.display(), e))?;
    let text = std::fs::read_to_string(repo.join("pw-facts.json")).map_err(|_| format!("nothing is declared here: there is no pw-facts.json in {}", repo.display()))?;
    let facts: Vec<Value> = serde_json::from_str(&text).map_err(|e| format!("pw-facts.json is not JSON: {}", e))?;
    if use_agent {
        agent::ready()?;
    }
    let got = plan(&repo, &lean_dir, &facts, &suppose, if use_agent { Some(&ag) } else { None })?;
    let files: BTreeMap<String, (String, String)> = got["files"].as_object().unwrap().iter()
        .map(|(p, v)| (p.clone(), (v[0].as_str().unwrap_or("").to_string(), v[1].as_str().unwrap_or("").to_string()))).collect();
    let open = !list(&got, "refused").is_empty() || !list(&got, "by hand").is_empty() || !list(&got, "unread").is_empty();
    if as_json {
        println!("{}", serde_json::to_string(&got).unwrap());
    } else {
        for r in list(&got, "refused") {
            let said = list(&r, "instructions");
            if r["supposed"].as_bool().unwrap_or(false) {
                let mine = said.iter().find(|i| s(i, "by") == SUPPOSED).cloned().unwrap_or_default();
                let others: Vec<String> = said.iter().filter(|i| s(i, "by") != SUPPOSED).map(|i| format!("{} ({})", s(i, "by"), s(i, "is"))).collect();
                println!("{}: supposing {} is against what was laid down by {}. Nothing is written for it.", s(&r, "fact"), s(&mine, "is"), others.join(", "));
            } else {
                println!("{}: the instructions of {} cannot both hold. Nothing is written for it.", s(&r, "fact"), said.iter().map(|i| s(i, "by")).collect::<Vec<_>>().join(", "));
            }
        }
        for u in list(&got, "unread") {
            println!("{}: {} is not read ({}), so nothing can be said about it", s(&u, "fact"), s(&u, "at"), s(&u, "why").chars().take(80).collect::<String>());
        }
        let short = |x: &str, n: usize| x.chars().take(n).collect::<String>();
        for w in list(&got, "written") {
            let by: Vec<String> = list(&w, "by").iter().filter_map(Value::as_str).map(String::from).collect();
            println!("{}: {}  {} -> {}   (from {}; {})", s(&w, "fact"), s(&w, "at"), short(s(&w, "reads as"), 60), short(s(&w, "to"), 60), by.join(", "), s(&w, "how"));
        }
        for b in list(&got, "by hand") {
            println!("{}: {} reads as {} and is left to change by hand to {}: {}", s(&b, "fact"), s(&b, "at"), short(s(&b, "reads as"), 80), short(s(&b, "to"), 80), s(&b, "why"));
        }
    }
    if !files.is_empty() {
        if !as_json {
            println!();
            print!("{}", diff(&files));
        }
        if apply {
            for (path, (_, new)) in &files {
                std::fs::write(repo.join(path), new).map_err(|e| format!("{}: {}", path, e))?;
            }
            let readings = list(&got, "readings");
            if !readings.is_empty() {                  // what the blind reader read of the new text holds for the files as written
                kernel::with_record(&repo.join("pw-log.jsonl"), "propagate", |st| st.adopt(&readings))?;
            }
            if !as_json {
                println!("\n{} file(s) written. Then: pw check{}", files.len(), if use_agent { " (and pw maintain for what an agent changed)" } else { "" });
            }
        } else if !as_json {
            println!("\nnothing was written (--apply writes these changes)");
        }
    } else if !open && !as_json {
        let laid = facts.iter().any(|f| !list(f, "instructions").is_empty()) || !suppose.is_empty();
        println!("{}", if laid { "every place already says what was laid down" } else { "no fact has an instruction: there is nothing to write (--suppose tries a value)" });
    }
    Ok(if open { 1 } else { 0 })
}
