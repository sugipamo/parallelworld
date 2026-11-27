//! What is done with a place's text besides reading it: writing a value back through a pattern,
//! the part of a long place a reader is shown, what surrounds a small one, the question a reader
//! is asked, and what calibration measured about readers. pw.discover, pw.propagate, pw.maintain
//! and pw.calibrate use these through `pw kernel` (pw/kernel.py names them as before).
use crate::kernel::interval;
use crate::read::*;
use crate::util::*;
use rustpython_parser::ast::{Ranged, Stmt};
use serde_json::{json, Map, Value};
use std::path::Path;

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

/// How a value is written in a file, for a kind of pattern: the reverse of reading it.
fn spell(kind: &str, term: &str) -> R<String> {
    let value: Value = serde_json::from_str(term).map_err(|_| format!("{} cannot be written as a {}", term, kind))?;
    match (kind, &value) {
        ("string", Value::String(x)) => Ok(x.clone()),
        ("nat" | "int", Value::Number(n)) if n.is_i64() || n.is_u64() => Ok(n.to_string()),
        ("permille", Value::Number(n)) if n.is_i64() || n.is_u64() => {
            let v = n.as_i64().unwrap_or(0);
            let (whole, rest) = (v.div_euclid(1000), v.rem_euclid(1000));
            Ok(if rest == 0 { format!("{}.0", whole) } else { format!("{}.{:03}", whole, rest).trim_end_matches('0').trim_end_matches('.').to_string() })
        }
        _ => Err(format!("{} cannot be written as a {}", term, kind)),
    }
}

/// The text with the value a pattern reads replaced by `term`: reading in reverse. Only one value
/// found by `find` (inside `within`), not rewritten; what was written has to read back as `term`.
pub fn write_pattern(rd: &Value, text: &str, term: &str) -> R<String> {
    if s(rd, "language") != "pattern" || rd.get("find").and_then(Value::as_str).is_none() || rd.get("rewrite").map_or(false, |r| !r.is_null()) {
        return Err("only a single value read by `find`, without `rewrite`, can be written back".into());
    }
    let steps: Vec<&str> = rd.get("within").and_then(Value::as_array).into_iter().flatten().filter_map(Value::as_str).chain([s(rd, "find")]).collect();
    let (mut start, mut piece) = (0usize, text.to_string());
    for step in steps {
        let found: Vec<_> = rx(step)?.captures_iter(&piece).collect();
        if found.len() != 1 {
            return Err(format!("the pattern matches {} times here; it has to match exactly once", found.len()));
        }
        let g = found[0].get(1).ok_or("the pattern's group took no part in the match")?;
        let (a, b) = (g.start(), g.end());
        start += a;
        piece = piece[a..b].to_string();
    }
    let new = format!("{}{}{}", &text[..start], spell(s(rd, "as"), term)?, &text[start + piece.len()..]);
    let back = read_pattern(rd, &new).map_err(|e| format!("after writing, the place can no longer be read: {}", e))?;
    if serde_json::from_str::<Value>(&back).ok() != serde_json::from_str::<Value>(term).ok() {
        return Err(format!("after writing, the place reads as {}, not {}", back, term));
    }
    Ok(new)
}

fn lines_keep(text: &str) -> Vec<&str> {
    text.split_inclusive('\n').collect()
}

/// The part of a long place a way of reading looks at, as it stands in the file, for a blind
/// reader; None where the whole place is to be shown (it is short, or no smaller part can be told).
pub fn excerpt(rd: &Value, text: &str, least: usize) -> Option<String> {
    let size = text.chars().count();
    if size < least {
        return None;
    }
    let small = |shown: &str| shown.chars().count() * 2 < size;
    if s(rd, "language") == "pattern" {
        if let Some(first) = rd.get("within").and_then(Value::as_array).and_then(|w| w.first()).and_then(Value::as_str) {
            // the lines the first `within` matches, whole, as they stand: what the pattern reads is in them
            let body = text.replace("\r\n", "\n");
            let found: Vec<_> = rx(first).ok()?.find_iter(&body).collect();
            if found.len() == 1 {
                let begin = body[..found[0].start()].rfind('\n').map_or(0, |i| i + 1);
                let shown = match body[found[0].end()..].find('\n') { Some(i) => &body[begin..found[0].end() + i + 1], None => &body[begin..] };
                if small(shown) {
                    return Some(shown.to_string());
                }
            }
        }
    }
    if s(rd, "language") == "rust" {
        if let Some(shown) = crate::structured::rust_lines(rd, text) {
            if small(&shown) {
                return Some(shown);
            }
        }
    }
    if s(rd, "language") == "table" {
        if let Some(shown) = crate::structured::table_lines(rd, text) {
            if small(&shown) {
                return Some(shown);
            }
        }
    }
    if s(rd, "language") == "data" && s(rd, "format") == "toml" {
        let lines = lines_keep(text);
        let mut starts = vec![0];
        starts.extend((1..lines.len()).filter(|i| lines[*i].trim_start().starts_with('[')));
        let ends: Vec<usize> = starts.iter().skip(1).cloned().chain([lines.len()]).collect();
        let kept: Vec<String> = starts.iter().zip(ends).map(|(a, b)| lines[*a..b].concat()).filter(|p| read_data(rd, p).is_ok()).collect();
        let shown = kept.concat();
        if !kept.is_empty() && read_data(rd, &shown).ok() == read_data(rd, text).ok() && small(&shown) {
            return Some(shown);
        }
    }
    if s(rd, "language") == "python" && s(rd, "take") == "names" {
        if dedent(text) != text {
            return None;
        }
        let body = parse_python(text)?;
        let line_of = |offset: usize| text[..offset].matches('\n').count();
        let lines = lines_keep(text);
        let (cls, inside): (Option<&Stmt>, &[Stmt]) = match body.as_slice() {
            [c @ Stmt::ClassDef(x)] => (Some(c), &x.body),
            _ => (None, &body),
        };
        let mut heads: Vec<String> = cls.map(|c| vec![lines[line_of(usize::from(c.range().start()))].to_string()]).unwrap_or_default();
        for n in inside {
            let (decorators, first_body) = match n {
                Stmt::FunctionDef(f) => (&f.decorator_list, &f.body),
                Stmt::AsyncFunctionDef(f) => (&f.decorator_list, &f.body),
                _ => continue,
            };
            let own = line_of(usize::from(n.range().start()));
            let first = decorators.iter().map(|d| line_of(usize::from(d.range().start()))).chain([own]).min().unwrap();
            let start_of_body = first_body.first().map(|b| line_of(usize::from(b.range().start()))).unwrap_or(own + 1);
            let head = lines[first..start_of_body.max(first)].concat();
            heads.push(if head.is_empty() { lines[own].to_string() } else { head });
        }
        let shown = heads.concat();
        if !heads.is_empty() && small(&shown) {
            return Some(shown);
        }
    }
    None
}

/// What surrounds a place too small to tell what it belongs to (its enclosing JSON object, or the
/// lines around it); None otherwise. For a reader's orientation only.
pub fn context(subject: &str, cwd: &Path, small: usize, lines: usize) -> Option<String> {
    let (path, part) = subject.split_once("::")?;
    let content = locate(subject, cwd)?;
    if part.is_empty() || content.len() > small {
        return None;
    }
    let text = std::fs::read_to_string(cwd.join(path)).ok()?;
    let cut = |x: String| x.chars().take(2500).collect::<String>();
    if path.ends_with(".json") {
        let mut around: Value = serde_json::from_str(&text).ok()?;
        let keys: Vec<&str> = part.split('.').collect();
        for key in &keys[..keys.len() - 1] {
            around = match around {
                Value::Array(a) => a.get(key.parse::<usize>().ok()?)?.clone(),
                Value::Object(o) => o.get(*key)?.clone(),
                _ => return None,
            };
        }
        let mut out = Vec::new();
        let mut ser = serde_json::Serializer::with_formatter(&mut out, serde_json::ser::PrettyFormatter::with_indent(b" "));
        serde::Serialize::serialize(&around, &mut ser).ok()?;
        return Some(cut(String::from_utf8(out).ok()?));
    }
    let content = String::from_utf8(content).ok()?;
    let at = text.find(&content)?;
    let before = lines_keep(&text[..at]);
    let after = lines_keep(&text[at + content.len()..]);
    let b = &before[before.len().saturating_sub(lines)..];
    let a = &after[..after.len().min(lines + 1)];
    Some(cut(format!("{}{}{}", b.concat(), content, a.concat())))
}

/// What a reader of a place is asked, and the identity of that question (pw/kernel.py question).
pub fn question(fact: &Value, place: &Value) -> (String, String) {
    const SOME: &str = " This passage is only expected to mention some of them (it is an example, an excerpt, a list of highlights): give the ones it mentions, and none it does not.";
    let text = format!("{}: {}", s(fact, "name"), s(fact, "text"));
    if place.get("some").and_then(Value::as_bool).unwrap_or(false) {
        (text + SOME, sha(&[s(fact, "asked"), "some"]))
    } else {
        (text, s(fact, "asked").to_string())
    }
}

/// Per reader: every measurement made in this repository, added up, with the bounds the counts
/// allow. `instructions`: only those made under these; None: per (model, instructions).
pub fn measurements(cwd: &Path, instructions: Option<&str>) -> R<Vec<Value>> {
    let Ok(text) = std::fs::read_to_string(cwd.join("pw-calibration.json")) else { return Ok(vec![]) };
    let runs: Value = serde_json::from_str(&text).map_err(|e| format!("pw-calibration.json is not JSON: {}", e))?;
    let mut out: Vec<(String, Option<String>, Map<String, Value>)> = vec![];
    for r in runs.as_array().into_iter().flatten() {
        let under = r.get("instructions").and_then(Value::as_str).map(String::from);
        if instructions.map_or(false, |i| under.as_deref() != Some(i)) {
            continue;
        }
        let model = s(r, "model").to_string();
        let key = if instructions.is_some() { None } else { under.clone() };
        let at = match out.iter().position(|(m, u, _)| *m == model && *u == key) {
            Some(i) => i,
            None => {
                let mut m = Map::new();
                for k in ["runs", "planted", "read", "stuck", "decoys", "accepted", "twice", "picked"] {
                    m.insert(k.into(), json!(0));
                }
                out.push((model, key, m));
                out.len() - 1
            }
        };
        let m = &mut out[at].2;
        m["runs"] = json!(m["runs"].as_i64().unwrap() + 1);
        for (key, src, name) in [("planted", "planted", "n"), ("read", "planted", "read"), ("stuck", "planted", "stuck"), ("decoys", "decoys", "n"),
                                 ("accepted", "decoys", "accepted"), ("twice", "twice", "n"), ("picked", "twice", "picked")] {
            let add = r.get(src).and_then(|x| x.get(name)).and_then(Value::as_i64).unwrap_or(0);
            m[key] = json!(m[key].as_i64().unwrap() + add);
        }
    }
    Ok(out.into_iter().map(|(model, under, mut m)| {
        let n = |k: &str| m[k].as_f64().unwrap_or(0.0);
        let rate = |k: f64, n: f64| { let (lo, hi) = interval(k, n); json!([lo, hi]) };
        let (planted, decoys, twice) = (n("planted"), n("decoys"), n("twice"));
        let (read, stuck, accepted, picked) = (n("read"), n("stuck"), n("accepted"), n("picked"));
        if planted > 0.0 {
            m.insert("read rate".into(), rate(read, planted));
            m.insert("stuck rate".into(), rate(stuck, planted));
        }
        if decoys > 0.0 {
            m.insert("accept rate".into(), rate(accepted, decoys));
        }
        if twice > 0.0 {
            m.insert("pick rate".into(), rate(picked, twice));
        }
        m.insert("model".into(), json!(model));
        m.insert("instructions".into(), json!(under));
        Value::Object(m)
    }).collect())
}

/// One operation on text, files and measurements, as pw/kernel.py asks for it.
pub fn op(req: &Value) -> Option<R<Value>> {
    let cwd = Path::new(req.get("cwd").and_then(Value::as_str).unwrap_or("."));
    let text = s(req, "text");
    let rd = &req["reader"];
    Some(match s(req, "op") {
        "reader" => reader(&req["read"], s(req, "at")),
        "compute" => compute(rd, text).map(|v| json!(v)),
        "write_pattern" => write_pattern(rd, text, s(req, "term")).map(|v| json!(v)),
        "excerpt" => Ok(json!(excerpt(rd, text, req.get("least").and_then(Value::as_u64).unwrap_or(1500) as usize))),
        "context" => Ok(json!(context(s(req, "subject"), cwd, req.get("small").and_then(Value::as_u64).unwrap_or(300) as usize,
                                      req.get("lines").and_then(Value::as_u64).unwrap_or(8) as usize))),
        "part" => Ok(json!(match s(req, "kind") { "md" => md_section(text, s(req, "part")), "json" => json_part(text, s(req, "part")), _ => py_part(text, s(req, "part")) })),
        "locate" => Ok(json!(locate(s(req, "subject"), cwd).map(|b| String::from_utf8_lossy(&b).into_owned()))),
        "subject_id" => Ok(json!(subject_id(s(req, "subject"), cwd))),
        "unreadable" => Ok(json!(unreadable(s(req, "subject"), cwd))),
        "anchored" => Ok(json!(anchored(s(req, "quote"), s(req, "subject"), cwd))),
        "question" => { let (t, a) = question(&req["fact"], &req["place"]); Ok(json!([t, a])) }
        "measurements" => measurements(cwd, req.get("instructions").and_then(Value::as_str)).map(|v| json!(v)),
        "interval" => { let (lo, hi) = interval(req["k"].as_f64().unwrap_or(0.0), req["n"].as_f64().unwrap_or(0.0)); Ok(json!([lo, hi])) }
        _ => return None,
    })
}
