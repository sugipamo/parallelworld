//! The record replayed, and every declared fact held against the files.
use crate::read::*;
use crate::util::*;
use serde_json::{json, Map, Value};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

const CONDITIONS: [&str; 9] = [
    "computed", "confirmed by a person", "blind", "words occur in the place", "agrees with a computed place",
    "agrees with another place read blind", "read the same by a second model", "read the same blind", "contained in a computed place",
];
const DEFAULT_RULES: &str = include_str!("../../pw/rules.json");

#[derive(Clone, Default, Debug)]
pub struct Who {
    by: BTreeSet<String>,
    blind: BTreeSet<String>,
    models: BTreeSet<String>,
    under: HashMap<String, HashSet<Option<String>>>,
}

#[derive(Clone, Debug)]
pub struct Model {
    subject: String,
    obj: String,
    binding: Option<Value>,
    quote: Option<String>,
    anchor: bool,
    literal: bool,
    who: Who,
    asked: HashMap<String, Who>,
}

pub struct Place {
    pub at: String,
    pub some: bool,
    pub reader: Option<Value>,
}

pub struct Fact {
    pub h: String,
    pub name: String,
    pub typ: String,
    pub text: String,
    pub asked: String,
    pub places: Vec<Place>,
    pub instructions: Vec<Map<String, Value>>,
    pub defined: Option<Value>,
}

#[derive(Default)]
pub struct State {
    models: HashMap<String, Model>,
    objs: HashMap<String, String>,
    readings: HashMap<String, Vec<(String, String)>>,
    declined: HashMap<String, Vec<Value>>,
    confirmations: Vec<(String, Value)>,
    order: Vec<String>,
    pub proofs: usize,
    pub ways: HashSet<(String, String, String)>,
}

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

/// Replay the record: one JSON object per line.
pub fn replay(path: &Path) -> R<State> {
    let mut st = State::default();
    let mut asked: HashMap<String, String> = HashMap::new();
    let Ok(text) = std::fs::read_to_string(path) else { return Ok(st) };
    for (n, line) in text.lines().enumerate().filter(|(_, l)| !l.trim().is_empty()) {
        let bad = |e: String| format!("{}, line {}: not a readable event ({})", path.display(), n + 1, e);
        let p: Value = serde_json::from_str(line).map_err(|e| bad(e.to_string()))?;
        let h = s(&p, "h").to_string();
        match s(&p, "type") {
            "claim" => {
                let fact = p.get("fact").ok_or_else(|| bad("a claim that is not a fact".into()))?;
                let a = match fact.get("asked").and_then(Value::as_str) {
                    Some(a) => a.to_string(),
                    None => {
                        let plain = format!("the same {} is stated in {} place(s)", s(fact, "name"), fact["places"].as_array().map_or(0, Vec::len));
                        sha(&["asked", if s(&p, "text") != plain { s(&p, "text") } else { "" }])
                    }
                };
                asked.insert(h.clone(), a);
                if !st.order.contains(&h) {
                    st.order.push(h);
                }
            }
            "reading" => {
                let obj = &p["obj"];
                st.objs.entry(s(obj, "id").to_string()).or_insert_with(|| s(obj, "text").to_string());
                let m = s(&p, "m").to_string();
                let binding = p.get("binding").filter(|b| !b.is_null()).cloned();
                if let Some(b) = &binding {
                    st.ways.insert((h.clone(), s(&p, "place").to_string(), pyjson(b, true)));
                }
                let model = st.models.entry(m.clone()).or_insert_with(|| Model {
                    subject: s(&p, "subject").to_string(),
                    obj: s(obj, "id").to_string(),
                    binding,
                    quote: p.get("quote").and_then(Value::as_str).map(String::from),
                    anchor: p.get("anchor").and_then(Value::as_bool).unwrap_or(false),
                    literal: false,
                    who: Who::default(),
                    asked: HashMap::new(),
                });
                let q = p.get("asked").and_then(Value::as_str).map(String::from).or_else(|| asked.get(&h).cloned()).ok_or_else(|| bad("a reading of a fact that was not declared".into()))?;
                let actor = p.get("actor").and_then(Value::as_str).unwrap_or("anon").to_string();
                let blind = p.get("blind").and_then(Value::as_bool).unwrap_or(false);
                let name = p.get("model").and_then(Value::as_str).filter(|x| !x.is_empty());
                let under = p.get("instructions").and_then(Value::as_str).map(String::from);
                model.literal |= p.get("literal").and_then(Value::as_bool).unwrap_or(false);
                let note = |w: &mut Who| {
                    w.by.insert(actor.clone());
                    if blind {
                        w.blind.insert(actor.clone());
                        if let Some(x) = name {
                            w.models.insert(x.to_string());
                            w.under.entry(x.to_string()).or_default().insert(under.clone());
                        }
                    }
                };
                note(&mut model.who);
                note(model.asked.entry(q).or_default());
                let list = st.readings.entry(h).or_default();
                let key = (s(&p, "place").to_string(), m);
                if !list.contains(&key) {
                    list.push(key);
                }
            }
            "decline" => {
                let mut d = p.clone();
                if d.get("asked").and_then(Value::as_str).is_none() {
                    d["asked"] = json!(asked.get(&h).cloned().unwrap_or_default());
                }
                st.declined.entry(h).or_default().push(d);
            }
            "observe" => {
                if s(&p, "kind") != "sign_off" {
                    return Err(bad(format!("evidence of kind {}", s(&p, "kind"))));
                }
                let eid = s(&p, "eid").to_string();
                st.confirmations.retain(|(e, _)| *e != eid);
                st.confirmations.push((eid, p));
            }
            "proof" => st.proofs += 1,
            "agree" | "withdraw" => {}
            other => return Err(bad(format!("an event of type {}", other))),
        }
    }
    Ok(st)
}

/// The facts declared in pw-facts.json.
pub fn declared(path: &Path) -> R<Vec<Fact>> {
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("pw-facts.json");
    let dir = path.parent().map(|p| std::fs::canonicalize(p).unwrap_or(p.to_path_buf()).display().to_string()).unwrap_or_default();
    let text = std::fs::read_to_string(path).map_err(|_| format!("nothing is declared here: there is no {} in {}", name, dir))?;
    let all: Value = serde_json::from_str(&text).map_err(|e| format!("{} is not JSON: {}", name, e))?;
    let list = all.as_array().ok_or_else(|| format!("{} is a list of facts: [{{\"name\": ..., \"type\": ..., \"places\": [...]}}, ...]", name))?;
    let mut out: Vec<Fact> = vec![];
    for (n, d) in list.iter().enumerate() {
        let fname = d.get("name").and_then(Value::as_str).filter(|x| !x.trim().is_empty());
        let what = format!("{}, fact {}{}", name, n + 1, fname.map(|x| format!(" ({})", x)).unwrap_or_default());
        let fname = fname.ok_or_else(|| format!("{}: a fact is an object with a \"name\"", what))?;
        let typ = d.get("type").and_then(Value::as_str).filter(|x| !x.trim().is_empty()).ok_or_else(|| format!("{}: it needs a \"type\", the Lean type of its value: String, Nat, Int, List String, List Nat", what))?;
        let places = d.get("places").and_then(Value::as_array).filter(|p| !p.is_empty()).ok_or_else(|| format!("{}: it needs \"places\", the list of places that state it", what))?;
        let unknown: Vec<&String> = d.as_object().unwrap().keys().filter(|k| !["name", "type", "gloss", "places", "instructions", "defined", "value"].contains(&k.as_str())).collect();
        if !unknown.is_empty() {
            return Err(format!("{}: unknown keys {:?}; a fact has name, type, places and optionally gloss, instructions, defined", what, unknown));
        }
        if out.iter().any(|f| f.name == fname) {
            return Err(format!("{}: {} is declared more than once; a fact is declared once, with all its places", name, fname));
        }
        let typ = norm(typ);
        let mut ps = vec![];
        for p in places {
            let place = match p {
                Value::String(at) => Place { at: at.clone(), some: false, reader: None },
                Value::Object(o) => {
                    let keys: Vec<&str> = o.keys().map(String::as_str).collect();
                    let some_ok = o.get("some").map_or(true, |v| v.as_bool() == Some(true));
                    let shape = (o.contains_key("read") && keys.iter().all(|k| ["at", "read", "some"].contains(k))) || (keys.len() == 2 && o.contains_key("some"));
                    if !o.contains_key("at") || !shape || !some_ok {
                        return Err(format!("{}: a place is a string, or {{\"at\": ..., \"read\": {{...}}}}, either with \"some\": true if it states only some entries of a list", fname));
                    }
                    let at = o.get("at").and_then(Value::as_str).ok_or_else(|| format!("{}: a place is a string, or {{\"at\": ..., \"read\": {{...}}}}", fname))?;
                    let some = o.get("some").and_then(Value::as_bool).unwrap_or(false);
                    let reader = match o.get("read") {
                        Some(r) => Some(reader(r, at).map_err(|e| format!("{}: {}", fname, e))?),
                        None => None,
                    };
                    Place { at: at.to_string(), some, reader }
                }
                _ => return Err(format!("{}: a place is a string, or {{\"at\": ..., \"read\": {{...}}}}", fname)),
            };
            if ps.iter().any(|q: &Place| q.at == place.at) {
                return Err(format!("{}: {} is listed more than once; a place is read one way per fact", fname, place.at));
            }
            ps.push(place);
        }
        if ps.iter().all(|p| p.some) {
            return Err("a fact needs at least one place that states the whole of it".into());
        }
        let gloss = norm(d.get("gloss").and_then(Value::as_str).unwrap_or(""));
        let mut instructions = vec![];
        for i in d.get("instructions").and_then(Value::as_array).cloned().unwrap_or_default() {
            let mut o = i.as_object().cloned().ok_or_else(|| format!("{}: \"instructions\" is a list of {{\"is\": value, \"by\": who}}", fname))?;
            let is = o.get("is").ok_or_else(|| format!("{}: an instruction is {{\"is\": value, \"by\": who}}, optionally with \"said\" and \"on\"", fname))?;
            let term = norm(&if json_like(&typ) { pyjson(is, false) } else { is.as_str().unwrap_or("").to_string() });
            if json_like(&typ) && written(&typ, &term).is_none() {
                return Err(format!("{} is not a {} written out", term, typ));
            }
            o.insert("is".into(), json!(term));
            instructions.push(o);
        }
        out.push(Fact {
            h: format!("H:{}", sha(&["fact", fname, &typ])),
            name: fname.to_string(),
            text: if gloss.is_empty() { format!("the same {} is stated in {} place(s)", fname, ps.len()) } else { gloss.clone() },
            asked: sha(&["asked", &gloss]),
            typ,
            places: ps,
            instructions,
            defined: d.get("defined").cloned(),
        });
    }
    Ok(out)
}

pub fn needs_lean(facts: &[Fact]) -> bool {
    facts.iter().any(|f| f.defined.is_some() || !json_like(&f.typ))
}

// ---- who may be believed ----------------------------------------------------------------------

fn beta_ppf(p: f64, a: f64, b: f64) -> f64 {
    use statrs::distribution::{Beta, ContinuousCDF};
    Beta::new(a, b).map(|d| d.inverse_cdf(p)).unwrap_or(f64::NAN)
}

fn interval(k: f64, n: f64) -> (f64, f64) {
    (if k == 0.0 { 0.0 } else { beta_ppf(0.025, k, n - k + 1.0) }, if k == n { 1.0 } else { beta_ppf(0.975, k + 1.0, n - k) })
}

fn rules(cwd: &Path) -> R<Value> {
    let own = cwd.join("pw-rules.json");
    let text = if own.exists() { std::fs::read_to_string(&own).map_err(|e| e.to_string())? } else { DEFAULT_RULES.to_string() };
    let rules: Value = serde_json::from_str(&text).map_err(|e| format!("pw-rules.json is not JSON: {}", e))?;
    for rule in rules["a reading stands if any of"].as_array().ok_or("pw-rules.json: \"a reading stands if any of\" is a list of rules")? {
        let conds: Vec<&str> = rule.as_array().map(|a| a.iter().filter_map(Value::as_str).collect()).unwrap_or_default();
        if conds.is_empty() || conds.iter().any(|c| !CONDITIONS.contains(c)) {
            return Err(format!("a rule may ask for {:?}; not {:?}", CONDITIONS, conds));
        }
    }
    Ok(rules)
}

/// The readers whose measurements, taken together, meet the rules' bar: (model, instructions).
fn measured(cwd: &Path, rules: &Value) -> R<HashSet<(String, Option<String>)>> {
    let bar = rules["a blind reader counts if measured"].as_object().cloned().unwrap_or_default();
    let limits: [(&str, &str, usize, f64); 4] = [
        ("read at least", "read", 0, 1.0), ("stuck at most", "stuck", 1, -1.0),
        ("takes another thing for it at most", "accepted", 1, -1.0), ("picks one of two values at most", "picked", 1, -1.0),
    ];
    if let Some(unknown) = bar.keys().find(|k| !limits.iter().any(|l| l.0 == k.as_str())) {
        return Err(format!("a reader can be asked for {:?}; not {:?}", limits.iter().map(|l| l.0).collect::<Vec<_>>(), unknown));
    }
    let Ok(text) = std::fs::read_to_string(cwd.join("pw-calibration.json")) else { return Ok(HashSet::new()) };
    let runs: Value = serde_json::from_str(&text).map_err(|e| format!("pw-calibration.json is not JSON: {}", e))?;
    let mut sums: HashMap<(String, Option<String>), HashMap<&str, f64>> = HashMap::new();
    for r in runs.as_array().cloned().unwrap_or_default() {
        let who = (s(&r, "model").to_string(), r.get("instructions").and_then(Value::as_str).map(String::from));
        let m = sums.entry(who).or_default();
        for (key, src, name) in [("planted", "planted", "n"), ("read", "planted", "read"), ("stuck", "planted", "stuck"), ("decoys", "decoys", "n"),
                                 ("accepted", "decoys", "accepted"), ("twice", "twice", "n"), ("picked", "twice", "picked")] {
            *m.entry(key).or_default() += r.get(src).and_then(|x| x.get(name)).and_then(Value::as_f64).unwrap_or(0.0);
        }
    }
    let total = |key: &str| match key { "read" | "stuck" => "planted", "accepted" => "decoys", _ => "twice" };
    Ok(sums.into_iter().filter(|(_, m)| {
        limits.iter().filter(|l| bar.contains_key(l.0)).all(|(name, key, end, sign)| {
            let n = m[total(key)];
            if n == 0.0 {
                return false;                      // a rate that was not measured does not meet a bar on it
            }
            let (lo, hi) = interval(m[*key], n);
            sign * (if *end == 0 { lo } else { hi }) >= sign * bar[*name].as_f64().unwrap_or(f64::NAN)
        })
    }).map(|(who, _)| who).collect())
}

fn counted(w: &Who, measured: &HashSet<(String, Option<String>)>) -> BTreeSet<String> {
    w.models.iter().filter(|m| {
        let any = HashSet::from([None]);
        w.under.get(*m).filter(|u| !u.is_empty()).unwrap_or(&any).iter().any(|i| match i {
            Some(_) => measured.contains(&((*m).clone(), i.clone())),
            None => measured.iter().any(|(x, _)| x == *m),
        })
    }).cloned().collect()
}

// ---- holding a fact against the files -----------------------------------------------------------

fn agreement(typ: &str, terms: &[&str]) -> R<&'static str> {
    let values: Option<Vec<Value>> = terms.iter().map(|t| written(typ, t)).collect();
    let values = values.ok_or("a term that is not a written-out value: this needs Lean, which this build does not ask yet (python -m pw.check does)")?;
    Ok(if values.iter().all(|v| *v == values[0]) { "holds" } else { "not" })
}

fn contained(typ: &str, part: &str, whole: &str) -> R<&'static str> {
    match (written(typ, part), written(typ, whole)) {
        (Some(Value::Array(a)), Some(Value::Array(b))) => Ok(if a.iter().all(|x| b.contains(x)) { "holds" } else { "not" }),
        _ => Err("a list that is not written out: this needs Lean, which this build does not ask yet (python -m pw.check does)".into()),
    }
}

fn outside(part: &str, whole: &str) -> Vec<Value> {
    let (Ok(Value::Array(a)), Ok(Value::Array(b))) = (serde_json::from_str::<Value>(part), serde_json::from_str::<Value>(whole)) else { return vec![] };
    let mut out: Vec<Value> = a.into_iter().filter(|x| !b.contains(x)).collect();
    out.sort_by_key(|x| x.as_str().map(String::from).unwrap_or_else(|| format!("{:>40}", x)));
    out.dedup();
    out
}

fn value(text: &str) -> Value {
    serde_json::from_str(text).unwrap_or_else(|_| json!(text))
}

/// The view of a reading as an answer to the question a place is asked now.
fn view<'a>(st: &'a State, m: &str, asked: &str) -> Option<(&'a Model, &'a Who)> {
    let info = &st.models[m];
    if info.binding.is_some() { Some((info, &info.who)) } else { info.asked.get(asked).map(|w| (info, w)) }
}

pub fn recheck_fact(st: &mut State, fact: &Fact, cwd: &Path) -> R<Value> {
    let h = &fact.h;
    let asked_of = |p: &Place| if p.some { sha(&[&fact.asked, "some"]) } else { fact.asked.clone() };
    let mut places: Vec<Map<String, Value>> = vec![];
    let mut unread: Vec<Value> = vec![];
    let rejected: HashSet<String> = st.confirmations.iter().filter(|(_, e)| s(e, "outcome") == "rejected").map(|(_, e)| s(e, "target").to_string()).collect();
    for decl in &fact.places {
        let (at, asked) = (&decl.at, asked_of(decl));
        let now = subject_id(at, cwd);
        let mut about = Map::new();
        about.insert("at".into(), json!(at));
        if decl.some {
            about.insert("some".into(), json!(true));
        }
        let fail = |mut about: Map<String, Value>, why: String, broken: bool| {
            about.insert("why".into(), json!(why));
            if broken {
                about.insert("broken".into(), json!(true));
            }
            Value::Object(about)
        };
        if let Some(lost) = unreadable(at, cwd) {
            unread.push(fail(about, lost, true));
            continue;
        }
        let readings = st.readings.get(h).cloned().unwrap_or_default();
        let ever: Vec<&String> = readings.iter().filter(|(p, m)| p == at && !rejected.contains(m)).map(|(_, m)| m).collect();
        let seen: Vec<&String> = ever.iter().filter(|m| view(st, m, &asked).is_some()).cloned().collect();
        let mut have: Vec<String> = seen.iter().filter(|m| {
            let x = &st.models[**m];
            x.subject == now || (x.anchor && x.quote.as_deref().map_or(false, |q| anchored(q, at, cwd)))
        }).map(|m| (*m).clone()).collect();
        let mut said: Vec<(String, String)> = vec![];
        for m in have.iter().filter(|m| st.models[*m].binding.is_none()) {
            let o = st.models[m].obj.clone();
            match said.iter_mut().find(|(x, _)| *x == o) {
                Some(e) => e.1 = m.clone(),
                None => said.push((o, m.clone())),
            }
        }
        if decl.reader.is_none() && said.len() > 1 {
            let each: Vec<String> = said.iter().map(|(o, m)| {
                let text: String = st.objs[o].chars().take(60).collect();
                format!("{} ({}) reads {}", m, st.models[m].who.by.iter().cloned().collect::<Vec<_>>().join(", "), text)
            }).collect();
            unread.push(fail(about, format!("its readers disagree: {}", each.join("; ")), false));
            continue;
        }
        if let Some(how) = &decl.reader {
            let text = String::from_utf8_lossy(&locate(at, cwd).unwrap_or_default()).into_owned();
            let computed = compute(how, &text).and_then(|obj| {
                let obj = norm(&obj);
                if json_like(&fact.typ) && written(&fact.typ, &obj).is_none() {
                    return Err(format!("{} is not a {} written out", obj.chars().take(80).collect::<String>(), fact.typ));
                }
                Ok(obj)
            });
            match computed {
                Ok(obj) => {
                    let o = format!("O:{}", sha(&[&fact.typ, &obj]));
                    let m = format!("M:{}", sha(&[h, &now, &o, &pyjson(how, true)]));
                    st.objs.entry(o.clone()).or_insert(obj);
                    st.models.entry(m.clone()).or_insert_with(|| Model {
                        subject: now.clone(), obj: o, binding: Some(how.clone()), quote: None, anchor: false, literal: false, who: Who::default(), asked: HashMap::new(),
                    });
                    let list = st.readings.entry(h.clone()).or_default();
                    if !list.contains(&(at.clone(), m.clone())) {
                        list.push((at.clone(), m.clone()));
                    }
                    have = vec![m];
                }
                Err(e) => {
                    unread.push(fail(about, e, true));
                    continue;
                }
            }
        } else if have.is_empty() {
            let no: Vec<Value> = st.declined.get(h).map(|d| d.iter().filter(|d| s(d, "place") == at && s(d, "subject") == now && s(d, "asked") == asked).cloned().collect()).unwrap_or_default();
            let why = if !seen.is_empty() { "it changed since it was read" } else if !ever.is_empty() { "the fact's description changed since it was read: what was read answered another question" } else { "nobody has read it yet" };
            let mut u = fail(about, why.into(), false);
            if !no.is_empty() {
                u["declined"] = json!(no);
            }
            unread.push(u);
            continue;
        }
        let m = have.last().unwrap();
        about.insert("reads as".into(), json!(st.objs[&st.models[m].obj]));
        about.insert("m".into(), json!(m));
        about.insert("by".into(), json!(if st.models[m].binding.is_some() { "reader" } else { "stated" }));
        places.push(about);
    }
    let mut entry = Map::new();
    entry.insert("h".into(), json!(h));
    entry.insert("fact".into(), json!(fact.name));
    entry.insert("text".into(), json!(fact.text));

    // what people have laid down, and which of it can be used
    let mut said = fact.instructions.clone();
    for a in 0..said.len() {
        for b in a + 1..said.len() {
            let (x, y) = (s(&Value::Object(said[a].clone()), "is").to_string(), s(&Value::Object(said[b].clone()), "is").to_string());
            if x != y && agreement(&fact.typ, &[&x, &y])? != "holds" {
                for (i, other) in [(a, b), (b, a)] {
                    let by = said[other]["by"].clone();
                    said[i].entry("set aside").or_insert_with(|| json!([])).as_array_mut().unwrap().push(by);
                }
            }
        }
    }
    let usable: Vec<&Map<String, Value>> = said.iter().filter(|i| !i.contains_key("set aside")).collect();
    let target = usable.first().map(|i| i["is"].as_str().unwrap_or("").to_string());
    if fact.defined.is_some() {
        return Err(format!("{} is defined from other facts: what the definition gives has to be worked out by Lean, which this build does not ask yet (python -m pw.check does)", fact.name));
    }
    let reads = |p: &Map<String, Value>| p["reads as"].as_str().unwrap_or("").to_string();
    let is_some = |p: &Map<String, Value>| p.contains_key("some");
    let whole: Vec<usize> = (0..places.len()).filter(|i| !is_some(&places[*i])).collect();
    let state_of = |verdict: Option<&str>| match verdict { Some("holds") => "current", Some("not") => "violated", _ => "uncovered" };
    let mut state: String;
    if let Some(t) = &target {
        entry.insert("value".into(), json!(t));
    }
    if !unread.is_empty() {
        state = if unread.iter().any(|u| s(u, "why").contains("disagree")) { "disputed" } else { "stale" }.into();
    } else if let Some(target) = &target {
        let mut who: Vec<String> = usable.iter().map(|i| i["by"].as_str().unwrap_or("").to_string()).collect();
        who.sort();
        who.dedup();
        let mut verdicts = vec![];
        for p in places.iter_mut() {
            let v = if is_some(p) {
                let v = contained(&fact.typ, &reads(p), target)?;
                p.insert("contained".into(), json!(v == "holds"));
                if v == "not" {
                    p.insert("not in the whole".into(), json!(outside(&reads(p), target)));
                }
                v
            } else {
                agreement(&fact.typ, &[&reads(p), target])?
            };
            if v == "not" {
                p.insert("against".into(), json!(who));
            }
            verdicts.push(v);
        }
        state = state_of(if verdicts.contains(&"not") { Some("not") } else if verdicts.iter().all(|v| *v == "holds") { Some("holds") } else { None }).into();
    } else {
        let terms: Vec<String> = whole.iter().map(|i| reads(&places[*i])).collect();
        let mut verdict = agreement(&fact.typ, &terms.iter().map(String::as_str).collect::<Vec<_>>())?;
        if verdict != "holds" {
            for p in places.iter_mut().filter(|p| is_some(p)) {
                p.insert("whole undecided".into(), json!(true));
            }
        } else {
            for p in places.iter_mut().filter(|p| is_some(p)) {
                let inside = contained(&fact.typ, &reads(p), &terms[0])?;
                p.insert("contained".into(), json!(inside == "holds"));
                if inside == "not" {
                    verdict = "not";
                    p.insert("not in the whole".into(), json!(outside(&reads(p), &terms[0])));
                }
            }
        }
        state = state_of(Some(verdict)).into();
        if verdict == "holds" {
            entry.insert("value".into(), json!(terms[0]));
        }
    }
    if !said.is_empty() {
        entry.insert("instructions".into(), json!(said));
    }
    if usable.len() < said.len() && unread.is_empty() {
        entry.insert("without the instructions set aside".into(), json!(state));
        state = "conflict".into();
    }

    // whether each reading stands is decided by the project's rules
    let rules = rules(cwd)?;
    let measured = measured(cwd, &rules)?;
    let confirmed: HashSet<(String, Option<String>)> = st.confirmations.iter().filter(|(_, e)| s(e, "outcome") == "confirmed")
        .map(|(_, e)| (s(e, "target").to_string(), e.get("asked").and_then(Value::as_str).map(String::from))).collect();
    let readings = st.readings.get(h).cloned().unwrap_or_default();
    let asked_at: HashMap<&str, String> = fact.places.iter().map(|p| (p.at.as_str(), asked_of(p))).collect();
    let whole_ms: Vec<(usize, String, String)> = whole.iter().map(|i| (*i, places[*i]["m"].as_str().unwrap().to_string(), places[*i]["at"].as_str().unwrap().to_string())).collect();
    for i in 0..places.len() {
        let (m, at) = (places[i]["m"].as_str().unwrap().to_string(), places[i]["at"].as_str().unwrap().to_string());
        let asked = &asked_at[at.as_str()];
        let (info, who) = view(st, &m, asked).ok_or("a reading that does not answer the question asked")?;
        let partial = is_some(&places[i]);
        let others: Vec<(&Model, &Who)> = whole_ms.iter().filter(|(j, qm, _)| *j != i && !partial && st.models[qm].obj == info.obj)
            .filter_map(|(_, qm, qat)| view(st, qm, &asked_at[qat.as_str()])).collect();
        let readers = counted(who, &measured);
        let mine: Vec<(&Model, &Who)> = readings.iter().filter(|(a, _)| *a == at).filter_map(|(_, x)| view(st, x, asked)).collect();
        let stated: Vec<&(&Model, &Who)> = mine.iter().filter(|(x, w)| x.binding.is_none() && !counted(w, &measured).is_empty()).collect();
        let same_blind = info.binding.is_some() && stated.iter().any(|(sm, _)| mine.iter().any(|(c, _)| c.binding == info.binding && sm.subject == c.subject && value(&st.objs[&sm.obj]) == value(&st.objs[&c.obj])));
        let has = |c: &str| -> bool {
            match c {
                "computed" => info.binding.is_some(),
                "confirmed by a person" => confirmed.contains(&(m.clone(), None)) || confirmed.contains(&(m.clone(), Some(asked.clone()))),
                "blind" => !readers.is_empty(),
                "words occur in the place" => info.literal,
                "agrees with a computed place" => others.iter().any(|(o, _)| o.binding.is_some()),
                "agrees with another place read blind" => others.iter().any(|(o, w)| o.binding.is_none() && !counted(w, &measured).is_empty() && w.blind.difference(&who.blind).next().is_some()),
                "read the same by a second model" => readers.len() > 1,
                "read the same blind" => same_blind,
                "contained in a computed place" => places[i].get("contained").and_then(Value::as_bool).unwrap_or(false) && whole_ms.iter().any(|(_, qm, _)| st.models[qm].binding.is_some()),
                _ => false,
            }
        };
        let met = rules["a reading stands if any of"].as_array().unwrap().iter().find(|rule| rule.as_array().unwrap().iter().all(|c| has(c.as_str().unwrap_or(""))));
        let why = met.map(|r| r.as_array().unwrap().iter().filter_map(Value::as_str).collect::<Vec<_>>().join(" + ")).unwrap_or_else(|| "no rule is met".into());
        let now = subject_id(&at, cwd);
        let mut extra = Map::new();
        extra.insert("stands".into(), json!(met.is_some()));
        extra.insert("why".into(), json!(why));
        if info.binding.is_none() {
            let skip: &[&str] = if partial { &["agrees with a computed place", "agrees with another place read blind"] } else { &["contained in a computed place"] };
            let mut shown = Map::new();
            for c in CONDITIONS.iter().filter(|c| !["computed", "read the same blind"].contains(c) && !skip.contains(c)) {
                shown.insert((*c).into(), json!(has(c)));
            }
            extra.insert("has".into(), Value::Object(shown));
            let mut un: Vec<String> = who.models.difference(&readers).cloned().collect();
            if !who.blind.is_empty() && who.models.is_empty() {
                un.push("a reader whose model was not recorded".into());
            }
            extra.insert("unmeasured readers".into(), json!(un));
        } else {
            extra.insert("has".into(), json!({ "read the same blind": same_blind }));
            let un: BTreeSet<String> = mine.iter().filter(|(x, _)| x.binding.is_none()).flat_map(|(_, w)| w.models.difference(&counted(w, &measured)).cloned().collect::<Vec<_>>()).collect();
            extra.insert("unmeasured readers".into(), json!(un));
            let other: BTreeSet<String> = stated.iter().filter(|(x, _)| x.subject == now).map(|(x, _)| st.objs[&x.obj].clone()).filter(|t| *t != reads(&places[i])).collect();
            extra.insert("read blind as".into(), json!(other));
            let no: Vec<Value> = st.declined.get(h).map(|d| d.iter().filter(|d| s(d, "place") == at && s(d, "subject") == now && s(d, "asked") == asked).cloned().collect()).unwrap_or_default();
            extra.insert("declined".into(), json!(no));
        }
        places[i].extend(extra);
    }
    entry.insert("places".into(), json!(places));
    entry.insert("state".into(), json!(state));
    if !unread.is_empty() {
        entry.insert("unread".into(), json!(unread));
    }
    Ok(Value::Object(entry))
}

/// Hold every declared fact against the files in `cwd`: in the order the record first heard
/// of them, then the ones new to it.
pub fn recheck(st: &mut State, facts: &[Fact], cwd: &Path) -> R<Value> {
    let mut order: Vec<&Fact> = st.order.clone().iter().filter_map(|h| facts.iter().find(|f| f.h == *h)).collect();
    for f in facts {
        if !order.iter().any(|x| x.h == f.h) {
            order.push(f);
        }
    }
    let mut decisions = vec![];
    for f in order {
        match recheck_fact(st, f, cwd) {
            Ok(d) => decisions.push(d),
            // what this build cannot judge is said for that fact, and the others are still judged
            Err(e) if e.contains("this build does not ask yet") => decisions.push(json!({ "h": f.h, "fact": f.name, "text": f.text, "state": "needs Lean", "places": [], "why": e })),
            Err(e) => return Err(e),
        }
    }
    Ok(json!({ "decisions": decisions }))
}
