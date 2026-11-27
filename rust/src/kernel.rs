//! The record replayed, and every declared fact held against the files.
use crate::lean::Gate;
use crate::read::*;
use crate::util::*;
use serde_json::{json, Map, Value};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::Path;

const CONDITIONS: [&str; 9] = [
    "computed", "confirmed by a person", "blind", "words occur in the place", "agrees with a computed place",
    "agrees with another place read blind", "read the same by a second model", "read the same blind", "contained in a computed place",
];
/// Added to the question a place is asked when it states only some entries of a list (pw/kernel.py SOME).
const SOME: &str = " This passage is only expected to mention some of them (it is an example, an excerpt, a list of highlights): give the ones it mentions, and none it does not.";
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
    props: HashMap<String, String>,
    verdict: HashMap<String, BTreeSet<String>>,
    agreed: HashMap<String, Vec<(Vec<String>, String)>>,
    pub proofs: Vec<Value>,
    pub ways: HashSet<(String, String, String)>,
    asked: HashMap<String, String>,           // H -> the question its places are asked, as recorded
    facts: HashMap<String, Value>,            // H -> the fact as last claimed (with "asked")
    withdrawn: HashMap<String, String>,       // H -> why it is no longer declared
    types: HashMap<String, String>,           // O -> its Lean type
    /// who the events this run appends are by, and the events themselves, in order
    pub actor: String,
    pub pending: Vec<Value>,
}

impl State {
    /// The Lean propositions recorded proofs are about.
    pub fn props(&self) -> HashMap<String, String> {
        self.props.clone()
    }

    /// The readings a person has confirmed or rejected.
    pub fn signed(&self) -> HashSet<String> {
        self.confirmations.iter().map(|(_, e)| s(e, "target").to_string()).collect()
    }

    /// The sentence a reading quotes, and whether the kernel checked it is in the place.
    pub fn quote(&self, m: &str) -> (Option<String>, bool) {
        self.models.get(m).map_or((None, false), |x| (x.quote.clone(), x.anchor))
    }
}

/// The id of the instructions a blind reader is given (pw/reader.txt): a reading counts per model and instructions.
pub fn instructions_id() -> String {
    sha(&[include_str!("../../pw/reader.txt")])
}

/// Python's str() of a value read off a place, to look for it in the place's words.
fn pyshown(v: &Value) -> String {
    fn repr(v: &Value) -> String {
        match v {
            Value::String(x) => if x.contains('\'') && !x.contains('"') { format!("\"{}\"", x) } else { format!("'{}'", x.replace('\\', "\\\\").replace('\'', "\\'")) },
            Value::Array(a) => format!("[{}]", a.iter().map(repr).collect::<Vec<_>>().join(", ")),
            Value::Object(o) => format!("{{{}}}", o.iter().map(|(k, x)| format!("{}: {}", repr(&json!(k)), repr(x))).collect::<Vec<_>>().join(", ")),
            other => pystr_of(other),
        }
    }
    match v {
        Value::String(x) => x.clone(),
        Value::Array(_) | Value::Object(_) => repr(v),
        other => pystr_of(other),
    }
}

/// An error a reader is told about, named as the Python kernel names it.
pub type Told = (&'static str, String);

fn kernel_err(e: String) -> Told {
    ("KernelError", e)
}

/// What a reader says one place of a fact states, with the sentence that says it
/// (pw/kernel.py read_place, for a reading stated by an agent).
pub fn read_place(st: &mut State, judge: &Judge, h: &str, place: &str, obj: &str, cwd: &Path, quote: Option<&str>, blind: bool, model: Option<&str>) -> Result<Value, Told> {
    let fact = st.facts.get(h).cloned().ok_or_else(|| kernel_err(format!("{} is not a fact", h)))?;
    let places: Vec<Value> = fact["places"].as_array().cloned().unwrap_or_default();
    let decl = places.iter().find(|p| s(p, "at") == place).ok_or_else(|| {
        let ats: Vec<&str> = places.iter().map(|p| s(p, "at")).collect();
        kernel_err(format!("{} is not a place of this fact; its places are {}", place, pylist(&ats)))
    })?;
    let content = locate(place, cwd).ok_or_else(|| kernel_err(format!("{} is not there", place)))?;
    if let Some(q) = quote {
        if !anchored(q, place, cwd) {
            return Err(kernel_err("the quote is not in the place word for word".into()));
        }
    }
    let obj = norm(obj);
    judge.gate.screen(&obj).map_err(|e| ("GateError", e))?;
    let typ = s(&fact, "type").to_string();
    if json_like(&typ) && written(&typ, &obj).is_none() {
        // what a reader says a place states is a value, not a computation
        let example = match typ.chars().next() { Some('S') => "\"fast\"", Some('N') => "14", Some('I') => "-3", _ => "[\"a\", \"b\"] or [1, 2]" };
        return Err(kernel_err(format!("state the value itself, written out: a {} such as {}", typ, example)));
    }
    let o = format!("O:{}", sha(&[&typ, &obj]));
    if !st.objs.contains_key(&o) {
        judge.typed(&typ, &obj).map_err(kernel_err)?;
    }
    let version = subject_id(place, cwd);
    let m = format!("M:{}", sha(&[h, &version, &o, ""]));
    let literal = match serde_json::from_str::<Value>(&obj) {
        Ok(said) => {
            let whole = String::from_utf8_lossy(&content).into_owned();
            let list = said.as_array().is_some();
            let place_words = if quote.is_some() && !list { quote.unwrap().to_string() } else { whole };
            let each = if let Value::Array(a) = &said { a.clone() } else { vec![said.clone()] };
            each.iter().all(|x| place_words.contains(&pyshown(x)))
        }
        Err(_) => false,
    };
    let a = &st.asked[h];
    let asked = if decl.get("some").and_then(Value::as_bool).unwrap_or(false) { sha(&[a, "some"]) } else { a.clone() };
    let under = instructions_id();
    let named = model.filter(|x| !x.is_empty());
    let known = st.models.get(&m).and_then(|x| x.asked.get(&asked)).cloned().unwrap_or_default();
    let read = st.readings.get(h).map_or(false, |l| l.contains(&(place.to_string(), m.clone())));
    let actor = st.actor.clone();
    if !read || !known.by.contains(&actor) || (blind && !known.blind.contains(&actor))
        || (blind && named.map_or(false, |x| !known.under.get(x).map_or(false, |u| u.contains(&Some(under.clone()))))) {
        let mut payload = vec![
            ("h", json!(h)), ("place", json!(place)), ("subject", json!(version)), ("m", json!(m)),
            ("obj", json!({ "id": o, "type": typ, "text": obj })), ("binding", Value::Null), ("quote", json!(quote)),
            ("asked", json!(asked)), ("blind", json!(blind)), ("model", if blind { json!(model) } else { Value::Null }),
        ];
        if blind && named.is_some() {
            payload.push(("instructions", json!(under)));
        }
        payload.push(("literal", json!(literal)));
        payload.push(("anchor", json!(quote.is_some() && !typ.contains("List"))));
        st.emit("reading", payload);
    }
    Ok(json!({ "m": m, "o": o, "read as": obj }))
}

/// A reader shown a place found that it does not state the fact (pw/kernel.py decline).
pub fn decline(st: &mut State, h: &str, place: &str, why: &str, cwd: &Path, blind: bool, model: Option<&str>) -> Result<Value, Told> {
    let fact = st.facts.get(h).cloned().ok_or_else(|| kernel_err(format!("{} is not a fact", h)))?;
    let decl = fact["places"].as_array().into_iter().flatten().find(|p| s(p, "at") == place).cloned()
        .ok_or_else(|| kernel_err(format!("{} is not a place of this fact", place)))?;
    if locate(place, cwd).is_none() {
        return Err(kernel_err(format!("{} is not there", place)));
    }
    if norm(why).is_empty() {
        return Err(kernel_err("say what the place is about instead".into()));
    }
    let a = &st.asked[h];
    let asked = if decl.get("some").and_then(Value::as_bool).unwrap_or(false) { sha(&[a, "some"]) } else { a.clone() };
    st.emit("decline", vec![("h", json!(h)), ("place", json!(place)), ("subject", json!(subject_id(place, cwd))),
                            ("why", json!(norm(why).chars().take(400).collect::<String>())), ("asked", json!(asked)),
                            ("blind", json!(blind)), ("model", if blind { json!(model) } else { Value::Null })]);
    Ok(json!({ "declined": place }))
}

impl State {
    /// The record as replayed, in the shape pw/kernel.py's State has (sets as sorted lists),
    /// for the tools that act on what the record says without judging it.
    pub fn dump(&self) -> Value {
        fn who(w: &Who) -> Value {
            let under: Map<String, Value> = w.under.iter().map(|(m, u)| {
                let mut u: Vec<Value> = u.iter().map(|x| json!(x)).collect();
                u.sort_by_key(|x| x.to_string());
                (m.clone(), json!(u))
            }).collect();
            json!({ "by": w.by, "blind": w.blind, "models": w.models, "under": under })
        }
        let mut facts = Map::new();
        for h in &self.order {
            let Some(f) = self.facts.get(h) else { continue };
            let mut f = f.clone();
            let o = f.as_object_mut().unwrap();
            o.insert("readings".into(), json!(self.readings.get(h).cloned().unwrap_or_default()));
            o.insert("declined".into(), json!(self.declined.get(h).cloned().unwrap_or_default()));
            o.insert("agreed".into(), json!(self.agreed.get(h).cloned().unwrap_or_default()));
            facts.insert(h.clone(), f);
        }
        let models: Map<String, Value> = self.models.iter().map(|(m, x)| {
            let mut v = who(&x.who);
            let o = v.as_object_mut().unwrap();
            for (k, val) in [("subject", json!(x.subject)), ("obj", json!(x.obj)), ("binding", json!(x.binding)), ("quote", json!(x.quote)),
                             ("anchor", json!(x.anchor)), ("literal", json!(x.literal))] {
                o.insert(k.into(), val);
            }
            o.insert("asked".into(), Value::Object(x.asked.iter().map(|(a, w)| (a.clone(), who(w))).collect()));
            (m.clone(), v)
        }).collect();
        let objs: Map<String, Value> = self.objs.iter().map(|(o, t)| (o.clone(), json!({ "type": self.types.get(o), "text": t }))).collect();
        let verdict: Map<String, Value> = self.verdict.iter().map(|(f, r)| (f.clone(), json!(r))).collect();
        json!({
            "facts": facts, "models": models, "objs": objs, "props": self.props, "verdict": verdict, "proofs": self.proofs,
            "confirmations": Value::Object(self.confirmations.iter().map(|(e, v)| (e.clone(), v.clone())).collect()),
            "withdrawn": self.withdrawn,
        })
    }

    /// Take over readings made against a copy of this record, of text since written into the
    /// files (pw/kernel.py adopt): each holds here exactly if the file now has that content.
    pub fn adopt(&mut self, events: &[Value]) -> R<()> {
        for e in events {
            let ok = s(e, "type") == "reading" && self.facts.get(s(e, "h")).map_or(false, |f| {
                f["places"].as_array().into_iter().flatten().any(|p| s(p, "at") == s(e, "place"))
            });
            if !ok {
                return Err("only readings of declared places can be taken over".into());
            }
            let mut e = e.clone();
            e.as_object_mut().unwrap().shift_remove("id");
            apply(self, &e)?;
            self.pending.push(e);
        }
        Ok(())
    }
}

/// A person has compared a reading with the place itself, and confirms or rejects it
/// (pw/kernel.py sign_off). True if it was recorded already.
pub fn sign_off(st: &mut State, m: &str, who: &str, confirmed: bool) -> R<bool> {
    let outcome = if confirmed { "confirmed" } else { "rejected" };
    let mut asked = None;
    'facts: for h in &st.order {
        let Some(f) = st.facts.get(h) else { continue };
        for (at, x) in st.readings.get(h).into_iter().flatten() {
            if x != m {
                continue;
            }
            if let Some(p) = f["places"].as_array().into_iter().flatten().find(|p| s(p, "at") == at) {
                let a = &st.asked[h];
                asked = Some(if p.get("some").and_then(Value::as_bool).unwrap_or(false) { sha(&[a, "some"]) } else { a.clone() });
                break 'facts;
            }
        }
    }
    let asked = asked.ok_or_else(|| format!("{} is not a reading of a declared place", m))?;
    let source = format!("person:{}/{}", who, asked);
    let eid = format!("E:{}", sha(&[m, "sign_off", &source]));
    if let Some((_, old)) = st.confirmations.iter().find(|(e, _)| *e == eid) {
        if s(old, "outcome") != outcome {
            return Err(format!("{} already recorded this reading as {}", who, s(old, "outcome")));
        }
        return Ok(true);
    }
    st.emit("observe", vec![("eid", json!(eid)), ("target", json!(m)), ("kind", json!("sign_off")), ("outcome", json!(outcome)),
                            ("source", json!(source)), ("asked", json!(asked))]);
    Ok(false)
}

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

/// Replay the record: one JSON object per line.
pub fn replay(path: &Path) -> R<State> {
    replay_text(&std::fs::read_to_string(path).unwrap_or_default(), path)
}

pub fn replay_text(text: &str, path: &Path) -> R<State> {
    let mut st = State::default();
    for (n, line) in text.lines().enumerate().filter(|(_, l)| !l.trim().is_empty()) {
        let bad = |e: String| format!("{}, line {}: not a readable event ({})", path.display(), n + 1, e);
        let p: Value = serde_json::from_str(line).map_err(|e| bad(e.to_string()))?;
        apply(&mut st, &p).map_err(bad)?;
    }
    Ok(st)
}

/// What one event of the record changes (pw/kernel.py State.apply).
fn apply(st: &mut State, p: &Value) -> Result<(), String> {
    let h = s(p, "h").to_string();
    match s(p, "type") {
        "claim" => {
            let mut fact = p.get("fact").cloned().ok_or("a claim that is not a fact")?;
            if fact.get("value").map_or(false, |v| !v.is_null()) {
                return Err("a fact with a fixed value; say whose instruction it is under \"instructions\"".into());
            }
            let a = match fact.get("asked").and_then(Value::as_str) {
                Some(a) => a.to_string(),
                None => {
                    let plain = format!("the same {} is stated in {} place(s)", s(&fact, "name"), fact["places"].as_array().map_or(0, Vec::len));
                    sha(&["asked", if s(p, "text") != plain { s(p, "text") } else { "" }])
                }
            };
            if let Some(o) = fact.as_object_mut() {
                o.shift_remove("value");
                o.insert("asked".into(), json!(a));
                o.insert("text".into(), json!(s(p, "text")));
            }
            st.asked.insert(h.clone(), a);
            st.facts.insert(h.clone(), fact);
            st.withdrawn.remove(&h);
            if !st.order.contains(&h) {
                st.order.push(h);
            }
        }
        "reading" => {
            let obj = &p["obj"];
            st.objs.entry(s(obj, "id").to_string()).or_insert_with(|| s(obj, "text").to_string());
            st.types.entry(s(obj, "id").to_string()).or_insert_with(|| s(obj, "type").to_string());
            let m = s(p, "m").to_string();
            let binding = p.get("binding").filter(|b| !b.is_null()).cloned();
            if let Some(b) = &binding {
                st.ways.insert((h.clone(), s(p, "place").to_string(), pyjson(b, true)));
            }
            let q = p.get("asked").and_then(Value::as_str).map(String::from).or_else(|| st.asked.get(&h).cloned()).ok_or("a reading of a fact that was not declared")?;
            let model = st.models.entry(m.clone()).or_insert_with(|| Model {
                subject: s(p, "subject").to_string(),
                obj: s(obj, "id").to_string(),
                binding,
                quote: p.get("quote").and_then(Value::as_str).map(String::from),
                anchor: p.get("anchor").and_then(Value::as_bool).unwrap_or(false),
                literal: false,
                who: Who::default(),
                asked: HashMap::new(),
            });
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
            let key = (s(p, "place").to_string(), m);
            if !list.contains(&key) {
                list.push(key);
            }
        }
        "decline" => {
            let mut d = p.clone();
            if d.get("asked").and_then(Value::as_str).is_none() {
                d["asked"] = json!(st.asked.get(&h).cloned().unwrap_or_default());
            }
            st.declined.entry(h).or_default().push(d);
        }
        "observe" => {
            if s(p, "kind") != "sign_off" {
                return Err(format!("evidence of kind {}", s(p, "kind")));
            }
            let eid = s(p, "eid").to_string();
            match st.confirmations.iter_mut().find(|(e, _)| *e == eid) {
                Some(e) => e.1 = p.clone(),
                None => st.confirmations.push((eid, p.clone())),
            }
        }
        "proof" => {
            let relation = s(p, "relation").to_string();
            if relation != "holds" && relation != "not" {
                return Err(format!("a proof of {}", relation));
            }
            let f = p.get("args").and_then(|a| a.get(0)).and_then(Value::as_str).ok_or("a proof of nothing")?.to_string();
            st.verdict.entry(f).or_default().insert(relation);
            st.proofs.push(p.clone());
        }
        "agree" => {
            let f = s(p, "f").to_string();
            st.props.entry(f.clone()).or_insert_with(|| s(p, "lean").to_string());
            let guards: Vec<String> = p.get("guards").and_then(Value::as_array).map(|g| g.iter().filter_map(Value::as_str).map(String::from).collect()).unwrap_or_default();
            st.agreed.entry(h).or_default().push((guards, f));
        }
        "withdraw" => {
            st.withdrawn.insert(h, s(p, "justification").to_string());
        }
        other => return Err(format!("an event of type {}", other)),
    }
    Ok(())
}

impl State {
    /// Add an event, as the Python kernel writes it: ts, actor, type, then what it says.
    fn emit(&mut self, typ: &str, payload: Vec<(&str, Value)>) {
        let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs_f64()).unwrap_or(0.0);
        let mut e = Map::new();
        e.insert("ts".into(), json!((now * 1000.0).round() / 1000.0));
        e.insert("actor".into(), json!(self.actor));
        e.insert("type".into(), json!(typ));
        for (k, v) in payload {
            e.insert(k.into(), v);
        }
        let e = Value::Object(e);
        apply(self, &e).expect("an event this kernel made itself");
        self.pending.push(e);
    }
}

/// Run `f` on the record with nothing else writing to it, and append the events it adds: the
/// record is locked, replayed, changed and written as one step (pw/kernel.py Kernel._tx).
pub fn with_record<T>(path: &Path, actor: &str, f: impl FnOnce(&mut State) -> R<T>) -> R<T> {
    use std::io::{Read, Seek, SeekFrom, Write};
    let mut fh = std::fs::OpenOptions::new().read(true).append(true).create(true).open(path)
        .map_err(|e| format!("{}: {}", path.display(), e))?;
    fh.lock().map_err(|e| format!("{}: {}", path.display(), e))?;
    let mut text = String::new();
    fh.seek(SeekFrom::Start(0)).and_then(|_| fh.read_to_string(&mut text)).map_err(|e| format!("{}: {}", path.display(), e))?;
    let mut st = replay_text(&text, path)?;
    st.actor = actor.to_string();
    let out = f(&mut st);
    if out.is_ok() && !st.pending.is_empty() {
        let lines: String = st.pending.iter().map(|e| pyjson(e, false) + "\n").collect();
        fh.write_all(lines.as_bytes()).and_then(|_| fh.flush()).map_err(|e| format!("{}: {}", path.display(), e))?;
    }
    let _ = fh.unlock();
    out
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
            let mut unknown = unknown;
            unknown.sort();
            return Err(format!("{}: unknown keys {}; a fact has name, type, places and optionally gloss, instructions, defined", what, pylist(&unknown)));
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
        let listed = match d.get("instructions") {
            None => vec![],
            Some(Value::Array(a)) if a.iter().all(Value::is_object) => a.clone(),
            Some(_) => return Err(format!("{}: \"instructions\" is a list of {{\"is\": value, \"by\": who}}", fname)),
        };
        for i in listed {
            let o = i.as_object().unwrap();
            let shape = format!("{}: an instruction is {{\"is\": value, \"by\": who}}, optionally with \"said\" and \"on\"", fname);
            let by = o.get("by").map(pystr_of).unwrap_or_default();
            if o.keys().any(|k| !["is", "by", "said", "on"].contains(&k.as_str())) || by.trim().is_empty() {
                return Err(shape);
            }
            let is = o.get("is").ok_or(shape)?;
            let term = norm(&if json_like(&typ) { pyjson(is, false) } else { is.as_str().unwrap_or("").to_string() });
            if json_like(&typ) && written(&typ, &term).is_none() {
                return Err(format!("{} is not a {} written out", term.chars().take(80).collect::<String>(), typ));
            }
            // kept as the Python kernel keeps it: is, by, and said and on where they say something
            let mut kept = Map::new();
            kept.insert("is".into(), json!(term));
            kept.insert("by".into(), json!(norm(&by)));
            for k in ["said", "on"] {
                if let Some(v) = o.get(k).filter(|v| truthy(v)) {
                    kept.insert(k.into(), json!(norm(&pystr_of(v))));
                }
            }
            if instructions.iter().any(|x: &Map<String, Value>| x["is"] == kept["is"] && x["by"] == kept["by"]) {
                return Err(format!("{}: the same instruction by the same person is listed twice", fname));
            }
            instructions.push(kept);
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
    // a definition has to make sense before anything is judged
    let shape = |n: &str| format!("{}: a definition is {{\"from\": [names of facts], \"as\": a Lean function of their values}}", n);
    for i in 0..out.len() {
        let Some(how) = out[i].defined.clone() else { continue };
        let name = out[i].name.clone();
        let from: Vec<String> = match (how.get("from").and_then(Value::as_array), how.get("as").and_then(Value::as_str)) {
            (Some(f), Some(_)) => f.iter().map(|x| x.as_str().map(String::from).ok_or_else(|| shape(&name))).collect::<R<_>>()?,
            _ => return Err(shape(&name)),
        };
        if let Some(missing) = from.iter().find(|x| !out.iter().any(|f| f.name == **x)) {
            return Err(format!("{} is defined from '{}', which is not declared", name, missing));
        }
        let (mut seen, mut todo) = (HashSet::new(), from.clone());
        while let Some(x) = todo.pop() {                // nothing may be defined, however indirectly, from itself
            if x == name {
                return Err(format!("{} is defined in a circle", name));
            }
            if seen.insert(x.clone()) {
                if let Some(Some(d)) = out.iter().find(|f| f.name == x).map(|f| f.defined.as_ref()) {
                    todo.extend(d.get("from").and_then(Value::as_array).into_iter().flatten().filter_map(Value::as_str).map(String::from));
                }
            }
        }
        if how.as_object().map_or(true, |o| o.len() != 2) || from.is_empty() {
            return Err(shape(&name));
        }
        if !out[i].instructions.is_empty() {
            return Err(format!("{}: its value comes from its definition; an instruction belongs to the facts it is defined from", name));
        }
        out[i].defined = Some(json!({ "from": from, "as": norm(how["as"].as_str().unwrap()) }));
    }
    Ok(out)
}

/// Python's str() of a JSON value, as the Python kernel applies it to who gave an instruction.
fn pystr_of(v: &Value) -> String {
    match v {
        Value::String(x) => x.clone(),
        Value::Bool(b) => if *b { "True".into() } else { "False".into() },
        Value::Null => "None".into(),
        other => pyjson(other, false),
    }
}

fn truthy(v: &Value) -> bool {
    match v {
        Value::Null => false,
        Value::Bool(b) => *b,
        Value::String(x) => !x.is_empty(),
        Value::Number(n) => n.as_f64() != Some(0.0),
        Value::Array(a) => !a.is_empty(),
        Value::Object(o) => !o.is_empty(),
    }
}

impl Fact {
    /// The fact as the Python kernel records it in a claim.
    fn recorded(&self) -> Value {
        let places: Vec<Value> = self.places.iter().map(|p| {
            let mut o = Map::new();
            o.insert("at".into(), json!(p.at));
            o.insert("reader".into(), p.reader.clone().unwrap_or(Value::Null));
            if p.some {
                o.insert("some".into(), json!(true));
            }
            Value::Object(o)
        }).collect();
        let mut f = Map::new();
        f.insert("name".into(), json!(self.name));
        f.insert("type".into(), json!(self.typ));
        f.insert("places".into(), json!(places));
        f.insert("asked".into(), json!(self.asked));
        if !self.instructions.is_empty() {
            f.insert("instructions".into(), json!(self.instructions));
        }
        if let Some(d) = &self.defined {
            f.insert("defined".into(), d.clone());
        }
        Value::Object(f)
    }
}

/// Make the standing facts the declared ones: claim what is new or changed, withdraw what is
/// no longer declared (pw/kernel.py sync_facts).
pub fn sync(st: &mut State, facts: &[Fact], file: &str) {
    for f in facts {
        let fact = f.recorded();
        let was = st.facts.get(&f.h).map(|x| {
            let mut x = x.clone();
            x.as_object_mut().map(|o| o.shift_remove("text"));
            x
        });
        if was.as_ref() != Some(&fact) || st.withdrawn.contains_key(&f.h) {
            st.emit("claim", vec![("h", json!(f.h)), ("text", json!(f.text)), ("fact", fact)]);
        }
    }
    for h in st.order.clone() {
        if !facts.iter().any(|f| f.h == h) && !st.withdrawn.contains_key(&h) {
            st.emit("withdraw", vec![("h", json!(h)), ("justification", json!(format!("no longer declared in {}", file)))]);
        }
    }
}

/// Does anything declared need Lean to be judged: a definition, or a type whose values are not
/// written out as JSON? With `always`, every comparison is put to Lean.
pub fn needs_lean(facts: &[Fact], always: bool) -> bool {
    always || facts.iter().any(|f| f.defined.is_some() || !json_like(&f.typ))
}

/// How values are compared: as written (Lean only where a value has to be worked out), or all by Lean.
pub struct Judge {
    pub always: bool,
    pub gate: Gate,
}

impl Judge {
    /// Refuse a value that is not of the fact's type. A written-out value shows its type on its
    /// face; anything else is for Lean to say.
    fn typed(&self, typ: &str, term: &str) -> R<()> {
        if !self.always && json_like(typ) {
            if written(typ, term).is_none() {
                return Err(format!("{} is not a {} written out", term.chars().take(80).collect::<String>(), typ));
            }
            return Ok(());
        }
        self.well_typed(&[(typ, term)])
    }

    fn well_typed(&self, items: &[(&str, &str)]) -> R<()> {
        let (ok, reason) = self.gate.typecheck(items);
        if ok { Ok(()) } else { Err(format!("Lean does not accept this under Gamma: {}", reason)) }
    }
}

/// What has to hold of the declaration before it is judged, and can only be said with Lean at
/// hand: that its types are types, its definitions functions of the right type, its instructions
/// values of the fact's type. (Without Lean, an unknown type passes here and is caught later.)
pub fn premises(facts: &[Fact], judge: &Judge, file: &str) -> R<()> {
    let types: BTreeSet<&str> = facts.iter().map(|f| f.typ.as_str()).collect();
    for t in types.into_iter().filter(|t| !json_like(t)) {
        let (ok, reason) = judge.gate.typecheck(&[("Type", t)]);
        if !ok && !reason.contains("is not installed") && !reason.contains("Gamma pins") {
            return Err(format!("{}: '{}' is not a type Lean knows here; the usual ones are String, Nat, Int, List String, List Nat", file, t));
        }
    }
    for f in facts {
        let Some(how) = &f.defined else { continue };
        let from: Vec<&str> = how["from"].as_array().unwrap().iter().filter_map(Value::as_str).collect();
        let fun = from.iter().map(|x| format!("({})", facts.iter().find(|g| g.name == *x).unwrap().typ)).collect::<Vec<_>>().join(" → ");
        judge.gate.screen(s(how, "as"))?;
        judge.well_typed(&[(&format!("{} → ({})", fun, f.typ), s(how, "as"))])?;
    }
    for f in facts {
        for i in &f.instructions {
            let term = i["is"].as_str().unwrap_or("");
            judge.gate.screen(term)?;
            judge.typed(&f.typ, term)?;
        }
    }
    Ok(())
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

type Said = Option<&'static str>;     // holds, not, contested, or nothing settled

/// The proposition that the given readings agree: compared as written where they are written
/// out, else stated once and settled by Lean. Also says whether the proposition is new to the fact.
fn agreement(st: &mut State, judge: &Judge, h: &str, typ: &str, guards: &[String], terms: &[&str]) -> (Said, bool) {
    if !judge.always {
        let values: Option<Vec<Value>> = terms.iter().map(|t| written(typ, t)).collect();
        if let Some(v) = values {
            return (Some(if v.iter().all(|x| *x == v[0]) { "holds" } else { "not" }), false);
        }
    }
    let parts: Vec<String> = terms[1..].iter().map(|x| format!("((({}) : {}) = (({}) : {}))", terms[0], typ, x, typ)).collect();
    let lean = if parts.is_empty() { "True".to_string() } else { parts.join(" ∧ ") };
    settle(st, judge, h, guards, &lean)
}

/// The proposition that every entry a place lists is an entry of the whole list.
fn contained(st: &mut State, judge: &Judge, h: &str, typ: &str, guards: &[String], part: &str, whole: &str) -> (Said, bool) {
    if !judge.always {
        if let (Some(Value::Array(a)), Some(Value::Array(b))) = (written(typ, part), written(typ, whole)) {
            return (Some(if a.iter().all(|x| b.contains(x)) { "holds" } else { "not" }), false);
        }
    }
    settle(st, judge, h, guards, &format!("(∀ x ∈ (({}) : {}), x ∈ (({}) : {}))", part, typ, whole, typ))
}

/// What the record's proofs say of a proposition; where they say nothing, ask Lean.
fn settle(st: &mut State, judge: &Judge, h: &str, guards: &[String], lean: &str) -> (Said, bool) {
    let f = format!("F:{}", sha(&[lean]));
    let key = (guards.to_vec(), f.clone());
    let new = !st.agreed.get(h).map_or(false, |a| a.contains(&key));
    if new {
        st.emit("agree", vec![("h", json!(h)), ("f", json!(f)), ("lean", json!(lean)), ("guards", json!(guards))]);
    }
    let prop = st.props.entry(f.clone()).or_insert_with(|| lean.to_string()).clone();
    if !st.verdict.contains_key(&f) {
        let tries = [("holds", "rfl"), ("holds", "decide"), ("holds", "simp"), ("not", "decide"), ("not", "simp")];
        for (relation, tactic) in tries {
            let v = judge.gate.check(relation, &[("Prop", &prop)], tactic);
            if v.ok {
                st.emit("proof", vec![("relation", json!(relation)), ("args", json!([f])), ("proof_sha", json!(sha(&[tactic]))), ("proof", json!(tactic)),
                                      ("axioms", json!(v.axioms)), ("gamma", json!(v.gamma))]);
                break;
            }
        }
    }
    let said = st.verdict.get(&f).cloned().unwrap_or_default();
    let verdict = if said.len() > 1 { Some("contested") } else if said.contains("holds") { Some("holds") } else if said.contains("not") { Some("not") } else { None };
    (verdict, new)
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

/// What a fact a definition builds on is settled as: (name, type, value), or why it is not.
pub type Given = (String, String, Result<String, String>);

pub fn recheck_fact(st: &mut State, judge: &Judge, fact: &Fact, cwd: &Path, given: Option<&[Given]>) -> R<Value> {
    let h = &fact.h;
    let mut reread = false;
    let asked_of = |p: &Place| if p.some { sha(&[&fact.asked, "some"]) } else { fact.asked.clone() };
    let mut places: Vec<Map<String, Value>> = vec![];
    let mut unread: Vec<Value> = vec![];
    let rejected: HashSet<String> = st.confirmations.iter().filter(|(_, e)| s(e, "outcome") == "rejected").map(|(_, e)| s(e, "target").to_string()).collect();
    for decl in &fact.places {
        let (at, asked) = (&decl.at, asked_of(decl));
        let now = subject_id(at, cwd);
        let mut about = Map::new();
        about.insert("at".into(), json!(at));
        about.insert("question".into(), json!(format!("{}: {}{}", fact.name, fact.text, if decl.some { SOME } else { "" })));
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
                judge.gate.screen(&obj)?;
                if !st.objs.contains_key(&format!("O:{}", sha(&[&fact.typ, &obj]))) {     // (a value read before was looked at then)
                    judge.typed(&fact.typ, &obj)?;
                }
                Ok(obj)
            });
            match computed {
                Ok(obj) => {
                    let o = format!("O:{}", sha(&[&fact.typ, &obj]));
                    let m = format!("M:{}", sha(&[h, &now, &o, &pyjson(how, true)]));
                    if !st.readings.get(h).map_or(false, |l| l.contains(&(at.clone(), m.clone()))) {
                        st.emit("reading", vec![
                            ("h", json!(h)), ("place", json!(at)), ("subject", json!(now)), ("m", json!(m)),
                            ("obj", json!({ "id": o, "type": fact.typ, "text": obj })), ("binding", how.clone()), ("quote", Value::Null),
                            ("asked", json!(asked)), ("blind", json!(false)), ("model", Value::Null), ("literal", json!(false)), ("anchor", json!(false)),
                        ]);
                    }
                    reread = reread || (!seen.is_empty() && have.last() != Some(&m));
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
    entry.insert("places".into(), Value::Null);       // (filled in below; the keys come in the order the Python check gives them)

    // what people have laid down, and which of it can be used
    let mut said = fact.instructions.clone();
    for a in 0..said.len() {
        for b in a + 1..said.len() {
            let (x, y) = (s(&Value::Object(said[a].clone()), "is").to_string(), s(&Value::Object(said[b].clone()), "is").to_string());
            if x != y && agreement(st, judge, h, &fact.typ, &[], &[&x, &y]).0 != Some("holds") {
                for (i, other) in [(a, b), (b, a)] {
                    let by = said[other]["by"].clone();
                    said[i].entry("set aside").or_insert_with(|| json!([])).as_array_mut().unwrap().push(by);
                }
            }
        }
    }
    let usable: Vec<&Map<String, Value>> = said.iter().filter(|i| !i.contains_key("set aside")).collect();
    if !said.is_empty() {
        entry.insert("instructions".into(), json!(said));
    }
    let mut target = usable.first().map(|i| i["is"].as_str().unwrap_or("").to_string());
    let mut waits: Vec<String> = vec![];
    if let Some(how) = &fact.defined {
        // A definition says nothing new: its value is what its function gives for the facts it is
        // defined from. While one of those is not settled, there is nothing to hold the places against.
        entry.insert("defined".into(), how.clone());
        let given = given.unwrap_or(&[]);
        waits = given.iter().filter_map(|(name, _, v)| v.as_ref().err().map(|why| format!("{} {}", name, why))).collect();
        if given.is_empty() {
            waits.push("the facts it is defined from".into());
        }
        if waits.is_empty() {
            let args: Vec<String> = given.iter().map(|(_, typ, v)| format!("(({}) : {})", v.as_ref().unwrap(), typ)).collect();
            target = Some(format!("(({}) {})", s(how, "as"), args.join(" ")));
        }
    }
    let reads = |p: &Map<String, Value>| p["reads as"].as_str().unwrap_or("").to_string();
    let is_some = |p: &Map<String, Value>| p.contains_key("some");
    let whole: Vec<usize> = (0..places.len()).filter(|i| !is_some(&places[*i])).collect();
    let m_of = |p: &Map<String, Value>| p["m"].as_str().unwrap_or("").to_string();
    let state_of = |verdict: Said, new: bool| match verdict {
        Some("holds") => if new && reread { "re-established" } else { "current" },
        Some("not") => "violated",
        Some("contested") => "contested",
        _ => "uncovered",
    };
    let mut state: String;
    if let Some(t) = &target {
        entry.insert("value".into(), json!(t));     // what this fact is settled as, for a definition that builds on it
    }
    if !unread.is_empty() {
        state = if unread.iter().any(|u| s(u, "why").contains("disagree")) { "disputed" } else { "stale" }.into();
        entry.insert("state".into(), json!(state));
        entry.insert("unread".into(), json!(unread));
    } else if !waits.is_empty() {
        state = "waits".into();
        entry.insert("state".into(), json!(state));
        entry.insert("waits for".into(), json!(waits));
    } else if let Some(target) = &target {
        // Someone has laid down what the value is, or a definition gives it. Each place is held
        // against that by itself, so that the places that differ can be named.
        let mut who: Vec<String> = usable.iter().map(|i| i["by"].as_str().unwrap_or("").to_string()).collect();
        who.sort();
        who.dedup();
        let (mut verdicts, mut new) = (vec![], false);
        for p in places.iter_mut() {
            let guards = [m_of(p)];
            let (v, fresh) = if is_some(p) {
                let (v, fresh) = contained(st, judge, h, &fact.typ, &guards, &reads(p), target);
                p.insert("contained".into(), json!(v == Some("holds")));
                if v == Some("not") {
                    p.insert("not in the whole".into(), json!(outside(&reads(p), target)));
                }
                (v, fresh)
            } else {
                agreement(st, judge, h, &fact.typ, &guards, &[&reads(p), target])
            };
            if v == Some("not") && !usable.is_empty() {
                p.insert("against".into(), json!(who));
            } else if v == Some("not") {
                p.insert("differs from the definition".into(), json!(true));
            }
            verdicts.push(v);
            new |= fresh;
        }
        let verdict = if verdicts.contains(&Some("contested")) { Some("contested") } else if verdicts.contains(&Some("not")) { Some("not") }
                      else if verdicts.iter().all(|v| *v == Some("holds")) { Some("holds") } else { None };
        state = state_of(verdict, new).into();
        entry.insert("state".into(), json!(state));
        if fact.defined.is_some() && verdict != Some("holds") {
            entry.insert("gives".into(), json!(judge.gate.evaluate(&fact.typ, target)));     // (to show; that a place differs was settled by a proof)
        }
    } else {
        // the places that state the whole of it have to read the same; a place that states some
        // entries has to list nothing the whole does not have
        let terms: Vec<String> = whole.iter().map(|i| reads(&places[*i])).collect();
        let guards: Vec<String> = whole.iter().map(|i| m_of(&places[*i])).collect();
        let (mut verdict, mut new) = agreement(st, judge, h, &fact.typ, &guards, &terms.iter().map(String::as_str).collect::<Vec<_>>());
        if verdict != Some("holds") {
            for p in places.iter_mut().filter(|p| is_some(p)) {
                p.insert("whole undecided".into(), json!(true));     // nothing to hold a partial listing against yet
            }
        } else {
            for p in places.iter_mut().filter(|p| is_some(p)) {
                let (inside, fresh) = contained(st, judge, h, &fact.typ, &[m_of(p), guards[0].clone()], &reads(p), &terms[0]);
                p.insert("contained".into(), json!(inside == Some("holds")));
                new |= fresh;
                if inside != Some("holds") {
                    verdict = if inside == Some("contested") || verdict == Some("contested") { Some("contested") }
                              else if inside == Some("not") || verdict == Some("not") { Some("not") } else { None };
                }
                if inside == Some("not") {
                    p.insert("not in the whole".into(), json!(outside(&reads(p), &terms[0])));
                }
            }
        }
        state = state_of(verdict, new).into();
        entry.insert("state".into(), json!(state));
        if verdict == Some("holds") {
            entry.insert("value".into(), json!(terms[0]));
        }
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
/// of them, then the ones new to it. A definition is held after the facts it is defined from,
/// with what they are settled as.
pub fn recheck(st: &mut State, judge: &Judge, facts: &[Fact], cwd: &Path) -> R<Value> {
    let mut order: Vec<&Fact> = st.order.clone().iter().filter_map(|h| facts.iter().find(|f| f.h == *h)).collect();
    for f in facts {
        if !order.iter().any(|x| x.h == f.h) {
            order.push(f);
        }
    }
    fn entry(st: &mut State, judge: &Judge, facts: &[Fact], cwd: &Path, f: &Fact, above: &[String], done: &mut HashMap<String, Value>) -> R<Value> {
        if let Some(d) = done.get(&f.h) {
            return Ok(d.clone());
        }
        let mut given: Option<Vec<Given>> = None;
        if let Some(how) = &f.defined {
            let mut g = vec![];
            for name in how["from"].as_array().unwrap().iter().filter_map(Value::as_str) {
                match facts.iter().find(|x| x.name == name) {
                    None => g.push((name.to_string(), String::new(), Err("is not declared".to_string()))),
                    Some(src) if src.h == f.h || above.contains(&src.h) => g.push((name.to_string(), String::new(), Err("is defined in a circle".to_string()))),
                    Some(src) => {
                        let mut up = above.to_vec();
                        up.push(f.h.clone());
                        let e = entry(st, judge, facts, cwd, src, &up, done)?;
                        g.push((name.to_string(), src.typ.clone(), match e.get("value").and_then(Value::as_str) {
                            Some(v) => Ok(v.to_string()),
                            None => Err(format!("is {}", s(&e, "state"))),
                        }));
                    }
                }
            }
            given = Some(g);
        }
        let d = recheck_fact(st, judge, f, cwd, given.as_deref())?;
        done.insert(f.h.clone(), d.clone());
        Ok(d)
    }
    let mut done = HashMap::new();
    let mut decisions = vec![];
    for f in order {
        decisions.push(entry(st, judge, facts, cwd, f, &[], &mut done)?);
    }
    Ok(json!({ "decisions": decisions }))
}
