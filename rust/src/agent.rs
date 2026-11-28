//! What is done with agents: blind readers shown one place each (pw maintain), readers measured
//! on planted changes (pw calibrate), and agents that look for places or propose edits (pw
//! discover, pw propagate). Each session is a `claude -p` run whose only tools are this
//! executable's own (`pw mcp`), so that whatever it says goes into the record through the kernel.
use crate::kernel::{self, Judge, State};
use crate::lean::Gate;
use crate::read::locate;
use crate::text;
use crate::util::*;
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

pub fn list(v: &Value, key: &str) -> Vec<Value> {
    v.get(key).and_then(Value::as_array).cloned().unwrap_or_default()
}

/// Python's way of printing a cost rounded to cents (0.1, 0.05, 1.0).
pub fn cents(x: f64) -> String {
    let r = (x * 100.0).round() / 100.0;
    if r.fract() == 0.0 { format!("{:.1}", r) } else { format!("{:.2}", r).trim_end_matches('0').to_string() }
}

fn thousands(n: usize) -> String {
    let d = n.to_string();
    let mut out = String::new();
    for (i, c) in d.chars().enumerate() {
        if i > 0 && (d.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// The command that runs agent sessions: PW_CLAUDE (a test stands in for it there), else `claude`.
pub fn claude() -> String {
    std::env::var("PW_CLAUDE").ok().filter(|x| !x.is_empty()).unwrap_or_else(|| "claude".into())
}

/// Stop before any session is paid for, if a reader could not answer.
pub fn ready() -> R<()> {
    let c = claude();
    let found = Path::new(&c).is_file() || std::env::var_os("PATH").map_or(false, |p| std::env::split_paths(&p).any(|d| d.join(&c).is_file()));
    if !found {
        return Err("Nothing was read. the `claude` command is not on PATH: it runs the readers' sessions.".into());
    }
    Ok(())
}

/// A place a reader is shown: (fact, place, type, what is asked, what surrounds it, the part shown).
#[derive(Clone)]
pub struct Item {
    pub h: String,
    pub at: String,
    pub typ: String,
    pub asked: String,
    pub around: Option<String>,
    pub shown: Option<String>,
}

pub struct Run {
    pub actor: String,
    pub error: Option<String>,
    pub turns: Option<i64>,
    pub cost: f64,
    pub no_answer: Vec<String>,
}

/// The executable that serves the tools: this one.
pub fn me() -> String {
    std::env::current_exe().map(|p| p.display().to_string()).unwrap_or_else(|_| "pw".into())
}

/// Run one `claude -p` session with this executable's MCP tools (`tools`, the names it may call).
pub fn session(prompt: &str, model: &str, budget: f64, env: &[(&str, String)], tools: &[&str], cwd: Option<&Path>) -> (Option<Value>, String) {
    session_reading(prompt, model, budget, env, tools, cwd, &[])
}

/// The same, where the agent may also use some of claude's own tools (`own`, e.g. Read, Grep, Glob:
/// pw discover's searcher reads the repository it runs in). With none, it has only ours.
pub fn session_reading(prompt: &str, model: &str, budget: f64, env: &[(&str, String)], tools: &[&str], cwd: Option<&Path>, own: &[&str]) -> (Option<Value>, String) {
    // (sessions run at once in one process, each with a directory of its own)
    static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    let work = std::env::temp_dir().join(format!("pw-agent-{}-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0), n));
    let _ = std::fs::create_dir_all(&work);
    let envs: serde_json::Map<String, Value> = env.iter().map(|(k, v)| (k.to_string(), json!(v))).collect();
    let cfg = work.join("mcp.json");
    let _ = std::fs::write(&cfg, json!({ "mcpServers": { "pw": { "command": me(), "args": ["mcp"], "env": envs } } }).to_string());
    let mut allowed: Vec<String> = own.iter().map(|t| t.to_string()).collect();
    allowed.extend(tools.iter().map(|t| format!("mcp__pw__{}", t)));
    let r = Command::new(claude())
        .args(["-p", prompt, "--model", model, "--tools", &own.join(","), "--mcp-config"]).arg(&cfg)
        .args(["--strict-mcp-config", "--allowedTools", &allowed.join(","), "--output-format", "json", "--max-budget-usd", &budget.to_string()])
        .current_dir(cwd.unwrap_or(&work)).output();
    let _ = std::fs::remove_dir_all(&work);
    match r {
        Ok(o) => {
            let out = String::from_utf8_lossy(&o.stdout).into_owned();
            let err = String::from_utf8_lossy(&o.stderr).into_owned();
            (serde_json::from_str(&out).ok(), format!("{}{}", out, err))
        }
        Err(e) => (None, e.to_string()),
    }
}

/// One session shown only the text of the given places (at most one per fact): it states what a
/// place says, or says that it does not state the thing, and has no other way to act.
pub fn blind_read(repo: &Path, lean_dir: &Path, model: &str, actor: &str, items: &[Item], budget: f64, db: &Path) -> Run {
    let mut prompt = kernel::READER.to_string();
    for it in items {
        let text = it.shown.clone().unwrap_or_else(|| String::from_utf8_lossy(&locate(&it.at, repo).unwrap_or_default()).into_owned());
        prompt += &format!("\n=== h: {}   place: {}\nAsked: {} (type {})\n", it.h, it.at, it.asked, it.typ);
        if let Some(around) = &it.around {
            prompt += &format!("What surrounds the passage in its file (not the passage; do not read the value from here):\n<<<\n{}\n>>>\n", around);
        }
        if it.shown.is_some() {
            prompt += "Only the parts of the place that are read are shown; the rest of the file is left out.\n";
        }
        prompt += &format!("Passage:\n<<<\n{}\n>>>\n", text);
    }
    let env = [("PW_DB", db.display().to_string()), ("PW_AGENT", actor.to_string()), ("PW_WORKDIR", repo.display().to_string()),
               ("PW_LEAN_DIR", lean_dir.display().to_string()), ("PW_BLIND", "1".into()), ("PW_MODEL", model.to_string()),
               ("PW_INSTRUCTIONS", kernel::instructions_id())];
    let (out, raw) = session(&prompt, model, budget, &env, &["read_place", "not_stated"], None);
    let mut run = Run { actor: actor.to_string(), error: None, turns: None, cost: 0.0, no_answer: vec![] };
    match out {
        None => run.error = Some(raw.chars().rev().take(500).collect::<Vec<_>>().into_iter().rev().collect()),
        Some(o) => {
            run.turns = o.get("num_turns").and_then(Value::as_i64);
            run.cost = o.get("total_cost_usd").and_then(Value::as_f64).unwrap_or(0.0);
            if o.get("is_error").and_then(Value::as_bool).unwrap_or(false) || o.get("subtype").and_then(Value::as_str).map_or(false, |x| x != "success") {
                let what: String = o.get("result").map(|r| r.as_str().map(String::from).unwrap_or_else(|| r.to_string())).unwrap_or_default().chars().take(300).collect();
                run.error = Some(format!("the session ended with {}: {}", o.get("subtype").and_then(Value::as_str).unwrap_or("an error"), what));
            }
        }
    }
    run
}

/// The (fact, place) pairs an actor read or declined, from the record.
pub fn answered(db: &Path, actor: &str) -> Vec<(String, String)> {
    std::fs::read_to_string(db).unwrap_or_default().lines().filter_map(|l| serde_json::from_str::<Value>(l).ok())
        .filter(|e| ["reading", "decline"].contains(&s(e, "type")) && s(e, "actor") == actor)
        .map(|e| (s(&e, "h").to_string(), s(&e, "place").to_string())).collect()
}

/// Read the wanted (fact, place) pairs in sessions that each see one place per fact.
pub fn read_blind(repo: &Path, lean_dir: &Path, db: &Path, wanted: &[(String, String)], model: &str, label: &str, budget: f64) -> R<Vec<Run>> {
    let st = kernel::replay(db)?;
    let mut batches: Vec<Vec<Item>> = vec![];
    for (h, at) in wanted {
        let fact = st.fact(h).ok_or_else(|| format!("{} is not a fact", h))?;
        let places = list(fact, "places");
        let decl = places.iter().find(|p| s(p, "at") == at).ok_or_else(|| format!("{} is not a place of {}", at, h))?;
        let file = |x: &str| x.split("::").next().unwrap_or("").to_string();
        // a place too small to tell what it belongs to is shown with what surrounds it, unless
        // another place of the same fact is in that file: the reader must not see two places of one fact
        let alone = places.iter().all(|p| s(p, "at") == at || file(s(p, "at")) != file(at));
        let text = String::from_utf8_lossy(&locate(at, repo).unwrap_or_default()).into_owned();
        let shown = decl.get("reader").filter(|r| !r.is_null()).and_then(|rd| text::excerpt(rd, &text, 1500));
        let item = Item { h: h.clone(), at: at.clone(), typ: s(fact, "type").to_string(), asked: text::question(fact, decl).0,
                          around: if alone { text::context(at, repo, 300, 8) } else { None }, shown };
        let n = batches.iter().filter(|b| b.iter().any(|i| i.h == *h)).count();
        if n == batches.len() {
            batches.push(vec![]);
        }
        batches[n].push(item);
    }
    // a reader's name is its session's: reading the same places again is another session
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0).to_string();
    let mut parts = vec![model, label, now.as_str()];
    parts.extend(wanted.iter().map(|(_, at)| at.as_str()));
    let tag = sha(&parts)[..6].to_string();
    println!("{} place(s) to read {}, blind, by {} in {} session(s)", wanted.len(), label, model, batches.len());
    let mut runs: Vec<Run> = vec![];
    for (k, group) in batches.chunks(4).enumerate() {
        let done: Vec<Run> = std::thread::scope(|sc| {
            let handles: Vec<_> = group.iter().enumerate().map(|(j, batch)| {
                let actor = format!("{}-{}-{}", label, tag, k * 4 + j);
                sc.spawn(move || blind_read(repo, lean_dir, model, &actor, batch, budget, db))
            }).collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        runs.extend(done);
    }
    for (r, batch) in runs.iter_mut().zip(&batches) {
        let sizes: Vec<String> = batch.iter().map(|i| {
            let n = i.shown.as_ref().map(|x| x.chars().count()).unwrap_or_else(|| locate(&i.at, repo).map_or(0, |b| b.len()));
            format!("{} ({} characters{})", i.at, thousands(n), if i.shown.is_some() { ", in part" } else { "" })
        }).collect();
        let how = r.error.clone().unwrap_or_else(|| format!("{} turns, ${}", r.turns.map_or("None".into(), |t| t.to_string()), cents(r.cost)));
        println!("   {}: {}   read {}", r.actor, how, sizes.join(", "));
        let said = answered(db, &r.actor);
        r.no_answer = batch.iter().filter(|i| !said.contains(&(i.h.clone(), i.at.clone()))).map(|i| i.at.clone()).collect();
        for at in &r.no_answer {        // silence is not a finding about the place
            println!("   {}: NO ANSWER for {}: neither read nor declined; the session failed for this place", r.actor, at);
        }
    }
    Ok(runs)
}

/// Hold the declared facts against the files, recording what is computed, as the given actor.
pub fn recheck(repo: &Path, db: &Path, facts_path: &Path, judge: &Judge, actor: &str) -> R<Value> {
    let facts = kernel::declared(facts_path)?;
    let file = facts_path.file_name().and_then(|n| n.to_str()).unwrap_or("pw-facts.json").to_string();
    kernel::premises(&facts, judge, &file)?;
    kernel::with_record(db, actor, |st: &mut State| {
        kernel::sync(st, &facts, &file);
        kernel::recheck(st, judge, &facts, repo)
    })
}

pub struct Opts {
    pub repo: PathBuf,
    pub lean_dir: PathBuf,
    pub model: String,
    pub second: String,
    pub budget: f64,
}

/// One round of keeping the facts true of the files (pw maintain): read what changed or was never
/// read, blind; have a blind reader look at computed places none has looked at; have a second
/// model read what rests on one reader; then hold everything against the files once more.
pub fn maintain(o: &Opts) -> R<i32> {
    let (repo, db, facts_path) = (&o.repo, o.repo.join("pw-log.jsonl"), o.repo.join("pw-facts.json"));
    let judge = Judge { always: false, gate: Gate::new(o.lean_dir.clone()) };
    let declared = kernel::declared(&facts_path)?;
    if kernel::needs_lean(&declared, false) {
        judge.gate.usable()?;
    }
    let mut report = recheck(repo, &db, &facts_path, &judge, "maintain")?;
    let reader_of = |h: &str, at: &str| declared.iter().find(|f| f.h == h).and_then(|f| f.places.iter().find(|p| p.at == at)).map_or(false, |p| p.reader.is_some());
    let declined_by = |x: &Value, model: &str| list(x, "declined").iter().any(|d| s(d, "model") == model);
    let unread = |report: &Value| -> Vec<(String, String)> {
        // (a place that cannot be found as declared is not for a reader: the declaration has to be repaired)
        list(report, "decisions").iter().flat_map(|d| list(d, "unread").into_iter().map(move |u| (d.clone(), u)))
            .filter(|(d, u)| !reader_of(s(d, "h"), s(u, "at")) && !s(u, "why").contains("disagree") && u.get("broken").is_none() && !declined_by(u, &o.model))
            .map(|(d, u)| (s(&d, "h").to_string(), s(&u, "at").to_string())).collect()
    };
    // computed places no blind reader has looked at: is the way of reading reading the thing asked?
    // A place the model has read already, as it is now, is not read again: that reading counts once
    // the reader is measured, and asking again would only pay for the same answer.
    let unchecked = |report: &Value| -> R<Vec<(String, String)>> {
        let st = kernel::replay(&db)?;
        Ok(list(report, "decisions").iter().flat_map(|d| list(d, "places").into_iter().map(move |p| (d.clone(), p)))
            .filter(|(d, p)| s(p, "by") == "reader" && !p["stands"].as_bool().unwrap_or(false)
                    && !(!list(p, "read blind as").is_empty() || declined_by(p, &o.model) || st.read_blind_already(s(d, "h"), s(p, "at"), s(p, "m"), &o.model)))
            .map(|(d, p)| (s(&d, "h").to_string(), s(&p, "at").to_string())).collect())
    };
    let first = unread(&report);
    if !first.is_empty() || !unchecked(&report)?.is_empty() {
        ready()?;
        // the files are read as they are now, committed or not: a change and the readings of it can go into one commit
        let dirty = Command::new("git").args(["status", "--porcelain", "--", ".", ":(exclude)pw-log.jsonl"]).current_dir(repo).output()
            .map(|x| !String::from_utf8_lossy(&x.stdout).trim().is_empty()).unwrap_or(false);
        if dirty {
            println!("Reading the files as they are now, uncommitted changes included. Commit them together with pw-log.jsonl.");
        }
    }
    let mut silent: Vec<Run> = vec![];
    if !first.is_empty() {
        silent.extend(read_blind(repo, &o.lean_dir, &db, &first, &o.model, "first", o.budget)?);
        report = recheck(repo, &db, &facts_path, &judge, "maintain")?;
    }
    let pattern = unchecked(&report)?;
    if !pattern.is_empty() {
        silent.extend(read_blind(repo, &o.lean_dir, &db, &pattern, &o.model, "pattern", o.budget)?);
        report = recheck(repo, &db, &facts_path, &judge, "maintain")?;
    }
    // a place read only by readers not measured here: read by the model, where that one is measured (else it would not count either)
    if kernel::counts_here(repo, &o.model) {
        let st = kernel::replay(&db)?;
        let unmeasured: Vec<(String, String)> = list(&report, "decisions").iter()
            .flat_map(|d| list(d, "places").into_iter().map(move |p| (d.clone(), p)))
            .filter(|(d, p)| s(p, "by") == "stated" && !p["stands"].as_bool().unwrap_or(false) && !list(p, "unmeasured readers").is_empty()
                    && !st.read_by_model(s(d, "h"), s(p, "at"), s(p, "m"), &o.model))
            .map(|(d, p)| (s(&d, "h").to_string(), s(&p, "at").to_string())).collect();
        if !unmeasured.is_empty() {
            silent.extend(read_blind(repo, &o.lean_dir, &db, &unmeasured, &o.model, "measured", o.budget)?);
            report = recheck(repo, &db, &facts_path, &judge, "maintain")?;
        }
    }
    if !o.second.is_empty() {
        // also where the places disagree: before that is put to a person, the reading that differs should not rest on one reader
        let st = kernel::replay(&db)?;
        let alone: Vec<(String, String)> = list(&report, "decisions").iter()
            .filter(|d| ["current", "re-established", "violated"].contains(&s(d, "state")))
            .flat_map(|d| list(d, "places").into_iter().map(move |p| (d.clone(), p)))
            .filter(|(d, p)| s(p, "by") == "stated" && !p["stands"].as_bool().unwrap_or(false) && !st.read_by_model(s(d, "h"), s(p, "at"), s(p, "m"), &o.second))
            .map(|(d, p)| (s(&d, "h").to_string(), s(&p, "at").to_string())).collect();
        if !alone.is_empty() {
            silent.extend(read_blind(repo, &o.lean_dir, &db, &alone, &o.second, "second", o.budget)?);
        }
    }
    let report = recheck(repo, &db, &facts_path, &judge, "maintain")?;
    let bad = crate::show(&report, false);
    let failed = silent.iter().filter(|r| r.error.is_some() || !r.no_answer.is_empty()).count();
    if failed > 0 {
        println!("\n{} reader session(s) failed or left a place unanswered (see above). That is not a finding: run this again.", failed);
        if silent.iter().all(|r| r.turns.map_or(true, |t| t == 1)) {
            println!("Every session ended after one turn without answering. The readers' tools may not have started: try `{} mcp` by hand; it should start and wait, not fail.", me());
        }
    }
    Ok(if bad || failed > 0 { 1 } else { 0 })
}
