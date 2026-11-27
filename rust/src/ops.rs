//! The kernel and the Lean gate as a program, one request at a time: a JSON object on stdin,
//! a JSON object on stdout ({"ok": what it gives} or {"error": why, "kind": KernelError or
//! GateError}). This is what pw/core.py calls; nothing else in Python judges or writes the record.
//!
//!     pw kernel    {"db", "actor", "lean_dir"?, "always"?, "op": claim|sync|read|decline|sign_off|prove|verify|withdraw|recheck|needs_lean|adopt|state, ...}
//!     pw lean      {"lean_dir"?, "op": check|check_many|typecheck|evaluate|screen|render|gamma|judge|available|usable, ...}
use crate::kernel::{self, Judge, GATE};
use crate::lean::{self, Gate, Verdict};
use crate::util::R;
use serde_json::{json, Value};
use std::path::{Path, PathBuf};

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

fn opt<'a>(v: &'a Value, key: &str) -> Option<&'a str> {
    v.get(key).and_then(Value::as_str)
}

fn gate(req: &Value) -> Gate {
    Gate::new(opt(req, "lean_dir").map(PathBuf::from).unwrap_or_else(lean::lean_dir))
}

fn verdict(v: Verdict) -> Value {
    if v.ok { json!({ "ok": true, "axioms": v.axioms, "gamma": v.gamma }) } else { json!({ "ok": false, "reason": v.reason }) }
}

fn items(v: &Value) -> Vec<(String, String)> {
    v.as_array().into_iter().flatten().map(|x| (x[0].as_str().unwrap_or("").to_string(), x[1].as_str().unwrap_or("").to_string())).collect()
}

/// Answer one request; what goes wrong is said, as the Python kernel named it.
fn reply(out: Result<Value, (String, String)>) -> i32 {
    let v = match out {
        Ok(v) => json!({ "ok": v }),
        Err((kind, e)) => json!({ "error": e, "kind": kind }),
    };
    println!("{}", serde_json::to_string(&v).unwrap());
    0
}

fn told(e: String) -> (String, String) {
    match e.strip_prefix(GATE) {
        Some(rest) => ("GateError".into(), rest.to_string()),
        None => ("KernelError".into(), e.replace(GATE, "")),
    }
}

fn request() -> R<Value> {
    let mut text = String::new();
    std::io::Read::read_to_string(&mut std::io::stdin(), &mut text).map_err(|e| e.to_string())?;
    serde_json::from_str(&text).map_err(|e| format!("a request is one JSON object: {}", e))
}

pub fn kernel() -> i32 {
    let req = match request() { Ok(r) => r, Err(e) => return reply(Err(("ValueError".into(), e))) };
    if let Some(out) = crate::text::op(&req) {          // text, files and measurements: no record involved
        return reply(out.map_err(told));
    }
    if s(&req, "op") == "read_text" {
        // how a declared way of reading reads a place: no record involved
        let cwd = PathBuf::from(opt(&req, "cwd").unwrap_or("."));
        let at = s(&req, "at");
        let out = crate::read::reader(&req["read"], at).and_then(|how| {
            let text = String::from_utf8_lossy(&crate::read::locate(at, &cwd).ok_or(format!("{} is not there", at))?).into_owned();
            Ok(json!({ "reader": how, "value": crate::read::compute(&how, &text)?, "subject": crate::read::subject_id(at, &cwd) }))
        });
        return reply(out.map_err(told));
    }
    let judge = Judge { always: req.get("always").and_then(Value::as_bool).unwrap_or(false), gate: gate(&req) };
    let db = PathBuf::from(s(&req, "db"));
    let actor = opt(&req, "actor").unwrap_or("anon").to_string();
    let cwd = |r: &Value| PathBuf::from(opt(r, "cwd").unwrap_or("."));
    let mut said: Option<(String, String)> = None;       // an error worded for the caller, kept as it is
    let out = kernel::with_record(&db, &actor, |st| -> R<Value> {
        let r = &req;
        let reader_said = |res: Result<Value, kernel::Told>, said: &mut Option<(String, String)>| res.map_err(|(k, e)| { *said = Some((k.to_string(), e)); String::new() });
        Ok(match s(r, "op") {
            "claim" => json!({ "h": kernel::claim_fact(st, &judge, s(r, "name"), s(r, "type"), r["places"].as_array().map(Vec::as_slice).unwrap_or(&[]),
                                                    s(r, "gloss"), r["instructions"].as_array().map(Vec::as_slice).unwrap_or(&[]), r.get("defined"))? }),
            "sync" => {
                let path = Path::new(s(r, "path"));
                let file = path.file_name().and_then(|n| n.to_str()).unwrap_or("pw-facts.json").to_string();
                let facts = kernel::declared(path)?;
                kernel::premises(&facts, &judge, &file)?;
                kernel::sync(st, &facts, &file);
                json!(facts.iter().map(|f| f.h.clone()).collect::<Vec<_>>())
            }
            "read" => reader_said(kernel::read_place(st, &judge, s(r, "h"), s(r, "place"), opt(r, "obj"), &cwd(r), opt(r, "quote"),
                                                     r.get("blind").and_then(Value::as_bool).unwrap_or(false), opt(r, "model"), opt(r, "instructions")), &mut said)?,
            "decline" => reader_said(kernel::decline(st, s(r, "h"), s(r, "place"), s(r, "why"), &cwd(r),
                                                     r.get("blind").and_then(Value::as_bool).unwrap_or(false), opt(r, "model")), &mut said)?,
            "sign_off" => {
                let (eid, duplicate) = kernel::sign_off(st, s(r, "m"), s(r, "who"), r.get("confirmed").and_then(Value::as_bool).unwrap_or(true))?;
                json!({ "eid": eid, "duplicate": duplicate })
            }
            "prove" => kernel::prove(st, &judge, s(r, "relation"), s(r, "f"), opt(r, "proof").unwrap_or(""))?,
            "verify" => json!(kernel::verify(st, &judge, r.get("proofs").and_then(Value::as_array).map(Vec::as_slice))),
            "withdraw" => { kernel::withdraw(st, s(r, "h"), s(r, "justification"))?; json!({ "h": s(r, "h") }) }
            "recheck" => {
                let facts = st.live();
                if kernel::needs_lean(&facts, judge.always) {
                    judge.gate.usable()?;                // what has to be worked out is not judged without Lean
                }
                kernel::recheck(st, &judge, &facts, &cwd(r))?
            }
            "needs_lean" => json!(kernel::needs_lean(&st.live(), judge.always)),
            "adopt" => { st.adopt(r["events"].as_array().map(Vec::as_slice).unwrap_or(&[]))?; Value::Null }
            "state" => st.dump(),
            other => return Err(format!("no operation {}", other)),
        })
    });
    reply(out.map_err(|e| said.take().unwrap_or_else(|| told(e))))
}

pub fn lean() -> i32 {
    let req = match request() { Ok(r) => r, Err(e) => return reply(Err(("ValueError".into(), e))) };
    let g = gate(&req);
    let gate_error = |e: String| ("GateError".to_string(), e);
    let r = &req;
    let pairs = |key: &str| items(&r[key]);
    let borrowed = |v: &[(String, String)]| v.iter().map(|(a, b)| (a.clone(), b.clone())).collect::<Vec<_>>();
    let out = match s(r, "op") {
        "check" => { let it = pairs("items"); let it: Vec<(&str, &str)> = it.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect(); Ok(verdict(g.check(s(r, "relation"), &it, s(r, "proof")))) }
        "check_many" => {
            let jobs: Vec<(String, Vec<(String, String)>, String)> = r["jobs"].as_array().into_iter().flatten()
                .map(|j| (j[0].as_str().unwrap_or("").to_string(), borrowed(&items(&j[1])), j[2].as_str().unwrap_or("").to_string())).collect();
            Ok(json!(g.check_many(&jobs, r.get("batch").and_then(Value::as_u64).unwrap_or(50) as usize).into_iter().map(verdict).collect::<Vec<_>>()))
        }
        "typecheck" => { let it = pairs("items"); let it: Vec<(&str, &str)> = it.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect(); let (ok, reason) = g.typecheck(&it); Ok(json!({ "ok": ok, "reason": reason })) }
        "evaluate" => Ok(json!(g.evaluate(s(r, "typ"), s(r, "term")))),
        "screen" => g.screen(s(r, "text")).map(|_| Value::Null).map_err(gate_error),
        "render" => { let it = pairs("items"); let it: Vec<(&str, &str)> = it.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect(); g.render(s(r, "relation"), &it, s(r, "proof")).map(|x| json!(x)).map_err(gate_error) }
        "gamma" => Ok(json!(g.gamma())),
        "judge" => Ok(verdict(Gate::judge(r.get("returncode").and_then(Value::as_i64).unwrap_or(1) as i32, s(r, "output"), s(r, "gamma")))),
        "available" => Ok(json!(g.available())),
        "usable" => g.usable().map(|_| Value::Null).map_err(gate_error),
        other => Err(("ValueError".to_string(), format!("no operation {}", other))),
    };
    reply(out)
}
