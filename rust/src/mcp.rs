//! The MCP server through which a reader says what a place states (stdio, one JSON-RPC message
//! per line). The same two tools as pw/mcp_server.py, and no other way to act.
//!
//! Env: PW_DB (the record), PW_AGENT (the reader's name), PW_WORKDIR (the repository),
//! PW_LEAN_DIR (the Lean project), PW_BLIND ("1" if the reader is shown the place and nothing
//! else), PW_MODEL (which model the reader is), PW_INSTRUCTIONS (the id of the instructions it was
//! given; by default those this build has, pw/reader.txt).
use crate::kernel;
use crate::lean;
use serde_json::{json, Value};
use std::io::{BufRead, Write};
use std::path::PathBuf;

const READ_PLACE: &str = "For a FACT (one thing stated in several places): state what one of its places says, as a \
Lean term of the fact's type, e.g. object \"\\\"pqd\\\"\" or \"[\\\"a\\\", \\\"b\\\"]\" or \"14\". `place` is exactly \
as listed for the fact, e.g. \"docs/spec.md::3. Model\". `quote` is the sentence or table row of \
that place which says it, copied word for word (for a list spread over a table, the row of \
one entry); the kernel checks the quote is there and shows it to the person who confirms your \
reading. Write what the place itself says. The kernel compares the places; you prove nothing.";

const NOT_STATED: &str = "For a FACT: say that a place you were shown does not state it. Use this instead of \
`read_place` when the place is about something else, or mentions the thing without saying \
what its value is. `why` says in a sentence what the place is about instead. Declining is \
an answer: a place that is read as something it does not say hides a disagreement.";

fn schema(names: &[&str]) -> Value {
    let props: serde_json::Map<String, Value> = names.iter().map(|n| {
        let title: String = n.chars().take(1).flat_map(char::to_uppercase).chain(n.chars().skip(1)).collect();
        (n.to_string(), json!({ "title": title, "type": "string" }))
    }).collect();
    json!({ "type": "object", "properties": props, "required": names })
}

fn tools() -> Value {
    json!([
        { "name": "read_place", "description": READ_PLACE, "inputSchema": schema(&["h", "place", "object", "quote"]) },
        { "name": "not_stated", "description": NOT_STATED, "inputSchema": schema(&["h", "place", "why"]) },
    ])
}

fn env(name: &str) -> Option<String> {
    std::env::var(name).ok()
}

/// One tool call, under the record's lock: what it says back to the reader.
fn call(name: &str, args: &Value) -> Value {
    let arg = |k: &str| args.get(k).and_then(Value::as_str).unwrap_or("").to_string();
    let db = PathBuf::from(env("PW_DB").unwrap_or_else(|| "pw-log.jsonl".into()));
    let actor = env("PW_AGENT").filter(|x| !x.is_empty()).unwrap_or_else(|| "anon".into());
    let cwd = PathBuf::from(env("PW_WORKDIR").unwrap_or_else(|| ".".into()));
    let (blind, model) = (env("PW_BLIND").as_deref() == Some("1"), env("PW_MODEL"));
    let judge = kernel::Judge { always: false, gate: lean::Gate::new(env("PW_LEAN_DIR").map(PathBuf::from).unwrap_or_else(lean::lean_dir)) };
    let mut told: Option<kernel::Told> = None;
    let out = kernel::with_record(&db, &actor, |st| {
        let r = match name {
            "read_place" => kernel::read_place(st, &judge, &arg("h"), &arg("place"), Some(&arg("object")), &cwd, args.get("quote").and_then(Value::as_str), blind, model.as_deref(), env("PW_INSTRUCTIONS").as_deref()),
            "not_stated" => kernel::decline(st, &arg("h"), &arg("place"), &arg("why"), &cwd, blind, model.as_deref()),
            other => Err(("ValueError", format!("no tool {}", other))),
        };
        r.map_err(|e| { told = Some(e); String::new() })
    });
    match (out, told) {
        (Ok(v), _) => v,
        (Err(_), Some((kind, e))) => json!({ "error": format!("{}: {}", kind, e) }),
        (Err(e), None) => match e.strip_prefix(kernel::GATE) {
            Some(rest) => json!({ "error": format!("GateError: {}", rest) }),
            None => json!({ "error": format!("KernelError: {}", e) }),
        },
    }
}

pub fn serve() -> i32 {
    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        let Ok(msg) = serde_json::from_str::<Value>(&line) else { continue };
        let Some(id) = msg.get("id").cloned() else { continue };          // a notification: nothing to answer
        let params = msg.get("params").cloned().unwrap_or(json!({}));
        let reply = match msg.get("method").and_then(Value::as_str).unwrap_or("") {
            "initialize" => Ok(json!({
                "protocolVersion": params.get("protocolVersion").cloned().unwrap_or(json!("2025-06-18")),
                "capabilities": { "tools": { "listChanged": false } },
                "serverInfo": { "name": "pw", "version": env!("CARGO_PKG_VERSION") },
            })),
            "ping" => Ok(json!({})),
            "tools/list" => Ok(json!({ "tools": tools() })),
            "tools/call" => {
                let r = call(params.get("name").and_then(Value::as_str).unwrap_or(""), params.get("arguments").unwrap_or(&json!({})));
                Ok(json!({ "content": [{ "type": "text", "text": serde_json::to_string_pretty(&r).unwrap() }], "structuredContent": r, "isError": false }))
            }
            _ => Err(json!({ "code": -32601, "message": "Method not found" })),
        };
        let mut answer = json!({ "jsonrpc": "2.0", "id": id });
        match reply {
            Ok(r) => answer["result"] = r,
            Err(e) => answer["error"] = e,
        }
        if writeln!(out, "{}", answer).and_then(|_| out.flush()).is_err() {
            break;
        }
    }
    0
}
