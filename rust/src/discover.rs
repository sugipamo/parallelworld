//! Look for the places a declaration misses, and for things not declared yet (pw discover).
//! (Being ported from pw/discover.py.)
use crate::util::R;
use serde_json::{json, Value};

/// The tools a searching agent answers through (PW_TOOLS=find).
pub fn find_tools() -> Value {
    json!([])
}

pub fn call_find(name: &str, _args: &Value) -> Value {
    json!({ "error": format!("ValueError: no tool {}", name) })
}

pub fn command(_args: &[String]) -> R<i32> {
    Err("pw discover is not there yet".into())
}
