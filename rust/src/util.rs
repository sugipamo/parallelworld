//! Small things that have to come out exactly as the Python implementation writes them:
//! the record's identifiers are hashes of these strings.
use serde_json::Value;
use sha2::{Digest, Sha256};

pub type R<T> = Result<T, String>;

/// `_sha(*parts)`: the first ten hex digits of the SHA-256 of the parts joined by NUL.
pub fn sha(parts: &[&str]) -> String {
    hex10(parts.join("\u{0}").as_bytes())
}

pub fn hex10(bytes: &[u8]) -> String {
    let d = Sha256::digest(bytes);
    d.iter().map(|b| format!("{:02x}", b)).collect::<String>()[..10].to_string()
}

/// `" ".join(text.split())`
pub fn norm(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// `json.dumps(s, ensure_ascii=False)` of a string.
pub fn pystr(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

/// Python's repr of a string, `'a'`: how the Python kernel quoted text in its messages.
pub fn pyrepr(x: &str) -> String {
    let l = pylist(&[x]);
    l[1..l.len() - 1].to_string()
}

/// Python's repr of a list of strings, `['a', 'b']`: how the Python check names keys in its messages.
pub fn pylist<S: AsRef<str>>(items: &[S]) -> String {
    let one = |x: &str| {
        let x = x.replace('\\', "\\\\");
        if x.contains('\'') && !x.contains('"') { format!("\"{}\"", x) } else { format!("'{}'", x.replace('\'', "\\'")) }
    };
    format!("[{}]", items.iter().map(|x| one(x.as_ref())).collect::<Vec<_>>().join(", "))
}

/// `json.dumps(v, ensure_ascii=False[, sort_keys=True])`: ", " and ": " as separators.
pub fn pyjson(v: &Value, sort_keys: bool) -> String {
    match v {
        Value::Array(a) => format!("[{}]", a.iter().map(|x| pyjson(x, sort_keys)).collect::<Vec<_>>().join(", ")),
        Value::Object(o) => {
            let mut keys: Vec<&String> = o.keys().collect();
            if sort_keys {
                keys.sort();
            }
            format!("{{{}}}", keys.iter().map(|k| format!("{}: {}", pystr(k), pyjson(&o[*k], sort_keys))).collect::<Vec<_>>().join(", "))
        }
        Value::String(s) => pystr(s),
        other => other.to_string(),
    }
}

/// Is a value of this type written the same way in JSON and in Lean?
pub fn json_like(typ: &str) -> bool {
    matches!(typ, "String" | "Nat" | "Int" | "List String" | "List Nat" | "List Int")
}

fn unparen(typ: &str, text: &str) -> String {
    if typ.ends_with("Int") {
        regex::Regex::new(r"\((-\d+)\)").unwrap().replace_all(text, "$1").into_owned()
    } else {
        text.to_string()
    }
}

/// The value a written-out term stands for, or None if it is not a plain value of the type.
pub fn written(typ: &str, text: &str) -> Option<Value> {
    if !json_like(typ) {
        return None;
    }
    let v: Value = serde_json::from_str(&unparen(typ, text)).ok()?;
    let base = typ.strip_prefix("List ").unwrap_or(typ);
    let one = |x: &Value| match base {
        "String" => x.is_string(),
        "Nat" => x.is_u64(),
        "Int" => x.is_i64() || x.is_u64(),
        _ => false,
    };
    let ok = if typ.starts_with("List ") { v.as_array().map_or(false, |a| a.iter().all(one)) } else { one(&v) };
    if ok { Some(v) } else { None }
}

/// `_term(kind, text)`: (a key to sort by, the Lean term).
#[derive(Clone, Debug, PartialEq)]
pub enum Key {
    S(String),
    N(i128),
}

impl PartialOrd for Key {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        match (self, o) {
            (Key::S(a), Key::S(b)) => a.partial_cmp(b),
            (Key::N(a), Key::N(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

pub fn term(kind: &str, text: &str) -> R<(Key, String)> {
    let digits = |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_digit());
    let bad = || format!("{} is not a {}", pyrepr(text), kind);
    match kind {
        "string" => Ok((Key::S(text.to_string()), pystr(text))),
        "nat" if digits(text) => {
            let n: i128 = text.parse().map_err(|_| bad())?;
            Ok((Key::N(n), n.to_string()))
        }
        "int" if digits(text.strip_prefix('-').unwrap_or(text)) => {
            let n: i128 = text.parse().map_err(|_| bad())?;
            Ok((Key::N(n), if n >= 0 { n.to_string() } else { format!("({})", n) }))
        }
        "permille" => {
            if text.starts_with('-') {
                return Err(bad());
            }
            let (whole, frac) = text.split_once('.').unwrap_or((text, ""));
            if !digits(whole) || (text.contains('.') && !digits(frac)) {
                return Err(bad());
            }
            let frac = frac.trim_end_matches('0');
            if frac.len() > 3 {
                return Err(bad());
            }
            let n: i128 = whole.parse::<i128>().map_err(|_| bad())? * 1000 + format!("{:0<3}", frac).parse::<i128>().map_err(|_| bad())?;
            Ok((Key::N(n), n.to_string()))
        }
        _ => Err(bad()),
    }
}

/// Values taken from a place, as a Lean term: one value, or a list.
pub fn listed(rd: &Value, items: Vec<(Key, String)>, list: bool) -> R<String> {
    if !list {
        return Ok(items.into_iter().next().map(|v| v.1).unwrap_or_default());
    }
    let mut values = items;
    if rd.get("unique").and_then(Value::as_bool).unwrap_or(false) {
        let mut seen = std::collections::HashSet::new();
        values.retain(|v| seen.insert(v.1.clone()));
    }
    if rd.get("sort").and_then(Value::as_bool).unwrap_or(false) {
        values.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
    }
    Ok(format!("[{}]", values.iter().map(|v| v.1.as_str()).collect::<Vec<_>>().join(", ")))
}
