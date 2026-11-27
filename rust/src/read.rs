//! Finding the place a declaration names, and reading a value off it.
use crate::util::*;
use regex::RegexBuilder;
use rustpython_parser::ast::{self, Constant, Expr, Ranged, Stmt};
use serde_json::{json, Map, Value};
use std::path::Path;

pub fn rx(pattern: &str) -> R<regex::Regex> {
    RegexBuilder::new(pattern).multi_line(true).build().map_err(|e| format!("a pattern is not a regular expression: {}", e))
}

// ---- places ---------------------------------------------------------------------------------

pub fn md_section(text: &str, title: &str) -> Option<String> {
    let heading = regex::Regex::new(r"^(#+)\s+(.*?)\s*#*\s*$").unwrap();
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let (mut fenced, mut start, mut level) = (false, None, 0);
    for (i, line) in lines.iter().enumerate() {
        if line.trim_start().starts_with("```") {
            fenced = !fenced;
        }
        if fenced {
            continue;
        }
        let Some(m) = heading.captures(line) else { continue };
        if start.is_none() && m[2].trim() == title.trim() {
            start = Some(i);
            level = m[1].len();
        } else if start.is_some() && m[1].len() <= level {
            return Some(lines[start.unwrap()..i].concat());
        }
    }
    start.map(|s| lines[s..].concat())
}

pub fn json_part(text: &str, keys: &str) -> Option<String> {
    let mut part: Value = serde_json::from_str(text).ok()?;
    for key in keys.split('.') {
        part = match part {
            Value::Array(a) => a.get(key.parse::<usize>().ok()?)?.clone(),
            Value::Object(o) => o.get(key)?.clone(),
            _ => return None,
        };
    }
    Some(pyjson(&part, true))
}

pub fn parse_python(text: &str) -> Option<Vec<Stmt>> {
    match rustpython_parser::parse(text, rustpython_parser::Mode::Module, "<place>").ok()? {
        ast::Mod::Module(m) => Some(m.body),
        _ => None,
    }
}

fn stmt_name(s: &Stmt) -> Option<&str> {
    match s {
        Stmt::FunctionDef(f) => Some(f.name.as_str()),
        Stmt::AsyncFunctionDef(f) => Some(f.name.as_str()),
        Stmt::ClassDef(c) => Some(c.name.as_str()),
        _ => None,
    }
}

fn stmt_body(s: &Stmt) -> &[Stmt] {
    match s {
        Stmt::FunctionDef(f) => &f.body,
        Stmt::AsyncFunctionDef(f) => &f.body,
        Stmt::ClassDef(c) => &c.body,
        _ => &[],
    }
}

/// The source of a definition or assignment, by dotted name (Class.method).
pub fn py_part(text: &str, name: &str) -> Option<String> {
    let module = parse_python(text)?;
    let mut body: &[Stmt] = &module;
    let mut node: Option<&Stmt> = None;
    for part in name.split('.') {
        node = body.iter().find(|n| {
            stmt_name(n) == Some(part)
                || matches!(n, Stmt::Assign(a) if a.targets.iter().any(|t| matches!(t, Expr::Name(x) if x.id.as_str() == part)))
        });
        body = stmt_body(node?);
    }
    let r = node?.range();
    Some(text[usize::from(r.start())..usize::from(r.end())].to_string())
}

fn part_of(path: &str, part: &str, text: &str) -> Option<String> {
    if path.ends_with(".md") || path.ends_with(".markdown") {
        md_section(text, part)
    } else if path.ends_with(".json") {
        json_part(text, part)
    } else if path.ends_with(".py") {
        py_part(text, part)
    } else {
        None
    }
}

/// The content a subject names, as bytes; None if the file is not there.
pub fn locate(subject: &str, cwd: &Path) -> Option<Vec<u8>> {
    let (path, part) = subject.split_once("::").unwrap_or((subject, ""));
    let full = cwd.join(path);
    if !full.is_file() {
        return None;
    }
    let raw = std::fs::read(full).ok()?;
    if !part.is_empty() {
        if let Ok(text) = std::str::from_utf8(&raw) {
            if let Some(found) = part_of(path, part, text) {
                return Some(found.into_bytes());
            }
        }
    }
    Some(raw)
}

/// Why a declared place cannot be found as named, or None.
pub fn unreadable(subject: &str, cwd: &Path) -> Option<String> {
    let (path, part) = subject.split_once("::").unwrap_or((subject, ""));
    let full = cwd.join(path);
    if !full.is_file() {
        return Some(format!("{} is no longer there", path));
    }
    if part.is_empty() || !(path.ends_with(".md") || path.ends_with(".markdown") || path.ends_with(".json") || path.ends_with(".py")) {
        return None;
    }
    let found = std::fs::read(full).ok().and_then(|raw| String::from_utf8(raw).ok()).and_then(|text| part_of(path, part, &text));
    if found.is_some() { None } else { Some(format!("{} no longer has a part named '{}'", path, part)) }
}

pub fn subject_id(subject: &str, cwd: &Path) -> String {
    match locate(subject, cwd) {
        Some(content) => format!("{}@{}", subject, hex10(&content)),
        None => subject.to_string(),
    }
}

pub fn anchored(quote: &str, subject: &str, cwd: &Path) -> bool {
    locate(subject, cwd).map_or(false, |c| norm(&String::from_utf8_lossy(&c)).contains(&norm(quote)))
}

// ---- ways of reading ------------------------------------------------------------------------

const KINDS: [&str; 4] = ["string", "nat", "int", "permille"];

fn flag(r: &Map<String, Value>, key: &str) -> bool {
    r.get(key).and_then(Value::as_bool).unwrap_or(false)
}

/// The way of reading a place that its declaration describes ("read" in pw-facts.json), in
/// the form the record keeps it in.
pub fn reader(read: &Value, at: &str) -> R<Value> {
    let r = read.as_object().ok_or_else(|| format!("{}: \"read\" is an object", at))?;
    let kind = r.get("as").and_then(Value::as_str).unwrap_or("string");
    if !KINDS.contains(&kind) {
        let mut kinds = KINDS.to_vec();
        kinds.sort();
        return Err(format!("a value is one of {}, not {}", pylist(&kinds), pyrepr(kind)));
    }
    let known = |allowed: &[&str]| -> R<()> {
        let mut extra: Vec<&String> = r.keys().filter(|k| !allowed.contains(&k.as_str())).collect();
        extra.sort();
        if extra.is_empty() { Ok(()) } else { Err(format!("{}: unknown keys in \"read\": {}", at, pylist(&extra))) }
    };
    let ext = Path::new(at.split("::").next().unwrap()).extension().and_then(|e| e.to_str()).unwrap_or("");
    if r.contains_key("table") {
        // a column of a Markdown table (every cell), or one cell of it: the row whose first cell is `row`
        known(&["table", "row", "as", "sort", "unique"])?;
        if !["md", "markdown"].contains(&ext) {
            return Err(format!("{}: \"table\" reads a Markdown file", at));
        }
        let column = r["table"].as_str().filter(|c| !c.trim().is_empty()).ok_or("\"table\" is the heading of a column")?;
        let mut out = Map::new();
        out.insert("language".into(), json!("table"));
        out.insert("column".into(), json!(column.trim()));
        if let Some(row) = r.get("row") {
            out.insert("row".into(), json!(row.as_str().ok_or("\"row\" is the first cell of a row")?.trim()));
        } else {
            out.insert("sort".into(), json!(flag(r, "sort")));
            out.insert("unique".into(), json!(flag(r, "unique")));
        }
        out.insert("as".into(), json!(kind));
        return Ok(Value::Object(out));
    }
    if r.contains_key("rust") {
        known(&["rust", "item", "as", "sort", "unique"])?;
        if ext != "rs" || at.contains("::") {
            return Err(format!("{}: \"rust\" reads a whole .rs file; name the item with \"item\"", at));
        }
        let take = r["rust"].as_str().unwrap_or("");
        if !["value", "strings", "names"].contains(&take) {
            return Err(format!("\"rust\" is one of value, strings, names; not {}", pyrepr(take)));
        }
        let item = r.get("item").and_then(Value::as_str).filter(|i| !i.is_empty()).ok_or("\"rust\" needs \"item\": the name of a const, static, fn, enum, struct, impl or mod (a::b inside mods)")?;
        return Ok(json!({ "language": "rust", "take": take, "item": item, "as": kind, "sort": flag(r, "sort"), "unique": flag(r, "unique") }));
    }
    if r.contains_key("python") || r.contains_key("data") {
        known(&["python", "data", "as", "sort", "unique", "keys", "public", "decorator", "call", "with", "keyword"])?;
        if r.contains_key("python") == r.contains_key("data") {
            return Err("give exactly one of python and data".into());
        }
        let mut out = Map::new();
        out.insert("as".into(), json!(kind));
        out.insert("sort".into(), json!(flag(r, "sort")));
        out.insert("unique".into(), json!(flag(r, "unique")));
        if let Some(take) = r.get("python") {
            if ext != "py" {
                return Err(format!("{}: \"python\" reads a .py file", at));
            }
            let take = take.as_str().unwrap_or("");
            if !["value", "strings", "keys", "names", "keyword"].contains(&take) {
                return Err(format!("\"python\" is one of value, strings, keys, names, keyword; not {}", pyrepr(take)));
            }
            out.insert("language".into(), json!("python"));
            out.insert("take".into(), json!(take));
            if take == "names" {
                out.insert("public".into(), json!(flag(r, "public")));
                if let Some(d) = r.get("decorator").and_then(Value::as_str) {
                    out.insert("decorator".into(), json!(d));
                }
            } else if flag(r, "public") || r.contains_key("decorator") {
                return Err("\"public\" and \"decorator\" go with \"python\": \"names\"".into());
            }
            if take == "keyword" {
                let (Some(call), Some(keyword)) = (r.get("call").and_then(Value::as_str), r.get("keyword").and_then(Value::as_str)) else {
                    return Err("\"python\": \"keyword\" needs \"call\" and \"keyword\" (and \"with\", to say which call)".into());
                };
                out.insert("call".into(), json!(call));
                out.insert("keyword".into(), json!(keyword));
                if let Some(w) = r.get("with") {
                    if !w.is_null() {
                        out.insert("with".into(), w.clone());
                    }
                }
            } else if r.contains_key("call") || r.contains_key("keyword") || r.contains_key("with") {
                return Err("\"call\", \"with\" and \"keyword\" go with \"python\": \"keyword\"".into());
            }
        } else {
            if at.contains("::") {
                return Err(format!("{}: \"data\" reads a whole file; put the path into \"data\", not after ::", at));
            }
            let fmt = match ext {
                "toml" | "lock" => "toml",
                "json" => "json",
                "yml" | "yaml" => "yaml",
                _ => return Err("\"data\" reads a .toml, .json or .yaml file (or a .lock file written as TOML)".into()),
            };
            let path = r["data"].as_str().unwrap_or("");
            let step = regex::Regex::new(r"^(\*|[^.\[\]=*]+(\[[^.\[\]=*]+=[^.\[\]]*\])?)$").unwrap();
            if path.is_empty() || !path.split('.').all(|s| step.is_match(s)) {
                return Err(format!("\"data\" is a dotted path such as package.version, tasks.*, package[name=x].version; not {}", pyrepr(path)));
            }
            out.insert("language".into(), json!("data"));
            out.insert("format".into(), json!(fmt));
            out.insert("path".into(), json!(path));
            out.insert("keys".into(), json!(flag(r, "keys")));
        }
        return Ok(Value::Object(out));
    }
    known(&["find", "find_all", "as", "sort", "unique", "within", "rewrite"])?;
    let (find, find_all) = (r.get("find").and_then(Value::as_str), r.get("find_all").and_then(Value::as_str));
    if find.is_some() == find_all.is_some() {
        return Err("give exactly one of find and find_all".into());
    }
    let plain = |p: &str, what: &str, groups: Option<usize>| -> R<usize> {
        if regex::Regex::new(r"\(\?[=!<P]|\\[1-9]").unwrap().is_match(p) {
            return Err(format!("look-around, back-references and named groups are not accepted in {}", what));
        }
        if regex::Regex::new(r"\(\?[a-zA-Z-]+[:)]").unwrap().is_match(p) {
            return Err(format!("inline flags such as (?m) are not accepted in {}; ^ and $ already match at line ends", what));
        }
        let n = rx(p).map_err(|e| e.replace("a pattern", what))?.captures_len() - 1;
        match groups {
            Some(g) if n != g => Err(format!("{} needs exactly {} group: the part in ( ) is what is taken", what, g)),
            _ => Ok(n),
        }
    };
    plain(find.or(find_all).unwrap(), "a pattern", Some(1))?;
    let mut out = Map::new();
    out.insert("language".into(), json!("pattern"));
    out.insert("as".into(), json!(kind));
    out.insert(if find.is_some() { "find" } else { "find_all" }.into(), json!(find.or(find_all).unwrap()));
    if find_all.is_some() {
        out.insert("sort".into(), json!(flag(r, "sort")));
        out.insert("unique".into(), json!(flag(r, "unique")));
    }
    match r.get("within") {
        Some(Value::String(s)) if !s.is_empty() => {
            plain(s, "`within`", Some(1))?;
            out.insert("within".into(), json!([s]));
        }
        Some(Value::Array(steps)) if !steps.is_empty() => {
            for s in steps {
                plain(s.as_str().ok_or("`within` is a pattern, or a list of patterns")?, "`within`", Some(1))?;
            }
            out.insert("within".into(), json!(steps));
        }
        _ => {}
    }
    if let Some(Value::Array(rw)) = r.get("rewrite") {
        if !rw.is_empty() {
            let (Some(a), Some(b)) = (rw.first().and_then(Value::as_str), rw.get(1).and_then(Value::as_str)) else {
                return Err("`rewrite` is [pattern, replacement]".into());
            };
            if rw.len() != 2 {
                return Err("`rewrite` is [pattern, replacement]".into());
            }
            plain(a, "the pattern of `rewrite`", None)?;
            out.insert("rewrite".into(), json!([a, b]));
        }
    }
    Ok(Value::Object(out))
}

pub fn read_pattern(rd: &Value, text: &str) -> R<String> {
    let mut text = text.replace("\r\n", "\n");
    let groups = |pattern: &str, text: &str| -> R<Vec<String>> {
        Ok(rx(pattern)?.captures_iter(text).map(|c| c.get(1).map_or("", |m| m.as_str()).to_string()).collect())
    };
    if let Some(steps) = rd.get("within").and_then(Value::as_array) {
        for step in steps {
            let found = groups(step.as_str().unwrap_or(""), &text)?;
            if found.len() != 1 {
                return Err(format!("`within` matches {} times here; it has to match exactly once", found.len()));
            }
            text = found.into_iter().next().unwrap();
        }
    }
    let find = rd.get("find").and_then(Value::as_str);
    let mut found = groups(find.or(rd.get("find_all").and_then(Value::as_str)).unwrap_or(""), &text)?;
    if let Some(rw) = rd.get("rewrite").and_then(Value::as_array) {
        let whole = RegexBuilder::new(&format!("^(?:{})$", rw[0].as_str().unwrap_or(""))).build().map_err(|e| e.to_string())?;
        let to = rw[1].as_str().unwrap_or("");
        for piece in found.iter_mut() {
            let m = whole.captures(piece).ok_or_else(|| format!("`rewrite` does not match {} as a whole", pyrepr(piece)))?;
            let mut out = String::new();
            let mut chars = to.chars();
            while let Some(c) = chars.next() {
                if c == '\\' {
                    match chars.next() {
                        Some(d) if d.is_ascii_digit() => out.push_str(m.get(d.to_digit(10).unwrap() as usize).map_or("", |g| g.as_str())),
                        Some(other) => out.push(other),
                        None => {}
                    }
                } else {
                    out.push(c);
                }
            }
            *piece = out;
        }
    }
    let kind = rd["as"].as_str().unwrap_or("string");
    if find.is_some() {
        if found.len() != 1 {
            return Err(format!("the pattern matches {} times here; it has to match exactly once", found.len()));
        }
        return Ok(term(kind, &found[0])?.1);
    }
    if found.is_empty() {
        return Err("the pattern matches nothing here; it has to match at least once".into());
    }
    let values = found.iter().map(|x| term(kind, x)).collect::<R<Vec<_>>>()?;
    listed(rd, values, true)
}

/// A literal, as Python's ast.literal_eval reads it: a value or a list of values.
pub enum Lit {
    One(Value),
    Many(Vec<Value>),
}

fn constant(c: &Constant) -> Option<Value> {
    match c {
        Constant::Str(s) => Some(json!(s)),
        Constant::Int(i) => Some(Value::Number(i.to_string().parse().ok()?)),
        Constant::Float(f) => Some(json!(f)),
        Constant::Bool(b) => Some(json!(b)),
        _ => None,
    }
}

fn literal(e: &Expr, what: &str) -> R<Lit> {
    let bad = || format!("{} is not written out as a literal", what);
    let one = |e: &Expr| -> R<Value> {
        match e {
            Expr::Constant(c) => constant(&c.value).ok_or_else(bad),
            Expr::UnaryOp(u) if matches!(u.op, ast::UnaryOp::USub) => match u.operand.as_ref() {
                Expr::Constant(c) => match &c.value {
                    Constant::Int(i) => Ok(Value::Number(format!("-{}", i).parse().map_err(|_| bad())?)),
                    Constant::Float(f) => Ok(json!(-f)),
                    _ => Err(bad()),
                },
                _ => Err(bad()),
            },
            _ => Err(bad()),
        }
    };
    match e {
        Expr::List(l) => Ok(Lit::Many(l.elts.iter().map(one).collect::<R<_>>()?)),
        Expr::Tuple(l) => Ok(Lit::Many(l.elts.iter().map(one).collect::<R<_>>()?)),
        Expr::Set(l) => {
            let mut v: Vec<Value> = l.elts.iter().map(one).collect::<R<_>>()?;
            v.sort_by_key(|x| x.to_string());
            Ok(Lit::Many(v))
        }
        other => Ok(Lit::One(one(other)?)),
    }
}

fn value_term(rd: &Value, v: &Value) -> R<(Key, String)> {
    let kind = rd["as"].as_str().unwrap_or("string");
    match v {
        Value::String(s) if kind == "string" => term(kind, s),
        Value::String(s) if kind != "string" => term(kind, s),
        Value::Number(n) if kind != "string" => {
            let text = match n.as_f64() {
                Some(f) if n.is_f64() && f.fract() == 0.0 => format!("{:.1}", f),
                _ => n.to_string(),
            };
            term(kind, &text)
        }
        other => Err(format!("{} is not a {}", other, kind)),
    }
}

pub fn lit_term(rd: &Value, lit: Lit) -> R<String> {
    match lit {
        Lit::One(v) => Ok(value_term(rd, &v)?.1),
        Lit::Many(vs) => {
            if vs.is_empty() {
                return Err("nothing is found here; a list has to have at least one entry".into());
            }
            listed(rd, vs.iter().map(|v| value_term(rd, v)).collect::<R<_>>()?, true)
        }
    }
}

pub fn dedent(text: &str) -> String {
    let lead = |l: &str| l.chars().take_while(|c| *c == ' ' || *c == '\t').collect::<String>();
    let mut common: Option<String> = None;
    for l in text.lines().filter(|l| !l.trim().is_empty()) {
        let w = lead(l);
        common = Some(match common {
            None => w,
            Some(c) => c.chars().zip(w.chars()).take_while(|(a, b)| a == b).map(|(a, _)| a).collect(),
        });
    }
    let common = common.unwrap_or_default();
    text.split_inclusive('\n').map(|l| if l.trim().is_empty() { "\n".to_string() } else { l.strip_prefix(&common).unwrap_or(l).to_string() }).collect()
}

fn dotted(e: &Expr) -> Option<String> {
    match e {
        Expr::Name(n) => Some(n.id.to_string()),
        Expr::Attribute(a) => Some(format!("{}.{}", dotted(&a.value)?, a.attr)),
        _ => None,
    }
}

struct Calls<'a> {
    name: &'a str,
    with: Option<&'a Value>,
    found: Vec<ast::ExprCall>,
}

impl<'a> ast::Visitor for Calls<'a> {
    fn visit_expr_call(&mut self, node: ast::ExprCall) {
        let named = match node.func.as_ref() {
            Expr::Attribute(a) => a.attr.as_str() == self.name,
            Expr::Name(n) => n.id.as_str() == self.name,
            _ => false,
        };
        let with = self.with.map_or(true, |w| node.args.iter().any(|a| matches!(a, Expr::Constant(c) if constant(&c.value).as_ref() == Some(w))));
        if named && with {
            self.found.push(node.clone());
        }
        self.generic_visit_expr_call(node);
    }
}

struct Strings(Vec<Value>);

impl ast::Visitor for Strings {
    fn visit_expr_constant(&mut self, node: ast::ExprConstant) {
        if let Constant::Str(s) = &node.value {
            self.0.push(json!(s));
        }
    }
}

fn read_python(rd: &Value, text: &str) -> R<String> {
    use ast::Visitor;
    let body = parse_python(&dedent(text)).ok_or("the place is not Python that parses")?;
    let one = if body.len() == 1 { Some(&body[0]) } else { None };
    let assigned: Option<&Expr> = match one {
        Some(Stmt::Assign(a)) => Some(&a.value),
        Some(Stmt::AnnAssign(a)) => a.value.as_deref(),
        _ => None,
    };
    let take = rd["take"].as_str().unwrap_or("");
    if take == "names" {
        let inside: &[Stmt] = match one {
            Some(Stmt::ClassDef(c)) => &c.body,
            _ => &body,
        };
        let public = rd.get("public").and_then(Value::as_bool).unwrap_or(false);
        let decorator = rd.get("decorator").and_then(Value::as_str);
        let mut names = vec![];
        for n in inside {
            let (name, decorators) = match n {
                Stmt::FunctionDef(f) => (f.name.as_str(), &f.decorator_list),
                Stmt::AsyncFunctionDef(f) => (f.name.as_str(), &f.decorator_list),
                _ => continue,
            };
            let carries = |want: &str| decorators.iter().any(|d| {
                let target = if let Expr::Call(c) = d { c.func.as_ref() } else { d };
                dotted(target).as_deref() == Some(want)
            });
            if !(public && name.starts_with('_')) && decorator.map_or(true, carries) {
                names.push(json!(name));
            }
        }
        return lit_term(rd, Lit::Many(names));
    }
    if take == "keyword" {
        let call = rd["call"].as_str().unwrap_or("");
        let mut v = Calls { name: call, with: rd.get("with"), found: vec![] };
        for s in body.iter().cloned() {
            v.visit_stmt(s);
        }
        if v.found.len() != 1 {
            return Err(format!("{} calls of {} fit here; it has to be exactly one", v.found.len(), call));
        }
        let keyword = rd["keyword"].as_str().unwrap_or("");
        let given: Vec<&Expr> = v.found[0].keywords.iter().filter(|k| k.arg.as_ref().map(|a| a.as_str()) == Some(keyword)).map(|k| &k.value).collect();
        if given.len() != 1 {
            return Err(format!("the call does not pass {}", keyword));
        }
        return lit_term(rd, literal(given[0], &format!("{} of {}", keyword, call))?);
    }
    let assigned = assigned.ok_or("the place is not one assignment; name it as path::NAME")?;
    match take {
        "value" => lit_term(rd, literal(assigned, "what is assigned")?),
        "keys" => {
            let Expr::Dict(d) = assigned else { return Err("what is assigned is not a dictionary written out".into()) };
            let mut keys = vec![];
            for k in &d.keys {
                match literal(k.as_ref().ok_or("what is assigned is not a dictionary written out")?, "a key")? {
                    Lit::One(v) => keys.push(v),
                    Lit::Many(_) => return Err("a key is not written out as a literal".into()),
                }
            }
            lit_term(rd, Lit::Many(keys))
        }
        _ => {
            let mut s = Strings(vec![]);
            s.visit_expr(assigned.clone());
            lit_term(rd, Lit::Many(s.0))
        }
    }
}

fn toml_value(v: toml::Value) -> Value {
    match v {
        toml::Value::String(s) => json!(s),
        toml::Value::Integer(i) => json!(i),
        toml::Value::Float(f) => json!(f),
        toml::Value::Boolean(b) => json!(b),
        toml::Value::Datetime(d) => json!({ "datetime": d.to_string() }),
        toml::Value::Array(a) => Value::Array(a.into_iter().map(toml_value).collect()),
        toml::Value::Table(t) => Value::Object(t.into_iter().map(|(k, v)| (k, toml_value(v))).collect()),
    }
}

fn pystr_of(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        Value::Bool(true) => "True".into(),
        Value::Bool(false) => "False".into(),
        Value::Null => "None".into(),
        other => other.to_string(),
    }
}

pub fn read_data(rd: &Value, text: &str) -> R<String> {
    let fmt = rd["format"].as_str().unwrap_or("");
    let root: Value = if fmt == "yaml" {
        crate::structured::yaml_value(text)?
    } else if fmt == "toml" {
        toml_value(text.parse::<toml::Table>().map(toml::Value::Table).map_err(|e| format!("the file does not parse as toml: {}", e.message()))?)
    } else {
        serde_json::from_str(text).map_err(|e| format!("the file does not parse as json: {}", e))?
    };
    let path = rd["path"].as_str().unwrap_or("");
    let keys = rd.get("keys").and_then(Value::as_bool).unwrap_or(false);
    let mut nodes = vec![root];
    for step in path.split('.') {
        let (name, cond) = step.split_once('[').unwrap_or((step, ""));
        let mut found = vec![];
        for n in &nodes {
            if name == "*" {
                match n {
                    Value::Object(o) => found.extend(o.values().cloned()),
                    Value::Array(a) => found.extend(a.iter().cloned()),
                    _ => {}
                }
            } else if let Some(x) = n.as_object().and_then(|o| o.get(name)) {
                found.push(x.clone());
            }
        }
        if !cond.is_empty() {
            let (key, want) = cond.trim_end_matches(']').split_once('=').unwrap_or((cond, ""));
            found = found
                .into_iter()
                .flat_map(|n| match n {
                    Value::Array(a) => a,
                    other => vec![other],
                })
                .filter(|x| x.as_object().map_or(false, |o| pystr_of(o.get(key).unwrap_or(&Value::Null)) == want))
                .collect();
        }
        nodes = found;
    }
    let many = path.split('.').any(|s| s == "*") || keys;
    if keys {
        if nodes.is_empty() || !nodes.iter().all(Value::is_object) {
            return Err(format!("{} is not a table here", path));
        }
        let all: Vec<Value> = nodes.iter().flat_map(|n| n.as_object().unwrap().keys().map(|k| json!(k))).collect();
        return lit_term(rd, Lit::Many(all));
    }
    if nodes.is_empty() {
        return Err(format!("{} is not in the file", path));
    }
    if many {
        let all = nodes.into_iter().flat_map(|n| match n {
            Value::Array(a) => a,
            other => vec![other],
        });
        return lit_term(rd, Lit::Many(all.collect()));
    }
    if nodes.len() != 1 {
        return Err(format!("{} is found {} times; it has to be exactly one", path, nodes.len()));
    }
    match nodes.into_iter().next().unwrap() {
        Value::Array(a) => lit_term(rd, Lit::Many(a)),
        other => lit_term(rd, Lit::One(other)),
    }
}

/// The value a way of reading computes for a text, as a Lean term.
pub fn compute(rd: &Value, text: &str) -> R<String> {
    match rd.get("language").and_then(Value::as_str) {
        Some("pattern") => read_pattern(rd, text),
        Some("python") => read_python(rd, text),
        Some("data") => read_data(rd, text),
        Some("table") => crate::structured::read_table(rd, text).and_then(|l| lit_term(rd, l)),
        Some("rust") => crate::structured::read_rust(rd, text).and_then(|l| lit_term(rd, l)),
        other => Err(format!("no way to read a place by {}; the record may come from another version", other.map(pyrepr).unwrap_or_else(|| "None".into()))),
    }
}
