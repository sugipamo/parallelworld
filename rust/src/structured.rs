//! Ways of reading by structure for what a pattern used to have to read: a column (or one cell)
//! of a Markdown table, a YAML file by a dotted path (as TOML and JSON), and a Rust item: the
//! value of a const or static, the string literals in an item, or the names an item declares.
//! Nothing is evaluated: only what is written out is taken.
use crate::read::Lit;
use crate::util::*;
use serde_json::{json, Value};

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

// ---- Markdown tables ----------------------------------------------------------------------------

/// A cell as it reads: spacing, and one pair of backticks around the whole of it, aside.
fn cell(text: &str) -> String {
    let t = text.trim();
    let t = if t.len() >= 2 && t.starts_with('`') && t.ends_with('`') && !t[1..t.len() - 1].contains('`') { &t[1..t.len() - 1] } else { t };
    t.trim().to_string()
}

fn cells(line: &str) -> Vec<String> {
    let mut out = vec![];
    let mut cur = String::new();
    let mut chars = line.trim().trim_start_matches('|').chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' if chars.peek() == Some(&'|') => { cur.push('|'); chars.next(); }
            '|' => out.push(std::mem::take(&mut cur)),
            other => cur.push(other),
        }
    }
    if !cur.trim().is_empty() {
        out.push(cur);
    }
    out.iter().map(|c| cell(c)).collect()
}

/// The tables in a text: (header cells, rows of cells). A table is a header row, a row of
/// dashes, and the rows after it, each starting with `|`; fenced code is not looked into.
fn tables(text: &str) -> Vec<(Vec<String>, Vec<Vec<String>>)> {
    let lines: Vec<&str> = text.lines().collect();
    let rule = regex::Regex::new(r"^\s*\|?\s*:?-{3,}:?\s*(\|\s*:?-{3,}:?\s*)*\|?\s*$").unwrap();
    let (mut out, mut fenced, mut i) = (vec![], false, 0);
    while i < lines.len() {
        if lines[i].trim_start().starts_with("```") {
            fenced = !fenced;
        }
        if !fenced && lines[i].trim_start().starts_with('|') && i + 1 < lines.len() && rule.is_match(lines[i + 1]) {
            let head = cells(lines[i]);
            let mut rows = vec![];
            let mut j = i + 2;
            while j < lines.len() && lines[j].trim_start().starts_with('|') {
                rows.push(cells(lines[j]));
                j += 1;
            }
            out.push((head, rows));
            i = j;
            continue;
        }
        i += 1;
    }
    out
}

pub fn read_table(rd: &Value, text: &str) -> R<Lit> {
    let column = s(rd, "column");
    let found: Vec<_> = tables(text).into_iter().filter(|(h, _)| h.iter().any(|c| c == column)).collect();
    if found.len() != 1 {
        return Err(format!("a table with the column {} is found {} times here; it has to be exactly one", pyrepr(column), found.len()));
    }
    let (head, rows) = &found[0];
    let at = head.iter().position(|c| c == column).unwrap();
    match rd.get("row").and_then(Value::as_str) {
        Some(key) => {
            let hits: Vec<&Vec<String>> = rows.iter().filter(|r| r.first().map(String::as_str) == Some(key)).collect();
            if hits.len() != 1 {
                return Err(format!("the row {} is found {} times in the table; it has to be exactly one", pyrepr(key), hits.len()));
            }
            Ok(Lit::One(json!(hits[0].get(at).cloned().unwrap_or_default())))
        }
        None => Ok(Lit::Many(rows.iter().filter_map(|r| r.get(at)).filter(|c| !c.is_empty()).map(|c| json!(c)).collect())),
    }
}

// ---- YAML ----------------------------------------------------------------------------------------

pub fn yaml_value(text: &str) -> R<Value> {
    use yaml_rust2::{Yaml, YamlLoader};
    fn conv(y: &Yaml) -> Value {
        match y {
            Yaml::Real(r) => r.parse::<f64>().map(|f| json!(f)).unwrap_or_else(|_| json!(r)),
            Yaml::Integer(i) => json!(i),
            Yaml::String(x) => json!(x),
            Yaml::Boolean(b) => json!(b),
            Yaml::Array(a) => Value::Array(a.iter().map(conv).collect()),
            Yaml::Hash(h) => Value::Object(h.iter().map(|(k, v)| (match k {
                Yaml::String(x) => x.clone(),
                Yaml::Integer(i) => i.to_string(),
                Yaml::Boolean(b) => b.to_string(),
                Yaml::Real(r) => r.clone(),
                _ => String::new(),
            }, conv(v))).collect()),
            _ => Value::Null,
        }
    }
    let docs = YamlLoader::load_from_str(text).map_err(|e| format!("the file does not parse as yaml: {}", e))?;
    Ok(docs.first().map(conv).unwrap_or(Value::Null))
}

// ---- Rust ----------------------------------------------------------------------------------------

/// The items a name names: `NAME` a const, static, fn, enum, struct, trait, type or mod;
/// `impl NAME` the impl blocks of that type (whatever trait they implement); `a::b` inside mod a.
fn items_named<'a>(items: &'a [syn::Item], path: &str) -> Vec<&'a syn::Item> {
    let (blocks, path) = match path.strip_prefix("impl ") { Some(rest) => (true, rest.trim()), None => (false, path) };
    let mut scope: Vec<&syn::Item> = items.iter().collect();
    let steps: Vec<&str> = path.split("::").collect();
    for (n, step) in steps.iter().enumerate() {
        let here: Vec<&syn::Item> = scope.iter().filter(|i| item_name(i).as_deref() == Some(*step)).cloned().collect();
        if n + 1 == steps.len() {
            return here.into_iter().filter(|i| matches!(i, syn::Item::Impl(_)) == blocks).collect();
        }
        scope = here.iter().filter_map(|i| match i { syn::Item::Mod(m) => m.content.as_ref().map(|(_, c)| c), _ => None }).flatten().collect();
    }
    vec![]
}

fn item_name(i: &syn::Item) -> Option<String> {
    Some(match i {
        syn::Item::Const(x) => x.ident.to_string(),
        syn::Item::Static(x) => x.ident.to_string(),
        syn::Item::Fn(x) => x.sig.ident.to_string(),
        syn::Item::Enum(x) => x.ident.to_string(),
        syn::Item::Struct(x) => x.ident.to_string(),
        syn::Item::Mod(x) => x.ident.to_string(),
        syn::Item::Trait(x) => x.ident.to_string(),
        syn::Item::Type(x) => x.ident.to_string(),
        syn::Item::Impl(x) => match x.self_ty.as_ref() {
            syn::Type::Path(p) => p.path.segments.last()?.ident.to_string(),
            _ => return None,
        },
        _ => return None,
    })
}

fn lit_value(l: &syn::Lit) -> Option<Value> {
    match l {
        syn::Lit::Str(x) => Some(json!(x.value())),
        syn::Lit::Int(x) => x.base10_parse::<i64>().ok().map(|i| json!(i)),
        syn::Lit::Float(x) => x.base10_parse::<f64>().ok().map(|f| json!(f)),
        syn::Lit::Bool(x) => Some(json!(x.value)),
        _ => None,
    }
}

fn expr_lit(e: &syn::Expr, what: &str) -> R<Lit> {
    let bad = || format!("{} is not written out as a literal", what);
    let one = |e: &syn::Expr| -> R<Value> {
        match e {
            syn::Expr::Lit(l) => lit_value(&l.lit).ok_or_else(bad),
            syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Neg(_)) => match u.expr.as_ref() {
                syn::Expr::Lit(l) => match lit_value(&l.lit) {
                    Some(Value::Number(n)) if n.is_i64() => Ok(json!(-n.as_i64().unwrap())),
                    Some(Value::Number(n)) => Ok(json!(-n.as_f64().unwrap_or(0.0))),
                    _ => Err(bad()),
                },
                _ => Err(bad()),
            },
            syn::Expr::Group(g) => match g.expr.as_ref() { syn::Expr::Lit(l) => lit_value(&l.lit).ok_or_else(bad), _ => Err(bad()) },
            _ => Err(bad()),
        }
    };
    match e {
        syn::Expr::Array(a) => Ok(Lit::Many(a.elems.iter().map(one).collect::<R<_>>()?)),
        syn::Expr::Reference(r) => expr_lit(&r.expr, what),
        syn::Expr::Group(g) => expr_lit(&g.expr, what),
        other => Ok(Lit::One(one(other)?)),
    }
}

/// Every string literal in a stream of tokens, macros' included (json!, vec!, format! are tokens to syn).
fn token_strings(tokens: proc_macro2::TokenStream, out: &mut Vec<Value>) {
    for t in tokens {
        match t {
            proc_macro2::TokenTree::Group(g) => token_strings(g.stream(), out),
            proc_macro2::TokenTree::Literal(l) => {
                if let Ok(syn::Lit::Str(x)) = syn::parse_str::<syn::Lit>(&l.to_string()) {
                    out.push(json!(x.value()));
                }
            }
            _ => {}
        }
    }
}

pub fn read_rust(rd: &Value, text: &str) -> R<Lit> {
    let file = syn::parse_file(text).map_err(|e| format!("the file does not parse as Rust: {}", e))?;
    let name = s(rd, "item");
    let found = items_named(&file.items, name);
    if found.is_empty() {
        return Err(format!("{} is not an item of this file", pyrepr(name)));
    }
    match s(rd, "take") {
        "value" => {
            let exprs: Vec<&syn::Expr> = found.iter().filter_map(|i| match i {
                syn::Item::Const(c) => Some(c.expr.as_ref()),
                syn::Item::Static(c) => Some(c.expr.as_ref()),
                _ => None,
            }).collect();
            if exprs.len() != 1 {
                return Err(format!("{} is not one const or static", pyrepr(name)));
            }
            expr_lit(exprs[0], name)
        }
        "fields" => {
            let structs: Vec<&syn::ItemStruct> = found.iter().filter_map(|i| match i { syn::Item::Struct(s) => Some(s), _ => None }).collect();
            if structs.len() != 1 {
                return Err(format!("{} is not one struct", pyrepr(name)));
            }
            Ok(Lit::Many(serde_fields(structs[0]).into_iter().map(|n| json!(n)).collect()))
        }
        "arms" => Ok(Lit::Many(found.iter().flat_map(|i| arm_strings(i)).map(|n| json!(n)).collect())),
        "strings" => {
            let mut out = vec![];
            for i in &found {
                token_strings(quote_item(i), &mut out);
            }
            Ok(Lit::Many(out))
        }
        _ => {
            let mut names = vec![];
            for i in &found {
                match i {
                    syn::Item::Enum(e) => names.extend(e.variants.iter().map(|v| v.ident.to_string())),
                    syn::Item::Struct(st) => names.extend(st.fields.iter().filter_map(|f| f.ident.as_ref().map(|x| x.to_string()))),
                    syn::Item::Impl(im) => names.extend(im.items.iter().filter_map(|x| match x { syn::ImplItem::Fn(f) => Some(f.sig.ident.to_string()), _ => None })),
                    syn::Item::Mod(m) => names.extend(m.content.iter().flat_map(|(_, c)| c.iter().filter_map(item_name))),
                    syn::Item::Trait(t) => names.extend(t.items.iter().filter_map(|x| match x { syn::TraitItem::Fn(f) => Some(f.sig.ident.to_string()), _ => None })),
                    _ => {}
                }
            }
            Ok(Lit::Many(names.into_iter().map(|n| json!(n)).collect()))
        }
    }
}

/// A struct's fields as serde writes and reads them: `rename` applied, `skip` left out.
fn serde_fields(st: &syn::ItemStruct) -> Vec<String> {
    let mut out = vec![];
    for f in &st.fields {
        let Some(ident) = &f.ident else { continue };
        let (mut name, mut skip) = (ident.to_string().trim_start_matches("r#").to_string(), false);
        for a in f.attrs.iter().filter(|a| a.path().is_ident("serde")) {
            let _ = a.parse_nested_meta(|m| {
                if m.path.is_ident("rename") {
                    if let Ok(v) = m.value() { if let Ok(s) = v.parse::<syn::LitStr>() { name = s.value(); } }
                } else if m.path.is_ident("skip") || m.path.is_ident("skip_deserializing") {
                    skip = true;
                } else if let Ok(v) = m.value() {
                    let _ = v.parse::<syn::Expr>();          // (another key = value: not ours)
                }
                Ok(())
            });
        }
        if !skip {
            out.push(name);
        }
    }
    out
}

/// The string literals the arms of `match` expressions in an item match on.
fn arm_strings(item: &syn::Item) -> Vec<String> {
    use syn::visit::Visit;
    struct Arms(Vec<String>);
    fn pat(p: &syn::Pat, out: &mut Vec<String>) {
        match p {
            syn::Pat::Lit(l) => if let syn::Lit::Str(s) = &l.lit { out.push(s.value()) },
            syn::Pat::Or(o) => o.cases.iter().for_each(|c| pat(c, out)),
            syn::Pat::Paren(x) => pat(&x.pat, out),
            syn::Pat::Ident(i) => if let Some((_, sub)) = &i.subpat { pat(sub, out) },
            _ => {}
        }
    }
    impl<'a> Visit<'a> for Arms {
        fn visit_arm(&mut self, arm: &'a syn::Arm) {
            pat(&arm.pat, &mut self.0);
            syn::visit::visit_arm(self, arm);
        }
    }
    let mut v = Arms(vec![]);
    v.visit_item(item);
    v.0
}

/// The lines of the items a Rust way of reading takes, as they stand (for a blind reader).
pub fn rust_lines(rd: &Value, text: &str) -> Option<String> {
    use syn::spanned::Spanned;
    let file = syn::parse_file(text).ok()?;
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let mut shown = String::new();
    for i in items_named(&file.items, s(rd, "item")) {
        let span = i.span();
        let (a, b) = (span.start().line, span.end().line);       // 1-based
        if a == 0 || b < a || b > lines.len() {
            return None;
        }
        shown.push_str(&lines[a - 1..b].concat());
    }
    if shown.is_empty() { None } else { Some(shown) }
}

/// The lines of the table a table reading takes, as they stand.
pub fn table_lines(rd: &Value, text: &str) -> Option<String> {
    let column = s(rd, "column");
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let starts: Vec<usize> = (0..lines.len()).filter(|i| lines[*i].trim_start().starts_with('|') && (*i == 0 || !lines[i - 1].trim_start().starts_with('|'))).collect();
    let mut found = vec![];
    for a in starts {
        let b = (a..lines.len()).take_while(|j| lines[*j].trim_start().starts_with('|')).last()? + 1;
        if cells(lines[a]).iter().any(|c| c == column) {
            found.push(lines[a..b].concat());
        }
    }
    if found.len() == 1 { found.pop() } else { None }
}

/// An item's source as tokens (to look for string literals in it, macros included).
fn quote_item(i: &syn::Item) -> proc_macro2::TokenStream {
    let mut out = proc_macro2::TokenStream::new();
    quote::ToTokens::to_tokens(i, &mut out);
    out
}
