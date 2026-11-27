//! pw check: hold every declared fact against the files as they are now.
mod kernel;
mod lean;
mod mcp;
mod ops;
mod structured;
mod text;
mod read;
mod util;

use serde_json::Value;
use std::path::{Path, PathBuf};
use util::R;

fn cut(s: &str, n: usize) -> String {
    s.chars().take(n).collect()
}

fn s<'a>(v: &'a Value, key: &str) -> &'a str {
    v.get(key).and_then(Value::as_str).unwrap_or("")
}

fn list(v: &Value, key: &str) -> Vec<Value> {
    v.get(key).and_then(Value::as_array).cloned().unwrap_or_default()
}

fn show_str(v: &Value) -> String {
    v.as_str().map(String::from).unwrap_or_else(|| v.to_string())
}

/// For a list whose places do not agree: which entries are not everywhere, and where they are.
fn differences(d: &Value) -> Vec<String> {
    let entries = |text: &str| serde_json::from_str::<Value>(text).ok().and_then(|v| v.as_array().cloned());
    let mut whole = vec![];
    for p in list(d, "places").iter().filter(|p| p.get("some").is_none()) {
        match entries(s(p, "reads as")) {
            Some(v) => whole.push((s(p, "at").to_string(), v)),
            None => return vec![],
        }
    }
    let show = |xs: &[Value]| {
        let mut names: Vec<String> = xs.iter().map(show_str).collect();
        names.sort();
        cut(&names.join(", "), 300)
    };
    let laid = list(d, "instructions").iter().find(|i| i.get("set aside").is_none()).and_then(|i| entries(s(i, "is")));
    let what = if laid.is_some() { "what was laid down" } else { "what the definition gives" };
    if let Some(target) = laid.or_else(|| entries(s(d, "gives"))) {
        let mut out = vec![];
        for (at, v) in &whole {
            let more: Vec<Value> = v.iter().filter(|x| !target.contains(x)).cloned().collect();
            let less: Vec<Value> = target.iter().filter(|x| !v.contains(x)).cloned().collect();
            if !more.is_empty() {
                out.push(format!("{} has, beyond {}: {}", at, what, show(&more)));
            }
            if !less.is_empty() {
                out.push(format!("{} lacks, of {}: {}", at, what, show(&less)));
            }
        }
        return out;
    }
    let mut seen: Vec<(Value, Vec<String>)> = vec![];
    for (at, v) in &whole {
        for x in v {
            match seen.iter_mut().find(|(y, _)| y == x) {
                Some(e) => e.1.push(at.clone()),
                None => seen.push((x.clone(), vec![at.clone()])),
            }
        }
    }
    let mut groups: std::collections::BTreeMap<Vec<String>, Vec<Value>> = Default::default();
    for (x, mut places) in seen {
        places.sort();
        places.dedup();
        if places.len() < whole.len() {
            groups.entry(places).or_default().push(x);
        }
    }
    groups.into_iter().map(|(places, xs)| format!("only in {}: {}", places.join(", "), show(&xs))).collect()
}

/// Print where every fact stands. Returns true if anything needs attention.
fn show(report: &Value, warn: bool) -> bool {
    let mut bad = false;
    let declined = |by: &[Value]| {
        for x in by {
            let who = if s(x, "model").is_empty() { s(x, "actor") } else { s(x, "model") };
            println!("          a blind reader ({}) says the place does not state this: {}", who, cut(s(x, "why"), 200));
            println!("          if it is about something else, take the place out of pw-facts.json; if it says two things, make it say one");
        }
    };
    let decisions = list(report, "decisions");
    for d in &decisions {
        let state = s(d, "state");
        let agree = state == "current" || state == "re-established";
        let places = list(d, "places");
        let loose = places.iter().any(|p| !p["stands"].as_bool().unwrap_or(false));
        let ok = agree && !loose;
        bad |= !ok && !(agree && warn);
        let mark = if ok { "ok  " } else if agree && warn { "WARN" } else { "FAIL" };
        println!("{} {:<15} {} fact: {}", mark, state, s(d, "h"), s(d, "fact"));
        let aside: Vec<Value> = list(d, "instructions").into_iter().filter(|i| i.get("set aside").is_some()).collect();
        if !aside.is_empty() {
            println!("       people's instructions about this cannot both hold. They are set aside until one is withdrawn:");
            for i in &aside {
                let on = if s(i, "on").is_empty() { String::new() } else { format!(" ({})", s(i, "on")) };
                let words = if s(i, "said").is_empty() { String::new() } else { format!("  \"{}\"", cut(s(i, "said"), 120)) };
                println!("          {}{}: {}{}", s(i, "by"), on, cut(s(i, "is"), 100), words);
            }
            if let Some(w) = d.get("without the instructions set aside") {
                println!("       judged without them, the fact is: {}", show_str(w));
            }
        }
        if let (Some(how), false) = (d.get("defined"), ok) {
            let from: Vec<String> = list(how, "from").iter().map(show_str).collect();
            let gives = if s(d, "gives").is_empty() { String::new() } else { format!("; that gives {}", cut(s(d, "gives"), 100)) };
            println!("       defined from {} as {}{}", from.join(", "), cut(s(how, "as"), 100), gives);
        }
        if !ok {
            for i in list(d, "instructions").iter().filter(|i| i.get("set aside").is_none()) {
                println!("       laid down by {}: {}", s(i, "by"), cut(s(i, "is"), 100));
            }
            for p in &places {
                let part = if p.get("some").is_some() { "lists (in part) " } else { "reads as " };
                if p.get("whole undecided").is_some() {
                    println!("       {} {}{}   (not judged: the places that state the whole of it do not agree)", s(p, "at"), part, cut(s(p, "reads as"), 100));
                    continue;
                }
                let stands = p["stands"].as_bool().unwrap_or(false);
                let earlier = stands && s(p, "why").contains("read the same blind") && s(p, "read the same blind on") == "an earlier text";
                let why = if !stands { "does not stand".to_string() } else if earlier {
                    format!("{}: on an earlier text of the place; the way of reading was confirmed, not this value", s(p, "why"))
                } else { s(p, "why").to_string() };
                println!("       {} {}{}   ({})", s(p, "at"), part, cut(s(p, "reads as"), 100), why);
                if let Some(a) = p.get("against").and_then(Value::as_array) {
                    println!("          against the instruction of {}", a.iter().map(show_str).collect::<Vec<_>>().join(", "));
                }
                if p.get("differs from the definition").is_some() {
                    println!("          not what the definition gives");
                }
                let out = list(p, "not in the whole");
                if !out.is_empty() {
                    println!("          not among the entries the other places state: {}", cut(&out.iter().map(show_str).collect::<Vec<_>>().join(", "), 200));
                }
                if !stands {
                    let has = p["has"].as_object().cloned().unwrap_or_default();
                    println!("          {}", has.iter().map(|(c, v)| format!("{}: {}", c, if v.as_bool().unwrap_or(false) { "yes" } else { "no" })).collect::<Vec<_>>().join(", "));
                    let un = list(p, "unmeasured readers");
                    if !un.is_empty() {
                        println!("          read blind by {}: not a measured reader here, with the instructions it read this under (python -m pw.calibrate --model ...)", un.iter().map(show_str).collect::<Vec<_>>().join(", "));
                    }
                    for other in list(p, "read blind as") {
                        println!("          a blind reader reads {} off it, not what the pattern computes", cut(&show_str(&other), 100));
                    }
                    declined(&list(p, "declined"));
                }
            }
        }
        if state == "violated" {
            for line in differences(d) {
                println!("       {}", line);
            }
        }
        let unread = list(d, "unread");
        for u in &unread {
            println!("       {}: {}", s(u, "at"), cut(s(u, "why"), 160));
            declined(&list(u, "declined"));
        }
        let any = |key: &str| places.iter().any(|p| p.get(key).map_or(false, |v| !v.is_null() && v.as_array().map_or(true, |a| !a.is_empty())));
        match state {
            "waits" => println!("       nothing to hold its places against yet: {}", cut(&list(d, "waits for").iter().map(show_str).collect::<Vec<_>>().join("; "), 200)),
            "violated" if any("differs from the definition") => println!("       a place does not say what the definition gives (verified by Lean): the place, or one of the facts it is defined from, has to change"),
            "conflict" => println!("       which instruction holds is for the people who gave them: take the other out of pw-facts.json"),
            "violated" if any("against") => println!("       a place does not say what was laid down: change the place, or have the instruction withdrawn"),
            "violated" if any("not in the whole") => println!("       a place lists something the others do not have; which one is right is for a person to say"),
            "violated" => println!("       the places do not say the same thing; which one is right is for a person to say"),
            "stale" if unread.iter().any(|u| u.get("broken").is_some()) => println!("       a declared place cannot be read as declared any more: python -m pw.discover (it looks for where the statement went)"),
            "stale" => println!("       read the place(s) again: python -m pw.maintain"),
            "disputed" => println!("       a person has to say which reading is right: python -m pw.confirm --who NAME M:... and --reject M:..."),
            "contested" => println!("       the record holds proofs both that the values agree and that they differ; one is not Lean's: python -m pw.check --verify"),
            "uncovered" => println!("       Lean could settle neither that the values are the same nor that they differ"),
            _ if !ok => {
                println!("       the places agree, but a reading does not stand by the rules (pw-rules.json):");
                println!("       python -m pw.maintain (a blind reading) or python -m pw.confirm (a person)");
            }
            _ => {}
        }
    }
    if decisions.is_empty() {
        println!("no facts declared");
    }
    bad
}

fn run(args: &[String]) -> R<i32> {
    let mut repo = ".".to_string();
    let (mut verify, mut warn, mut as_json, mut needs, mut always, mut keep) = (false, false, false, false, false, false);
    let mut lean_dir = lean::lean_dir();
    let (mut db, mut facts_at, mut actor): (Option<String>, Option<String>, String) = (None, None, "check".into());
    let usage = "pw check [--repo DIR] [--facts PATH] [--db PATH] [--lean-dir DIR] [--verify] [--unconfirmed fail|warn] [--lean needed|always] [--json] [--needs-lean] [--record [--actor NAME]]";
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--repo" => repo = value("a directory")?,
            "--lean-dir" => lean_dir = value("a directory")?.into(),
            "--verify" => verify = true,
            "--record" => keep = true,
            "--db" => db = Some(value("a path")?),
            "--facts" => facts_at = Some(value("a path")?),
            "--actor" => actor = value("a name")?,
            "--json" => as_json = true,
            "--needs-lean" => needs = true,
            "--unconfirmed" => warn = match value("fail or warn")?.as_str() { "warn" => true, "fail" => false, x => return Err(format!("--unconfirmed is fail or warn, not {}", x)) },
            "--lean" => always = match value("needed or always")?.as_str() { "always" => true, "needed" => false, x => return Err(format!("--lean is needed or always, not {}", x)) },
            other => return Err(format!("unknown argument {}; {}", other, usage)),
        }
        i += 1;
    }
    let cwd = Path::new(&repo);
    let facts_path = facts_at.map(PathBuf::from).unwrap_or_else(|| cwd.join("pw-facts.json"));
    let file = facts_path.file_name().and_then(|n| n.to_str()).unwrap_or("pw-facts.json").to_string();
    let facts = kernel::declared(&facts_path)?;
    if needs {
        println!("{}", if kernel::needs_lean(&facts, always) { "yes" } else { "no" });
        return Ok(0);
    }
    let judge = kernel::Judge { always, gate: lean::Gate::new(lean_dir) };
    // (named as the Python check names it: the directory made absolute)
    let record = db.map(PathBuf::from).unwrap_or_else(|| std::fs::canonicalize(cwd).unwrap_or_else(|_| cwd.to_path_buf()).join("pw-log.jsonl"));
    let with_lean = kernel::needs_lean(&facts, always);
    // Checking only looks: what it works out is kept in memory, unless --record asks for it to be appended.
    let work = |st: &mut kernel::State| -> R<(Value, Vec<Value>, std::collections::HashSet<(String, String, String)>, std::collections::HashMap<String, String>)> {
        let recorded = st.proofs.clone();       // what the project's record claims Lean proved, before this check adds anything
        let ways = st.ways.clone();
        kernel::premises(&facts, &judge, &file)?;
        kernel::sync(st, &facts, &file);
        if with_lean {
            judge.gate.usable()?;
        }
        let report = kernel::recheck(st, &judge, &facts, cwd)?;
        Ok((report, recorded, ways, st.props()))
    };
    let (report, recorded, ways, props) = if keep {
        kernel::with_record(&record, &actor, work)?
    } else {
        let mut st = kernel::replay(&record)?;
        st.actor = "check".into();
        work(&mut st)?
    };
    if as_json {
        let quiet = report["decisions"].as_array().unwrap().iter().any(|d| {
            let agree = ["current", "re-established"].contains(&s(d, "state"));
            let loose = list(d, "places").iter().any(|p| !p["stands"].as_bool().unwrap_or(false));
            !(agree && !loose) && !(agree && warn)
        });
        // printed as the Python check prints it (indent 1), so that the two can be compared as text
        let mut out = Vec::new();
        let mut ser = serde_json::Serializer::with_formatter(&mut out, serde_json::ser::PrettyFormatter::with_indent(b" "));
        serde::Serialize::serialize(&report, &mut ser).map_err(|e| e.to_string())?;
        println!("{}", String::from_utf8_lossy(&out));
        return Ok(if quiet { 1 } else { 0 });
    }
    let mut bad = show(&report, warn);
    let mut fresh: Vec<String> = vec![];
    for (d, f) in report["decisions"].as_array().unwrap().iter().filter_map(|d| facts.iter().find(|f| f.h == s(d, "h")).map(|f| (d, f))) {
        for p in list(d, "places") {
            let decl = f.places.iter().find(|x| x.at == s(&p, "at"));
            if let Some(Some(how)) = decl.map(|x| &x.reader) {
                if p["stands"].as_bool().unwrap_or(false) && !ways.contains(&(f.h.clone(), s(&p, "at").to_string(), util::pyjson(how, true))) {
                    fresh.push(s(&p, "at").to_string());
                }
            }
        }
    }
    fresh.sort();
    fresh.dedup();
    if !fresh.is_empty() && !keep {
        println!("note: the way {} {} read is not in the record yet. It stands for the text as it is; to have it stand when the text changes, run `python -m pw.maintain` (or `python -m pw.check --record`) now and commit pw-log.jsonl. No reader is called for that.",
                 cut(&fresh.join(", "), 300), if fresh.len() == 1 { "is" } else { "are" });
    }
    if verify && !with_lean && !judge.gate.available() {
        // Nothing here is judged by a proof: the values are written out and compared as they stand.
        println!("{} recorded proof(s) not run again: Lean is not here, and nothing declared needs it", recorded.len());
    } else if verify {
        let jobs: Vec<(String, Vec<(String, String)>, String)> = recorded.iter().map(|p| {
            let f = p["args"][0].as_str().unwrap_or("");
            (s(p, "relation").to_string(), vec![("Prop".to_string(), props.get(f).cloned().unwrap_or_default())], s(p, "proof").to_string())
        }).collect();
        let verdicts = judge.gate.check_many(&jobs, 50);
        let mut refused = 0;
        for (p, v) in recorded.iter().zip(&verdicts).filter(|(_, v)| !v.ok) {
            let args: Vec<String> = list(p, "args").iter().map(|a| format!("'{}'", show_str(a))).collect();
            let reason: String = v.reason.chars().rev().take(300).collect::<Vec<_>>().into_iter().rev().collect();
            println!("FAIL the record contains a proof Lean does not accept: {} [{}]\n       {}", s(p, "relation"), args.join(", "), cut(&reason, 200));
            refused += 1;
        }
        println!("{} recorded proof(s) verified again, {} refused", recorded.len() - refused, refused);
        bad |= refused > 0;
    }
    Ok(if bad { 1 } else { 0 })
}

/// Let a person confirm what an agent said a place says (pw/confirm.py).
fn confirm(args: &[String]) -> R<i32> {
    let (mut repo, mut who, mut reject, mut lean_dir, mut readings) = (".".to_string(), None, false, lean::lean_dir(), vec![]);
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--repo" => repo = value("a directory")?,
            "--lean-dir" => lean_dir = value("a directory")?.into(),
            "--who" => who = Some(value("a name")?),
            "--reject" => reject = true,
            x if x.starts_with("--") => return Err(format!("unknown argument {}; pw confirm [--repo DIR] [--who NAME [--reject] M:...]", x)),
            m => readings.push(m.to_string()),
        }
        i += 1;
    }
    let cwd = Path::new(&repo);
    let record = std::fs::canonicalize(cwd).unwrap_or_else(|_| cwd.to_path_buf()).join("pw-log.jsonl");
    if !readings.is_empty() {
        let who = who.ok_or("say who is confirming: --who NAME")?;
        for m in &readings {
            kernel::with_record(&record, &who, |st| kernel::sign_off(st, m, &who, !reject).map(|_| ()))?;
            println!("{}{}", if reject { "rejected " } else { "confirmed " }, m);
        }
        return Ok(0);
    }
    // the readings stated by an agent that hold for the files as they are and that no person has confirmed or rejected
    let facts = kernel::declared(&cwd.join("pw-facts.json"))?;
    let judge = kernel::Judge { always: false, gate: lean::Gate::new(lean_dir) };
    let mut st = kernel::replay(&record)?;
    st.actor = "confirm".into();
    kernel::premises(&facts, &judge, "pw-facts.json")?;
    kernel::sync(&mut st, &facts, "pw-facts.json");
    let report = kernel::recheck(&mut st, &judge, &facts, cwd)?;
    let signed = st.signed();
    let mut todo = vec![];
    for d in list(&report, "decisions") {
        for p in list(&d, "places") {
            if s(&p, "by") == "stated" && !signed.contains(s(&p, "m")) {
                todo.push(s(&p, "m").to_string());
                let (quote, anchor) = st.quote(s(&p, "m"));
                let at = s(&p, "at");
                let shown = match quote {
                    Some(q) if anchor => format!("because it says: {}", util::norm(&q)),
                    Some(q) => format!("for example it says: {}\n   (a list is read off the whole place: compare it with {})", util::norm(&q), at),
                    None => {
                        let passage = String::from_utf8_lossy(&read::locate(at, cwd).unwrap_or_default()).trim().to_string();
                        let more = if passage.chars().count() > 600 { "\n             …" } else { "" };
                        format!("passage:  {}{}", cut(&passage, 600).replace('\n', "\n             "), more)
                    }
                };
                println!("{}  {}\n   reads as: {}\n   {}\n", s(&p, "m"), at, s(&p, "reads as"), shown);
            }
        }
    }
    let how = if todo.is_empty() { String::new() } else { format!("; confirm with: python -m pw.confirm --who NAME {}", todo.join(" ")) };
    println!("{} reading(s) nobody has confirmed{}", todo.len(), how);
    Ok(0)
}

/// The commands the agent tools use to act on the record without judging anything themselves:
/// `pw state --db PATH` prints the record as replayed; `pw sync --facts PATH --db PATH` claims
/// and withdraws as declared; `pw adopt --db PATH` takes over readings given as JSON lines on stdin.
fn record_tool(name: &str, args: &[String]) -> R<i32> {
    let (mut db, mut facts_at, mut actor, mut lean_dir) = (None, None, "anon".to_string(), lean::lean_dir());
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--db" => db = Some(PathBuf::from(value("a path")?)),
            "--facts" => facts_at = Some(PathBuf::from(value("a path")?)),
            "--actor" => actor = value("a name")?,
            "--lean-dir" => lean_dir = value("a directory")?.into(),
            other => return Err(format!("unknown argument {}; pw {} --db PATH [--facts PATH] [--actor NAME]", other, name)),
        }
        i += 1;
    }
    let db = db.ok_or(format!("pw {} needs --db PATH", name))?;
    match name {
        "state" => {
            let st = kernel::replay(&db)?;
            println!("{}", serde_json::to_string(&st.dump()).unwrap());
        }
        "sync" => {
            let path = facts_at.ok_or("pw sync needs --facts PATH")?;
            let file = path.file_name().and_then(|n| n.to_str()).unwrap_or("pw-facts.json").to_string();
            let facts = kernel::declared(&path)?;
            let judge = kernel::Judge { always: false, gate: lean::Gate::new(lean_dir) };
            kernel::premises(&facts, &judge, &file)?;
            kernel::with_record(&db, &actor, |st| { kernel::sync(st, &facts, &file); Ok(()) })?;
            println!("{}", serde_json::to_string(&facts.iter().map(|f| f.h.clone()).collect::<Vec<_>>()).unwrap());
        }
        _ => {
            let mut text = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut text).map_err(|e| e.to_string())?;
            let events: Vec<Value> = text.lines().filter(|l| !l.trim().is_empty()).map(serde_json::from_str).collect::<Result<_, _>>().map_err(|e| e.to_string())?;
            kernel::with_record(&db, &actor, |st| st.adopt(&events))?;
        }
    }
    Ok(0)
}

const WORKFLOW: &str = "name: facts

# Hold the facts declared in pw-facts.json against the files, at every push and pull request.
# The checker is {action}, used as an action at a fixed commit: that one commit fixes the
# checker, its crates and Lean. No agent is used; the job only reads the repository.

on:
  push:
  pull_request:

permissions:
  contents: read

jobs:
  facts:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1        # v7.0.1
        with:
          persist-credentials: false
      - uses: {action}@{pin}
";

/// A first step for a repository that does not use this yet: an empty declaration, the line that
/// keeps both sides of the record when branches merge, and a CI job that runs the check. Nothing
/// that is there already is changed.
fn init(args: &[String]) -> R<i32> {
    let (mut repo, mut pin, mut action) = (".".to_string(), None, "sugipamo/parallelworld".to_string());
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--repo" => repo = value("a directory")?,
            "--pin" => pin = Some(value("a commit")?),
            "--action" => action = value("OWNER/REPO")?,
            other => return Err(format!("unknown argument {}; pw init [--repo DIR] [--pin COMMIT] [--action OWNER/REPO]", other)),
        }
        i += 1;
    }
    let cwd = Path::new(&repo);
    if !cwd.is_dir() {
        return Err(format!("{} is not a directory", repo));
    }
    // the commit to pin the action at: given, or the one this tool's own checkout is at
    let pin = match pin {
        Some(p) => p,
        None => {
            let here = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
            let head = std::process::Command::new("git").arg("-C").arg(&here).args(["rev-parse", "HEAD"]).output().ok()
                .filter(|o| o.status.success()).map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
            head.ok_or("say which commit of this tool the CI job is to use: --pin COMMIT (this build is not in a checkout to take it from)")?
        }
    };
    if !regex::Regex::new(r"^[0-9a-f]{40}$").unwrap().is_match(&pin) {
        return Err(format!("--pin is a whole commit id (40 hex digits), not {}: a name such as a branch or tag can be moved", pin));
    }
    let mut said = vec![];
    let mut put = |path: &str, text: &str| -> R<()> {
        let full = cwd.join(path);
        if full.exists() {
            said.push(format!("kept     {} (it is there already)", path));
            return Ok(());
        }
        if let Some(dir) = full.parent() {
            std::fs::create_dir_all(dir).map_err(|e| format!("{}: {}", dir.display(), e))?;
        }
        std::fs::write(&full, text).map_err(|e| format!("{}: {}", full.display(), e))?;
        said.push(format!("wrote    {}", path));
        Ok(())
    };
    put("pw-facts.json", "[]\n")?;
    put(".github/workflows/facts.yml", &WORKFLOW.replace("{action}", &action).replace("{pin}", &pin))?;
    // both branches' readings are kept when they merge: the record is appended to, never rewritten
    let attrs = cwd.join(".gitattributes");
    let now = std::fs::read_to_string(&attrs).unwrap_or_default();
    if now.lines().any(|l| l.split_whitespace().collect::<Vec<_>>() == ["pw-log.jsonl", "merge=union"]) {
        said.push("kept     .gitattributes (pw-log.jsonl merge=union is there already)".into());
    } else {
        let sep = if now.is_empty() || now.ends_with('\n') { "" } else { "\n" };
        std::fs::write(&attrs, format!("{}{}pw-log.jsonl merge=union\n", now, sep)).map_err(|e| format!("{}: {}", attrs.display(), e))?;
        said.push(format!("{} .gitattributes (pw-log.jsonl merge=union)", if now.is_empty() { "wrote   " } else { "added to" }));
    }
    for line in &said {
        println!("{}", line);
    }
    println!("\nThe CI job uses {}@{}.", action, &pin[..12]);
    println!("Next:");
    println!("  1. declare what this repository states in more than one place, in pw-facts.json (docs/spec.md, section 2),");
    println!("     or have an agent propose facts: python -m pw.discover --repo {} --new --apply", repo);
    println!("  2. have the places read: python -m pw.maintain --repo {}   (a blind reader reads what no pattern can)", repo);
    println!("  3. commit pw-facts.json, pw-log.jsonl, .gitattributes and .github/workflows/facts.yml");
    Ok(0)
}

const USAGE: &str = "pw: keep what a repository states in several places saying the same thing (parallelworld)

  pw check   [--repo DIR]                     hold the declared facts (pw-facts.json) against the files
  pw confirm [--repo DIR] [--who NAME [--reject] M:...]
                                              the readings nobody has confirmed; confirm or reject them
  pw init    [--repo DIR] [--pin COMMIT]      a first step for a repository that does not use this yet
  pw version
  pw help [check | confirm | init]

The agents' side (reading places blind, measuring readers, looking for places) is Python:
python -m pw.maintain, pw.calibrate, pw.discover, pw.propagate. They use these, which are not
for typing by hand: mcp, kernel, lean, state, sync, adopt.
";

const CHECK_USAGE: &str = "pw check: hold the declared facts against the files as they are now

  --repo DIR             the repository (default: .); its pw-facts.json and pw-log.jsonl
  --facts PATH           another declaration;  --db PATH  another record
  --verify               run the record's proofs through Lean again instead of believing them
  --unconfirmed warn     a fact whose places agree but rest on a reading no rule lets stand: a warning
  --lean always          put every comparison to Lean (by default only what has to be worked out)
  --json                 what was found, as JSON
  --needs-lean           only say yes or no: does anything declared need Lean?
  --record [--actor NAME]  append what was computed to the record (a check only reads it otherwise)
  --lean-dir DIR         the Lean project (default: the one next to this tool, or PW_LEAN_DIR)

Exit status: 0 every fact holds; 1 something needs attention; 2 the check could not be made.
";

const CONFIRM_USAGE: &str = "pw confirm: let a person confirm what an agent said a place says

  pw confirm [--repo DIR]                         the readings nobody has confirmed, each beside its passage
  pw confirm [--repo DIR] --who NAME M:... M:...  confirm these readings (they hold for the text as it is)
  pw confirm [--repo DIR] --who NAME --reject M:...
";

const INIT_USAGE: &str = "pw init: a first step for a repository

  pw init [--repo DIR] [--pin COMMIT] [--action OWNER/REPO]

Writes what is missing of: an empty pw-facts.json, the .gitattributes line that keeps both sides
of the record when branches merge, and .github/workflows/facts.yml, a CI job that runs this tool
as an action pinned to a commit (by default the commit of this tool's checkout). Changes nothing
that is there.
";

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let help = |a: &[String]| a.iter().any(|x| x == "--help" || x == "-h");
    let usage = |which: Option<&str>| {
        print!("{}", match which { Some("check") => CHECK_USAGE, Some("confirm") => CONFIRM_USAGE, Some("init") => INIT_USAGE, _ => USAGE });
        std::process::exit(0)
    };
    match args.first().map(String::as_str) {
        None => usage(None),
        Some("help" | "--help" | "-h") => usage(args.get(1).map(String::as_str)),
        Some(c @ ("check" | "confirm" | "init")) if help(&args[1..]) => usage(Some(c)),
        Some(x) if x.starts_with("--") && help(&args) => usage(Some("check")),
        _ => {}
    }
    let result = match args.first().map(String::as_str) {
        Some("confirm") => confirm(&args[1..]),
        Some("mcp") => Ok(mcp::serve()),
        Some("init") => init(&args[1..]),
        Some("version") => { println!("parallelworld {}", env!("CARGO_PKG_VERSION")); Ok(0) }
        Some("kernel") => Ok(ops::kernel()),
        Some("lean") => Ok(ops::lean()),
        Some(x @ ("state" | "sync" | "adopt")) => record_tool(x, &args[1..]),
        Some("check") => run(&args[1..]),
        _ => run(&args[..]),
    };
    match result {
        Ok(code) => std::process::exit(code),
        Err(e) => {
            eprintln!("pw: {}", e.replace(kernel::GATE, ""));
            std::process::exit(2);
        }
    }
}
