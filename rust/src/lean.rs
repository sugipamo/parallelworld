//! The Lean gate: the only way it is settled that a proposition holds, or does not.
//!
//! The same gate as pw/lean_gate.py, run the same way: the statement is written by the gate from
//! the registered text, the caller supplies only tactics, and a proof is accepted iff the module
//! compiles and a second file, free of caller text, prints exactly one axiom report listing only
//! allowed axioms. Lean runs in a copy of the project under the user's cache (PW_LEAN_WORK), the
//! same directory the Python gate uses, so that Gamma is built once for both.
use regex::Regex;
use sha2::{Digest, Sha256};
use std::cell::RefCell;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

pub const ALLOWED_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"]; // (sorted)
const PROJECT: [&str; 3] = ["lean-toolchain", "Gamma.lean", "lakefile.toml"];
const COPIED: [&str; 4] = ["lean-toolchain", "Gamma.lean", "lakefile.toml", "lake-manifest.json"];

/// The Lean project (lean/) as it was when this was built: used where no project is found on
/// disk (an executable published or installed on its own), so that it can still run proofs.
const BUILT_IN: [(&str, &str); 4] = [
    ("lean-toolchain", include_str!("../../lean/lean-toolchain")),
    ("Gamma.lean", include_str!("../../lean/Gamma.lean")),
    ("lakefile.toml", include_str!("../../lean/lakefile.toml")),
    ("lake-manifest.json", include_str!("../../lean/lake-manifest.json")),
];

pub struct Verdict {
    pub ok: bool,
    pub reason: String,
    pub axioms: Vec<String>,
    pub gamma: String,
}

impl Verdict {
    fn no(reason: impl Into<String>) -> Verdict {
        Verdict { ok: false, reason: reason.into(), axioms: vec![], gamma: String::new() }
    }
}

struct Ready {
    lake: PathBuf,
    home: PathBuf,
    lean_path: String,
}

pub struct Gate {
    dir: PathBuf,
    timeout: Duration,
    ready: RefCell<Option<Ready>>,
    runs: RefCell<u64>,
}

fn hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{:02x}", b)).collect()
}

fn tail(s: &str, n: usize) -> String {
    let count = s.chars().count();
    s.chars().skip(count.saturating_sub(n)).collect()
}

fn forbidden() -> &'static Regex {
    static RE: OnceLock<Regex> = OnceLock::new();
    RE.get_or_init(|| Regex::new(concat!(
        r"#|@\[|declare_|register_|builtin_|\b(sorry|admit|axiom|macro|macro_rules|syntax|notation|infix[lr]?|prefix|postfix|elab|",
        r"elab_rules|import|open|export|set_option|attribute|instance|unsafe|implemented_by|extern|",
        r"native_decide|initialize|local|scoped|private|protected|run_cmd|run_tac|namespace|section|end|theorem|lemma|def|abbrev|",
        r"example|structure|inductive|class|universe|variable|deriving|opaque|mutual)\b")).unwrap())
}

/// The Lean project next to this tool: PW_LEAN_DIR, else a `lean` directory beside the binary's
/// checkout (rust/target/release/pw is three levels down), else the one this was built from;
/// else none (the empty path), and the project built into this executable is used.
pub fn lean_dir() -> PathBuf {
    if let Ok(d) = std::env::var("PW_LEAN_DIR") {
        return PathBuf::from(d);
    }
    let mut candidates = vec![];
    if let Ok(exe) = std::env::current_exe().and_then(std::fs::canonicalize) {
        candidates.extend(exe.ancestors().skip(1).map(|a| a.join("lean")));
    }
    candidates.push(Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("lean"));
    candidates.iter().find(|d| d.join("lean-toolchain").exists()).cloned().unwrap_or_default()
}

/// Run a command to its end, or kill it after `timeout`. None if it did not finish in time.
fn run(cmd: &mut Command, timeout: Duration) -> Option<(i32, String, String)> {
    let mut child = cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().ok()?;
    let mut out = child.stdout.take().unwrap();
    let mut err = child.stderr.take().unwrap();
    let a = std::thread::spawn(move || { let mut s = Vec::new(); let _ = out.read_to_end(&mut s); s });
    let b = std::thread::spawn(move || { let mut s = Vec::new(); let _ = err.read_to_end(&mut s); s });
    let start = Instant::now();
    let code = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status.code().unwrap_or(-1),
            Ok(None) if start.elapsed() < timeout => std::thread::sleep(Duration::from_millis(5)),
            _ => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
        }
    };
    let text = |v: Vec<u8>| String::from_utf8_lossy(&v).into_owned();
    Some((code, text(a.join().unwrap_or_default()), text(b.join().unwrap_or_default())))
}

fn which(name: &str) -> Option<PathBuf> {
    std::env::var_os("PATH").and_then(|p| std::env::split_paths(&p).map(|d| d.join(name)).find(|f| f.is_file()))
}

impl Gate {
    pub fn new(dir: PathBuf) -> Gate {
        Gate { dir, timeout: Duration::from_secs(300), ready: RefCell::new(None), runs: RefCell::new(0) }
    }

    /// One file of the project: from its directory, or the one built in (the empty path).
    fn file(&self, name: &str) -> Option<Vec<u8>> {
        if self.dir.as_os_str().is_empty() {
            return BUILT_IN.iter().find(|(n, _)| *n == name).map(|(_, c)| c.as_bytes().to_vec());
        }
        std::fs::read(self.dir.join(name)).ok()
    }

    fn where_(&self, name: &str) -> String {
        if self.dir.as_os_str().is_empty() { format!("{}, built into this executable", name) } else { self.dir.join(name).display().to_string() }
    }

    /// The directory Lean is run in: a copy of the project, named after its content.
    fn home(&self) -> Result<PathBuf, String> {
        let mut h = Sha256::new();
        let mut files = vec![];
        for name in COPIED {
            match self.file(name).ok_or(()) {
                Ok(content) => {
                    h.update(name.as_bytes());
                    h.update(b"\0");
                    h.update(&content);
                    h.update(b"\0");
                    files.push((name, content));
                }
                Err(_) if PROJECT.contains(&name) => return Err(format!("{} is not the Lean project: it has no {}", self.dir.display(), name)),
                Err(_) => {}
            }
        }
        let digest: String = h.finalize().iter().map(|b| format!("{:02x}", b)).collect();
        let base = match std::env::var("PW_LEAN_WORK").ok().filter(|x| !x.is_empty()) {
            Some(b) => PathBuf::from(b),
            None => std::env::var("XDG_CACHE_HOME").ok().filter(|x| !x.is_empty()).map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(std::env::var("HOME").unwrap_or_default()).join(".cache")).join("parallelworld"),
        };
        let home = base.join(format!("lean-{}", &digest[..16]));
        let fail = |e: std::io::Error| format!("Lean needs a directory it can write to, and {} is not one ({}); set PW_LEAN_WORK", home.display(), e);
        std::fs::create_dir_all(&home).map_err(fail)?;
        for (name, content) in files {
            let path = home.join(name);
            if !path.exists() {
                let tmp = home.join(format!(".{}.{}", name, std::process::id()));     // (another process may be doing the same)
                std::fs::write(&tmp, content).map_err(fail)?;
                std::fs::rename(&tmp, &path).map_err(fail)?;
            }
        }
        Ok(home)
    }

    /// Refuse text that could start a new command or alter the environment (a denylist; see docs/spec.md §6).
    pub fn screen(&self, text: &str) -> Result<(), String> {
        if text.contains("'\"'") {
            return Err("a double quote as a character literal is not accepted".into());
        }
        static STR: OnceLock<Regex> = OnceLock::new();
        let plain = if text.contains('\\') { text.to_string() } else { STR.get_or_init(|| Regex::new(r#""[^"\n]*""#).unwrap()).replace_all(text, "\"\"").into_owned() };
        match forbidden().find(&plain) {
            Some(m) => Err(format!("forbidden token '{}' in Lean text", m.as_str())),
            None => Ok(()),
        }
    }

    pub fn gamma(&self) -> String {
        let mut h = Sha256::new();
        for name in PROJECT {
            h.update(self.file(name).unwrap_or_default());
        }
        h.update(ALLOWED_AXIOMS.join(",").as_bytes());
        h.finalize().iter().map(|b| format!("{:02x}", b)).collect::<String>()[..12].to_string()
    }

    /// items: (Lean type, Lean term), referred to by the goal as S0, S1.
    pub fn render(&self, relation: &str, items: &[(&str, &str)], proof: &str) -> Result<String, String> {
        for (t, b) in items {
            self.screen(t)?;
            self.screen(b)?;
        }
        self.screen(proof)?;
        let defs: Vec<String> = items.iter().enumerate().map(|(i, (t, b))| format!("def S{} : ({}) := ({})", i, t, b)).collect();
        let names: Vec<String> = (0..items.len()).map(|i| format!("PWStmt.S{}", i)).collect();
        let goal = match relation { "holds" => "PWStmt.S0", "not" => "_root_.Not PWStmt.S0", other => return Err(format!("no goal {}", other)) };
        let body: Vec<String> = proof.trim().lines().map(|l| format!("    {}", l)).collect();
        Ok(format!(
            "import Gamma\n\nnamespace PWStmt\n{}\nend PWStmt\n\ntheorem pw_goal : {} := by\n  unfold {}\n  try dsimp only\n  first\n  | done\n  | (\n{}\n    )\n",
            defs.join("\n"), goal, names.join(" "), body.join("\n")))
    }

    /// Locate lake, insist it is the Lean version Gamma pins, and build Gamma (once per process).
    fn lake(&self) -> Result<(PathBuf, PathBuf, String), String> {
        if let Some(r) = self.ready.borrow().as_ref() {
            return Ok((r.lake.clone(), r.home.clone(), r.lean_path.clone()));
        }
        let lake = std::env::var("PW_LAKE").ok().filter(|x| !x.is_empty()).map(PathBuf::from)
            .or_else(|| which("lake"))
            .unwrap_or_else(|| PathBuf::from(std::env::var("HOME").unwrap_or_default()).join(".elan/bin/lake"));
        if !lake.exists() {
            return Err("Lean (lake) is not installed; no proof can be accepted".into());
        }
        let home = self.home()?;
        let pinned = std::fs::read_to_string(home.join("lean-toolchain")).unwrap_or_default();
        let want = pinned.trim().rsplit(":v").next().unwrap_or("").to_string();
        let (_, out, err) = run(Command::new(&lake).arg("--version").current_dir(&home), self.timeout).unwrap_or_default();
        if !out.contains(&format!("Lean version {})", want)) {
            let said = if out.trim().is_empty() { err.trim().chars().take(200).collect() } else { out.trim().to_string() };
            return Err(format!("Gamma pins Lean {} ({}) but lake reports: {}. Install Lean {}, or point PW_LAKE at its lake",
                               want, self.where_("lean-toolchain"), said, want));
        }
        match run(Command::new(&lake).arg("build").current_dir(&home), self.timeout) {
            None => return Err("Gamma did not build in time".into()),
            Some((code, out, err)) if code != 0 => return Err(format!("Gamma failed to build: {}", tail(&(out + &err), 500))),
            _ => {}
        }
        let (_, path, _) = run(Command::new(&lake).args(["env", "printenv", "LEAN_PATH"]).current_dir(&home), self.timeout).unwrap_or_default();
        *self.ready.borrow_mut() = Some(Ready { lake: lake.clone(), home: home.clone(), lean_path: path.trim().to_string() });
        Ok((lake, home, path.trim().to_string()))
    }

    pub fn available(&self) -> bool {
        self.lake().is_ok()
    }

    /// Why Lean cannot be run here, if it cannot.
    pub fn usable(&self) -> Result<(), String> {
        self.lake().map(|_| ()).map_err(|e| format!("{}. Whether places agree is settled by Lean: nothing can be checked without it \
            (ci/lean.sh in this tool's repository fetches the right version)", e))
    }

    /// A directory of its own under the project's copy, for one run (Lean wants its input under the project).
    fn work(&self, home: &Path) -> Result<PathBuf, String> {
        let n = { let mut r = self.runs.borrow_mut(); *r += 1; *r };
        let dir = home.join(format!("run-{}-{}", std::process::id(), n));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {}", dir.display(), e))?;
        Ok(dir)
    }

    fn lean(&self, lake: &Path, home: &Path, lean_path: &str, work: &Path, args: &[&Path]) -> Option<(i32, String, String)> {
        let lean = lake.parent().map(|d| d.join("lean")).unwrap_or_else(|| PathBuf::from("lean"));
        run(Command::new(lean).args(args).current_dir(home).env("LEAN_PATH", format!("{}:{}", lean_path, work.display())), self.timeout)
    }

    pub fn check(&self, relation: &str, items: &[(&str, &str)], proof: &str) -> Verdict {
        let src = match self.render(relation, items, proof) { Ok(s) => s, Err(e) => return Verdict::no(e) };
        let (lake, home, lean_path) = match self.lake() { Ok(x) => x, Err(e) => return Verdict::no(e) };
        let work = match self.work(&home) { Ok(w) => w, Err(e) => return Verdict::no(e) };
        let module = format!("PWProof_{}", &hex(src.as_bytes())[..16]);
        let (file, audit, olean) = (work.join(format!("{}.lean", module)), work.join(format!("{}_audit.lean", module)), work.join(format!("{}.olean", module)));
        let verdict = (|| {
            std::fs::write(&file, &src).map_err(|e| e.to_string())?;
            std::fs::write(&audit, format!("import {}\n#print axioms pw_goal\n", module)).map_err(|e| e.to_string())?;
            let (code, out, err) = self.lean(&lake, &home, &lean_path, &work, &[Path::new("-o"), &olean, &file]).ok_or("timeout")?;
            if code != 0 {
                return Err(tail(&(out + &err), 1500));
            }
            let (code, out, err) = self.lean(&lake, &home, &lean_path, &work, &[&audit]).ok_or("timeout")?;
            Ok(Gate::judge(code, &(out + &err), &self.gamma()))
        })();
        let _ = std::fs::remove_dir_all(&work);
        verdict.unwrap_or_else(Verdict::no)
    }

    /// Check many proofs, (relation, items, proof): compiled together in batches, each accepted
    /// only if the whole batch compiles and audits as expected; otherwise one by one.
    pub fn check_many(&self, jobs: &[(String, Vec<(String, String)>, String)], batch: usize) -> Vec<Verdict> {
        let mut out = vec![];
        for part in jobs.chunks(batch.max(1)) {
            match if part.len() > 1 { self.together(part) } else { None } {
                Some(v) => out.extend(v),
                None => out.extend(part.iter().map(|(r, items, p)| {
                    let items: Vec<(&str, &str)> = items.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
                    self.check(r, &items, p)
                })),
            }
        }
        out
    }

    fn together(&self, jobs: &[(String, Vec<(String, String)>, String)]) -> Option<Vec<Verdict>> {
        let mut parts = vec![];
        for (i, (relation, items, proof)) in jobs.iter().enumerate() {
            let items: Vec<(&str, &str)> = items.iter().map(|(a, b)| (a.as_str(), b.as_str())).collect();
            let src = self.render(relation, &items, proof).ok()?;
            let (head, body) = src.split_once("\n\n")?;
            if head != "import Gamma" {
                return None;
            }
            parts.push(format!("namespace PW{}\n{}\nend PW{}\n", i, body, i));
        }
        let (lake, home, lean_path) = self.lake().ok()?;
        let src = format!("import Gamma\n\n{}", parts.join("\n"));
        let work = self.work(&home).ok()?;
        let module = format!("PWProofs_{}", &hex(src.as_bytes())[..16]);
        let (file, audit, olean) = (work.join(format!("{}.lean", module)), work.join(format!("{}_audit.lean", module)), work.join(format!("{}.olean", module)));
        let result = (|| {
            std::fs::write(&file, &src).ok()?;
            let prints: String = (0..jobs.len()).map(|i| format!("#print axioms PW{}.pw_goal\n", i)).collect();
            std::fs::write(&audit, format!("import {}\n{}", module, prints)).ok()?;
            let (code, _, _) = self.lean(&lake, &home, &lean_path, &work, &[Path::new("-o"), &olean, &file])?;
            if code != 0 {
                return None;
            }
            let (code, out, err) = self.lean(&lake, &home, &lean_path, &work, &[&audit])?;
            if code != 0 {
                return None;
            }
            Some(out + &err)
        })();
        let _ = std::fs::remove_dir_all(&work);
        let output = result?;
        static REPORT: OnceLock<Regex> = OnceLock::new();
        let re = REPORT.get_or_init(|| Regex::new(r"'PW(\d+)\.pw_goal' (does not depend on any axioms|depends on axioms: \[[^\]]*\])").unwrap());
        let reports: Vec<(usize, String)> = re.captures_iter(&output).map(|c| (c[1].parse().unwrap_or(usize::MAX), c[2].to_string())).collect();
        let rebuilt: Vec<String> = reports.iter().map(|(n, rest)| format!("'PW{}.pw_goal' {}", n, rest)).collect();
        let whole: Vec<&str> = output.split_whitespace().collect();
        if reports.iter().map(|(n, _)| *n).ne(0..jobs.len()) || rebuilt.join(" ") != whole.join(" ") {
            return None;
        }
        let gamma = self.gamma();
        Some(reports.iter().map(|(_, rest)| Gate::judge(0, &format!("'pw_goal' {}", rest.split_whitespace().collect::<Vec<_>>().join(" ")), &gamma)).collect())
    }

    /// Run Lean on a file of ours that nothing imports. None if it does not finish in time.
    fn run_file(&self, src: &str, lake: &Path, home: &Path) -> Result<Option<(i32, String, String)>, String> {
        let work = self.work(home)?;
        let path = work.join(format!("PW_{}.lean", &hex(src.as_bytes())[..16]));
        let r = std::fs::write(&path, src).map_err(|e| e.to_string())
            .map(|_| run(Command::new(lake).args(["env", "lean"]).arg(&path).current_dir(home), self.timeout));
        let _ = std::fs::remove_dir_all(&work);
        r
    }

    /// Does Lean accept each (type, term) under Gamma?
    pub fn typecheck(&self, items: &[(&str, &str)]) -> (bool, String) {
        let go = || -> Result<(bool, String), String> {
            for (t, b) in items {
                self.screen(t)?;
                self.screen(b)?;
            }
            let (lake, home, _) = self.lake()?;
            let src = format!("import Gamma\n\n{}", items.iter().map(|(t, b)| format!("example : ({}) := ({})\n", t, b)).collect::<String>());
            Ok(match self.run_file(&src, &lake, &home)? {
                None => (false, "timeout".into()),
                Some((code, out, err)) => (code == 0, tail(&(out + &err), 800)),
            })
        };
        go().unwrap_or_else(|e| (false, e))
    }

    /// The value of a term as Lean prints it, or None if Lean does not evaluate it (for showing only).
    pub fn evaluate(&self, typ: &str, term: &str) -> Option<String> {
        self.screen(typ).ok()?;
        self.screen(term).ok()?;
        let (lake, home, _) = self.lake().ok()?;
        let src = format!("import Gamma\n\ndef pw_value : ({}) := ({})\n\n#eval IO.println (repr pw_value)\n", typ, term);
        match self.run_file(&src, &lake, &home).ok()?? {
            (0, out, _) if !out.trim().is_empty() => Some(out.trim().to_string()),
            _ => None,
        }
    }

    /// Read the audit run: its whole output must be one axiom report, nothing else.
    pub fn judge(code: i32, output: &str, gamma: &str) -> Verdict {
        let out = output.split_whitespace().collect::<Vec<_>>().join(" ");
        if code != 0 {
            return Verdict::no(tail(output, 1500));
        }
        let mut axioms: Vec<String> = if out == "'pw_goal' does not depend on any axioms" {
            vec![]
        } else {
            static ONE: OnceLock<Regex> = OnceLock::new();
            match ONE.get_or_init(|| Regex::new(r"^'pw_goal' depends on axioms: \[([^\]]*)\]$").unwrap()).captures(&out) {
                Some(c) => c[1].split(',').map(str::trim).filter(|a| !a.is_empty()).map(String::from).collect(),
                None => return Verdict::no(format!("unexpected audit output: {}", tail(output, 500))),
            }
        };
        axioms.sort();
        let mut bad: Vec<&String> = axioms.iter().filter(|a| !ALLOWED_AXIOMS.contains(&a.as_str())).collect();
        bad.dedup();
        if !bad.is_empty() {
            return Verdict::no(format!("depends on unapproved axioms: [{}]", bad.iter().map(|a| format!("'{}'", a)).collect::<Vec<_>>().join(", ")));
        }
        Verdict { ok: true, reason: String::new(), axioms, gamma: gamma.to_string() }
    }
}
