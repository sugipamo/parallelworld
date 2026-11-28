//! The way in (pw start): each step that is not done yet, in order, saying before a step that
//! calls an agent what it may cost. Every step looks at the repository to see whether it is done,
//! so running it again goes on from where it stopped.
//!
//!   1. pw init                         no pw-facts.json yet
//!   2. pw discover --new --apply       nothing declared: an agent proposes facts (each checked)
//!   3. pw calibrate                    the reader is not measured here, under its instructions
//!   4. pw maintain                     places nobody has read, as they are now
//!   5. pw check
use crate::agent;
use crate::kernel;
use crate::util::*;
use serde_json::Value;
use std::io::{BufRead, IsTerminal, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

/// The files the steps write, which belong in the repository.
const KEPT: [&str; 5] = ["pw-facts.json", "pw-log.jsonl", "pw-calibration.json", ".gitattributes", ".github/workflows/facts.yml"];

struct Step<'a> {
    what: &'a str,
    args: Vec<String>,
    cost: String,
}

/// Run this executable with `args`, in the open: what it prints is what the user sees. Its exit status.
fn run(args: &[String]) -> R<i32> {
    let status = Command::new(agent::me()).args(args).status().map_err(|e| format!("{}: {}", agent::me(), e))?;
    Ok(status.code().unwrap_or(2))
}

/// Whether to take a step that calls an agent: --yes; else asked, where someone can answer.
fn agreed(step: &Step, yes: bool) -> bool {
    println!("\nNext: {}\n  pw {}\n  {}", step.what, step.args.join(" "), step.cost);
    if yes {
        return true;
    }
    if !std::io::stdin().is_terminal() {
        println!("Stopped before it (nothing was spent). To take it: pw start --yes, or the command above.");
        return false;
    }
    print!("Take this step? [y/N] ");
    let _ = std::io::stdout().flush();
    let mut line = String::new();
    let _ = std::io::stdin().lock().read_line(&mut line);
    if matches!(line.trim(), "y" | "Y" | "yes") {
        return true;
    }
    println!("Stopped (nothing was spent). pw start goes on from here.");
    false
}

fn declared(repo: &Path) -> R<Vec<Value>> {
    let text = std::fs::read_to_string(repo.join("pw-facts.json")).map_err(|e| format!("pw-facts.json: {}", e))?;
    serde_json::from_str(&text).map_err(|e| format!("pw-facts.json is not JSON: {}", e))
}

pub fn command(args: &[String]) -> R<i32> {
    let usage = "pw start [--repo DIR] [--yes] [--model M] [--budget DOLLARS]";
    let (mut repo, mut yes, mut model, mut budget) = (PathBuf::from("."), false, agent::MODEL.to_string(), None::<String>);
    let mut i = 0;
    while i < args.len() {
        let flag = args[i].clone();
        let mut value = |what: &str| { i += 1; args.get(i).cloned().ok_or(format!("{} needs {}", flag, what)) };
        match flag.as_str() {
            "--repo" => repo = PathBuf::from(value("a directory")?),
            "--yes" | "-y" => yes = true,
            "--model" => model = value("a model")?,
            "--budget" => {
                let b = value("an amount in dollars")?;
                b.parse::<f64>().map_err(|_| "--budget is an amount in dollars".to_string())?;
                budget = Some(b);
            }
            other => return Err(format!("unknown argument {}; {}", other, usage)),
        }
        i += 1;
    }
    let repo = std::fs::canonicalize(&repo).map_err(|e| format!("{}: {}", repo.display(), e))?;
    // what the steps may write, as it was before: at the end, what changed is what there is to commit
    let before: Vec<Option<Vec<u8>>> = KEPT.iter().map(|f| std::fs::read(repo.join(f)).ok()).collect();
    let r = repo.display().to_string();
    let with = |cmd: &str, extra: &[&str], default_budget: f64| -> (Vec<String>, f64) {
        let mut a: Vec<String> = [cmd, "--repo", &r, "--model", &model].iter().map(|x| x.to_string()).collect();
        a.extend(extra.iter().map(|x| x.to_string()));
        let b = budget.clone().unwrap_or(default_budget.to_string());
        if budget.is_some() {
            a.extend(["--budget".to_string(), b.clone()]);
        }
        (a, b.parse().unwrap_or(default_budget))
    };

    // 1. set up
    if !repo.join("pw-facts.json").exists() {
        println!("1. Setting up (no cost): pw init");
        if run(&["init".into(), "--repo".into(), r.clone()])? != 0 {
            return Ok(2);
        }
    } else {
        println!("1. Set up already: pw-facts.json is there");
    }

    // 2. facts
    if declared(&repo)?.is_empty() {
        agent::ready()?;
        let (a, b) = with("discover", &["--new", "--apply"], 5.0);
        let step = Step { what: "nothing is declared yet: have an agent propose facts, each place it names checked against the file",
                          args: a, cost: format!("Agent sessions: a few, each spending at most ${} (--budget); each says what it spent.", cents(b)) };
        if !agreed(&step, yes) {
            return Ok(1);
        }
        run(&step.args)?;
        if declared(&repo)?.is_empty() {
            println!("\nNo fact was taken. Declare what this repository states in more than one place in pw-facts.json (docs/spec.md, section 2), then run pw start again.");
            return Ok(1);
        }
    } else {
        println!("2. Facts declared already: {} in pw-facts.json", declared(&repo)?.len());
    }

    // 3. the reader measured here
    if !kernel::counts_here(&repo, &model) {
        agent::ready()?;
        let (a, b) = with("calibrate", &[], 2.0);
        let step = Step { what: &format!("{} is not measured here as a reader: measure it on planted changes with known answers", model),
                          args: a, cost: format!("Agent sessions: about 10 to 20, in parallel, each spending at most ${} (--budget). A typical run spends a few dollars; it says what it spent.", cents(b)) };
        if !agreed(&step, yes) {
            return Ok(1);
        }
        run(&step.args)?;
        if !kernel::counts_here(&repo, &model) {
            println!("\n{} did not meet the bar of pw-rules.json here, so its readings would not count: see what pw calibrate printed above. Nothing further is taken.", model);
            return Ok(1);
        }
    } else {
        println!("3. Reader measured already: {} (pw-calibration.json)", model);
    }

    // 4. read what is not read, as it is now (maintain says itself when there is nothing to read)
    let (a, b) = with("maintain", &[], 3.0);
    let unread = Command::new(agent::me()).args(["check", "--repo", &r, "--json"]).output().ok()
        .and_then(|o| serde_json::from_slice::<Value>(&o.stdout).ok())
        .map_or(true, |rep| rep["decisions"].as_array().map_or(false, |ds| ds.iter().any(|d| {
            d["unread"].as_array().map_or(false, |u| !u.is_empty())
                || d["places"].as_array().map_or(false, |ps| ps.iter().any(|p| !p["stands"].as_bool().unwrap_or(true)))
        })));
    if unread {
        agent::ready()?;
        let step = Step { what: "have a blind reader read the places no reading of stands yet", args: a,
                          cost: format!("Agent sessions: about one per place of a fact, each spending at most ${} (--budget); it says what it spent.", cents(b)) };
        if !agreed(&step, yes) {
            return Ok(1);
        }
        run(&step.args)?;
    } else {
        println!("4. Every place is read as it is now");
    }

    // 5. where it stands
    println!("\n5. The check, as CI runs it: pw check");
    let code = run(&["check".into(), "--repo".into(), r.clone()])?;
    if code == 0 {
        let changed: Vec<&str> = KEPT.iter().zip(&before).filter(|(f, b)| std::fs::read(repo.join(f)).ok() != **b).map(|(f, _)| *f).collect();
        if changed.is_empty() {
            println!("\nDone. Nothing changed: there is nothing to commit.");
        } else {
            println!("\nDone. Commit what changed: {}.", changed.join(", "));
        }
    } else if code == 1 {
        println!("\nWhat the check says above needs a person (or another step it names). pw start goes on from there when run again.");
    }
    Ok(code)
}

fn cents(x: f64) -> String {
    if x.fract() == 0.0 { format!("{}", x as i64) } else { format!("{:.2}", x) }
}
