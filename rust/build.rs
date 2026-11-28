//! The commit this executable is built from, for `pw version` and for `pw init` to pin the CI job
//! at, where the executable is not in a checkout to ask (one published, or installed on its own).
fn main() {
    let here = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_default();
    let commit = std::process::Command::new("git").args(["rev-parse", "HEAD"]).current_dir(&here).output().ok()
        .filter(|o| o.status.success()).map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default();
    println!("cargo:rustc-env=PW_COMMIT={}", commit);
    let git = std::path::Path::new(&here).join("..").join(".git");
    for p in ["HEAD", "refs/heads", "packed-refs"] {
        if git.join(p).exists() {
            println!("cargo:rerun-if-changed={}", git.join(p).display());
        }
    }
    println!("cargo:rerun-if-changed=build.rs");
}
