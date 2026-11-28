#!/bin/sh
# Get the Rust build of this tool (pw), and print the path of the executable.
#
#     PW_BIN="$(ci/pw.sh)"                 # into the cache directory
#     ci/pw.sh DIR                         # into DIR instead
#     PW_BUILD=source ci/pw.sh             # always build from source
#     ci/pw.sh --source-digest             # only print the digest of the source here
#
# rust/release.txt names a published executable: its version, the digest of the source it was
# built from, where it is, and its SHA-256. It is taken only if that source is exactly the source
# here (the same rust/ and the files it compiles in) and the machine is Linux x86_64; the download
# is held against the checksum before it is used. Otherwise, or if anything about it fails, the
# executable is built from this source (cargo, crates pinned by rust/Cargo.lock).
set -eu

here=$(cd "$(dirname "$0")/.." && pwd)

# The source an executable is made from: every file compiled into it, by path and content.
source_digest() {
    (cd "$here" && { find rust/src -name '*.rs'; printf '%s\n' rust/Cargo.toml rust/Cargo.lock rust/build.rs pw/reader.txt pw/rules.json \
        rust/calibration/passages.json lean/lean-toolchain lean/Gamma.lean lean/lakefile.toml lean/lake-manifest.json; } \
        | LC_ALL=C sort | while read -r f; do printf '%s\000' "$f"; cat "$f"; printf '\000'; done) | sha256sum | cut -c1-64
}

if [ "${1:-}" = --source-digest ]; then
    source_digest
    exit 0
fi
dest=${1:-${XDG_CACHE_HOME:-$HOME/.cache}/parallelworld/bin}
mkdir -p "$dest"

field() { sed -n "s/^$1=//p" "$here/rust/release.txt" 2>/dev/null | head -n 1; }

fetched() {
    [ "${PW_BUILD:-}" != source ] && [ -f "$here/rust/release.txt" ] || return 1
    [ "$(uname -s)-$(uname -m)" = Linux-x86_64 ] || return 1
    for tool in curl sha256sum; do command -v "$tool" >/dev/null 2>&1 || return 1; done
    [ "$(field source)" = "$(source_digest)" ] || { echo "pw.sh: rust/release.txt is of other source; building" >&2; return 1; }
    bin="$dest/pw-$(field version)-$(field sha256 | cut -c1-12)"
    if [ ! -x "$bin" ]; then
        part="$bin.part"
        curl -fsSL -o "$part" "$(field url)" || { rm -f "$part"; return 1; }
        echo "$(field sha256)  $part" | sha256sum -c --quiet >&2 || {
            rm -f "$part"; echo "pw.sh: the download is not the executable rust/release.txt names; building" >&2; return 1; }
        chmod +x "$part" && mv "$part" "$bin"
    fi
    echo "$bin"
}

built() {
    command -v cargo >/dev/null 2>&1 || { echo "pw.sh: cargo is needed to build the Rust part of this tool" >&2; exit 1; }
    cargo build --release --locked --quiet --manifest-path "$here/rust/Cargo.toml" --target-dir "$dest/target" >&2
    echo "$dest/target/release/pw"
}

fetched || built
