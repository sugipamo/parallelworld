#!/bin/sh
# Fetch the Lean that lean/lean-toolchain names, and print the directory its lake and lean are in.
#
#     export PATH="$(ci/lean.sh):$PATH"          # or: PW_LAKE="$(ci/lean.sh)/lake"
#     ci/lean.sh DIR                              # unpack under DIR instead of the cache directory
#
# The archive is taken by version and held against the checksum below before it is unpacked:
# the version is stated in one place (lean/lean-toolchain), and the checksum is of that
# version's archive. When the version changes, the checksum here has to change with it; until
# it does, this refuses the archive.
set -eu

SHA256=320f18e7d58271d95fced740522b5a5ed41b85b2af5bf0e8ab9a8dbc380e450a   # lean-<version>-linux.tar.zst

here=$(cd "$(dirname "$0")/.." && pwd)
version=$(sed -n 's|^leanprover/lean4:v\([0-9][0-9A-Za-z.-]*\)$|\1|p' "$here/lean/lean-toolchain")
[ -n "$version" ] || { echo "lean.sh: no Lean version in $here/lean/lean-toolchain" >&2; exit 1; }

dest=${1:-${XDG_CACHE_HOME:-$HOME/.cache}/parallelworld/toolchain}
bin="$dest/lean-$version-linux/bin"
if [ ! -x "$bin/lake" ]; then
    if [ "$(uname -s)-$(uname -m)" != "Linux-x86_64" ]; then
        echo "lean.sh: only the Linux x86_64 archive is pinned here. Install Lean $version yourself (elan) and put its lake on PATH, or in PW_LAKE" >&2
        exit 1
    fi
    for tool in curl sha256sum tar zstd; do
        command -v "$tool" >/dev/null 2>&1 || { echo "lean.sh: $tool is needed to fetch and unpack Lean (the archive is .tar.zst)" >&2; exit 1; }
    done
    mkdir -p "$dest"
    archive="$dest/lean-$version-linux.tar.zst.part"
    trap 'rm -f "$archive"' EXIT
    curl -fsSL -o "$archive" "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-linux.tar.zst"
    echo "$SHA256  $archive" | sha256sum -c --quiet >&2 || {
        echo "lean.sh: the archive of Lean $version is not the one pinned in $0 (if lean-toolchain changed, the checksum has to change with it)" >&2
        exit 1
    }
    rm -rf "$dest/.unpack" && mkdir "$dest/.unpack"          # so that a half-unpacked Lean is never taken for a whole one
    zstd -dc "$archive" | tar -xf - -C "$dest/.unpack"
    rm -rf "$dest/lean-$version-linux" && mv "$dest/.unpack/lean-$version-linux" "$dest/" && rmdir "$dest/.unpack"
fi
echo "$bin"
