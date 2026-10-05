#!/bin/sh
# Checks out rustls at the revision this provider is built against, into
# the directory given (default: target/rustls), and patches it to use the
# provider: its API test suite gets a `tests_with_verified_garbage` module,
# and rustls-bench a `verified-garbage` feature and provider.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
dir=${1:-$here/target/rustls}
rev=$(sed -n 's/.*rustls\.git", rev = "\([0-9a-f]*\)".*/\1/p' "$here/Cargo.toml" | head -n1)
if [ ! -d "$dir" ]; then
    git clone https://github.com/rustls/rustls "$dir"
fi
cd "$dir"
git checkout -q "$rev"
sed "s#@VG_PROVIDER@#$here#g" "$here/bench/rustls.patch" | git apply
echo "patched rustls $rev in $dir"
