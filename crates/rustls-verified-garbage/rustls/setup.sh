#!/bin/sh
# Checks out rustls at the release this provider is built against (its tag,
# `v/<version>`, for the version in Cargo.toml) into the directory given
# (default: the workspace's target/rustls), and applies each patch here to
# it: `tests.patch` gives rustls's API test suite a
# `tests_with_verified_garbage` module, which runs it with this provider,
# and `bench.patch` gives rustls-bench a `verified-garbage` provider.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
dir=${1:-$here/../../target/rustls}
version=$(sed -n 's/^rustls = { version = "=\([^"]*\)".*/\1/p' "$here/Cargo.toml" | head -n1)
rev=v/$version
if [ ! -d "$dir" ]; then
    git clone https://github.com/rustls/rustls "$dir"
fi
cd "$dir"
git fetch -q --tags origin
git checkout -q "$rev"
for patch in "$here"/rustls/*.patch; do
    sed "s#@VG_PROVIDER@#$here#g" "$patch" | git apply
done
echo "patched rustls $rev in $dir"
