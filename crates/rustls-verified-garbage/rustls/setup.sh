#!/bin/sh
# Checks out rustls at the revision this provider is built against, into
# the directory given (default: the workspace's target/rustls), and applies each patch here
# to it: `tests.patch` gives rustls's API test suite a
# `tests_with_verified_garbage` module, which runs it with this provider.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
dir=${1:-$here/../../target/rustls}
rev=$(sed -n 's/.*github.com\/rustls\/rustls", rev = "\([0-9a-f]*\)".*/\1/p' "$here/Cargo.toml" | head -n1)
if [ ! -d "$dir" ]; then
    git clone https://github.com/rustls/rustls "$dir"
fi
cd "$dir"
git checkout -q "$rev"
for patch in "$here"/rustls/*.patch; do
    sed "s#@VG_PROVIDER@#$here#g" "$patch" | git apply
done
echo "patched rustls $rev in $dir"
