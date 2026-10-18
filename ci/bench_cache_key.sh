#!/bin/sh
# The cache key of the benchmarks' dependencies, built in BENCH (a `bench/`
# checkout): everything their build depends on that changes, which is the
# compiler (`rustc -vV`), the target (CARGO_BUILD_TARGET when
# cross-compiling, as the armv7-cross image does, else the compiler's host)
# and the benchmark crate's manifest and lock file. ci.yml's `rust` job saves
# the entry on main; bench.yml's `compare` restores it.
set -e
bench=$1
# macOS has `shasum`, Linux `sha256sum`.
if command -v sha256sum >/dev/null; then sum="sha256sum"; else sum="shasum -a 256"; fi
target=${CARGO_BUILD_TARGET:-$(rustc -vV | sed -n 's/^host: //p')}
hash=$({ rustc -vV; cat "$bench/Cargo.toml" "$bench/Cargo.lock"; } | $sum | cut -c1-16)
echo "bench-deps-$target-$hash"
