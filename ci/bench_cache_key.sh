#!/bin/sh
# The cache key of the benchmarks' dependencies, built in BENCH (a `bench/`
# checkout): everything their build depends on that changes, which is the
# compiler (`rustc -vV`, whose host names the architecture) and the
# benchmark crate's manifest and lock file. ci.yml's `rust` job saves the
# entry on main; bench.yml's `compare` restores it.
set -e
bench=$1
hash=$({ rustc -vV; cat "$bench/Cargo.toml" "$bench/Cargo.lock"; } | sha256sum | cut -c1-16)
echo "bench-deps-$(rustc -vV | sed -n 's/^host: //p')-$hash"
