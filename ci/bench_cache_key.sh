#!/bin/sh
# The cache key of the benchmarks' dependencies, built in BENCH (a `bench/`
# checkout): everything their build depends on that changes, which is the
# compiler (`rustc -vV`), the target (CARGO_BUILD_TARGET when
# cross-compiling, as the armv7-cross image does, else the compiler's host),
# Cargo's home and the benchmark crate's manifest and lock file. Prints
# `key=<key>` and `prefix=<prefix>` for $GITHUB_OUTPUT: the prefix leaves out
# the manifest and lock file, so that a branch that changes them (adding a
# dependency, as a benchmark of one architecture's internal functions does)
# restores main's entry for the same compiler and rebuilds only what changed,
# not every dependency (RISC-V's runners took six minutes). Cargo's
# fingerprint of a crate from the registry includes the path of its sources,
# under Cargo's home, so an entry built in an image with another home (as
# PPC64LE's was, before its runner image set CARGO_HOME) restores, but every
# dependency is built again. ci.yml's `rust` job saves the entry on main;
# bench.yml's `compare` restores it.
set -e
bench=$1
# macOS has `shasum`, Linux `sha256sum`.
if command -v sha256sum >/dev/null; then sum="sha256sum"; else sum="shasum -a 256"; fi
target=${CARGO_BUILD_TARGET:-$(rustc -vV | sed -n 's/^host: //p')}
home=${CARGO_HOME:-$HOME/.cargo}
tools=$({ rustc -vV; echo "$home"; } | $sum | cut -c1-16)
deps=$(cat "$bench/Cargo.toml" "$bench/Cargo.lock" | $sum | cut -c1-16)
echo "key=bench-deps-$target-$tools-$deps"
echo "prefix=bench-deps-$target-$tools-"
