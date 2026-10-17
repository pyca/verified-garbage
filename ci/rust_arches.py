#!/usr/bin/env python3
"""The architectures whose Rust tests a pull request runs (see ci.yml).

The verified functions of each architecture are its own generated files,
`src/asm/<target>/`, which only that architecture compiles, and the Lean
proofs reach the Rust code only through them (CI checks that they are what
the emitter writes). So a pull request runs the Rust tests of an
architecture only when it changes that architecture's files or anything else
that can change what the tests do (the shared Rust code, the tests, their
vectors, Cargo's files, the Rust jobs' workflow and scripts): every path
but those of one architecture and those in `NOT_RUST`.

  rust_arches.py < PATHS
      reads the changed paths, one per line, and prints
      `arches=<JSON list>` for $GITHUB_OUTPUT, and `all=true` or
      `all=false`
  rust_arches.py --all
      the same for every architecture
"""

import json
import sys

# `src/asm/<target>/`'s target, and the architecture (`target_arch`) it is
# compiled for.
ARCHES = {
    "aarch64": "aarch64",
    "arm": "arm",
    "x86": "x86",
    "x86_64": "x86_64",
}

# Paths that no Rust test reads or runs: the Lean sources (whose output is
# `src/asm/`), the benchmarks (a crate of their own, which the `rust` job
# lints whatever the architectures), documentation, and the workflows and
# actions of the Lean build and the benchmarks.
NOT_RUST_PREFIXES = (
    "lean/",
    "bench/",
    "docs/",
    ".github/actions/lean-",
)
NOT_RUST_FILES = {
    "AGENTS.md",
    "CLAUDE.md",
    "README.md",
    "LICENSE",
    "LICENSE.APACHE",
    "LICENSE.BSD",
    "logo.svg",
    "logo-dark.svg",
    ".github/workflows/bench.yml",
    ".github/workflows/lean-cache.yml",
}

# The scripts under ci/ that the Rust jobs run (or build their images from);
# every other one is the Lean build's, the benchmarks' or a static check's.
# ci/test_check_rust_arches.py checks that ci.yml's Rust jobs use no other.
RUST_CI = {
    "ci/arm32-run",
    "ci/bench_cache_key.sh",
    "ci/cpu_shards.py",
    "ci/cpu_tests.py",
    "ci/export_rust_coverage.py",
    "ci/merge_rust_coverage.py",
    "ci/requirements-coverage.txt",
    "ci/runner.Dockerfile",
    "ci/rust_arches.py",
}


def arches_of(path):
    """The architectures whose tests a change to `path` runs."""
    if path.startswith("src/asm/"):
        target = path.split("/")[2]
        if target in ARCHES and path.count("/") > 2:
            return {ARCHES[target]}
        return set(ARCHES.values())  # src/asm/mod.rs, or a new target
    if path.startswith(NOT_RUST_PREFIXES) or path in NOT_RUST_FILES:
        return set()
    if path.startswith("ci/") and path.count("/") == 1 and path not in RUST_CI:
        return set()
    return set(ARCHES.values())


def arches(paths):
    out = set()
    for path in paths:
        out |= arches_of(path)
    return sorted(out)


def output(selected):
    return f"arches={json.dumps(selected)}\nall={str(len(selected) == len(set(ARCHES.values()))).lower()}\n"


def main(argv):
    if argv == ["--all"]:
        selected = sorted(set(ARCHES.values()))
    elif not argv:
        selected = arches(line.strip() for line in sys.stdin if line.strip())
    else:
        sys.exit(__doc__)
    sys.stdout.write(output(selected))


if __name__ == "__main__":
    main(sys.argv[1:])
