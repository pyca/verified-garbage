#!/usr/bin/env python3
"""The Rust jobs a CI run starts: the entries of ci/rust_matrix.toml's
matrices for the architectures it tests (see `rust-arches` in ci.yml).

The verified functions of each architecture are its own generated files,
`src/asm/<target>/`, which only that architecture compiles, and the Lean
proofs reach the Rust code only through them (CI checks that they are what
the emitter writes). So a pull request runs the Rust jobs of an
architecture only when it changes that architecture's files or anything else
that can change what the tests do (the shared Rust code, the tests, their
vectors, Cargo's files, the Rust jobs' workflow, matrices and scripts):
every path but those of one architecture and those in `NOT_RUST`. The merge
queue runs every job, and a push to main runs every job without its tests
(for main's caches).

  rust_arches.py pull_request < PATHS
      the jobs of the architectures the changed paths (one per line) reach
  rust_arches.py merge_group
      every job
  rust_arches.py push
      every job, with `tests` false

It prints, for $GITHUB_OUTPUT, `arches=<JSON list>` (those tested),
`all=true` or `all=false` (whether that is every architecture), and each
job's matrix (`rust=`, `thumb=`, `cpu=`): the JSON list of its entries,
each with `tests`, and each CPU with shards as one entry per shard.
"""

import json
from pathlib import Path
import sys
import tomllib

MATRIX = Path(__file__).resolve().parent / "rust_matrix.toml"
JOBS = ("rust", "thumb", "cpu")

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
    "ci/rust_matrix.toml",
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


def entries(matrix, job):
    """The matrix's entries of `job`, a CPU with shards once per shard."""
    out = []
    for entry in matrix[job]:
        entry = dict(entry)
        n = entry.pop("shards", None)
        if n is None:
            out.append(entry)
        else:
            out += [dict(entry, shard=f"{i}/{n}") for i in range(1, n + 1)]
    return out


def arch_of(entry):
    return entry.get("arch", "x86_64")  # the SDE chips'


def output(matrix, selected, tests=True):
    """The outputs of a run testing the architectures `selected` (or, without
    `tests`, building every job)."""
    everything = sorted(set(ARCHES.values()))
    lines = [
        f"arches={json.dumps(selected if tests else [])}",
        f"all={str(tests and selected == everything).lower()}",
    ]
    for job in JOBS:
        keep = [dict(e, tests=tests) for e in entries(matrix, job)
                if not tests or arch_of(e) in selected]
        lines.append(f"{job}={json.dumps(keep, separators=(',', ':'))}")
    return "".join(line + "\n" for line in lines)


def main(argv):
    matrix = tomllib.loads(MATRIX.read_text())
    everything = sorted(set(ARCHES.values()))
    if argv == ["pull_request"]:
        out = output(matrix, arches(line.strip() for line in sys.stdin if line.strip()))
    elif argv == ["merge_group"]:
        out = output(matrix, everything)
    elif argv == ["push"]:
        out = output(matrix, everything, tests=False)
    else:
        sys.exit(__doc__)
    sys.stdout.write(out)


if __name__ == "__main__":
    main(sys.argv[1:])
