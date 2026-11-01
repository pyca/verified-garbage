#!/usr/bin/env python3
"""The Rust jobs a CI run starts: the entries of ci/rust_matrix.toml's
matrices for the architectures it tests (see `rust-arches` in ci.yml).

The verified functions of each architecture are its own crate of generated
code, `crates/verified-garbage-asm-<target>/`, which only that architecture compiles, and the Lean
proofs reach the Rust code only through them (CI checks that they are what
the emitter writes). So a pull request runs the Rust jobs of an
architecture only when it changes that architecture's files or anything else
that can change what the tests do (the shared Rust code, the tests, their
vectors, Cargo's files, the Rust jobs' workflow, matrices and scripts):
every path but those of one architecture and those in `NOT_RUST`. Each
architecture's jobs cover every line it builds (ci/merge_rust_coverage.py),
so a pull request's coverage is checked for those it tests. The merge queue
runs every job, and a push to main builds without tests, for main's caches:
every job of `rust` and `thumb`, and of `cpu`, whose jobs all build the same
tests into one cache per platform, the first entry of each (see `cache_of`).

  rust_arches.py pull_request < PATHS
      the jobs of the architectures the changed paths (one per line) reach
  rust_arches.py merge_group
      every job
  rust_arches.py push
      one job per cache, with `tests` false

It prints, for $GITHUB_OUTPUT, `arches=<JSON list>` (those tested),
`all=true` or `all=false` (whether that is every architecture), and each
job's matrix (`rust=`, `thumb=`, `cpu=`): the JSON list of its entries,
each with `tests`, and each CPU with shards as one entry per shard. Each
`rust` entry also has `bench`: whether the Benchmarks workflow measures its
architecture (ci/bench_arches.py's `PLATFORMS`), for which a push to main
caches the benchmarks' dependencies. `lint=` is the JSON list of the targets
`rust-lint` lints (ci/rust_lint.py): those of the architectures tested, or
every one when the benchmarks changed, or on a push to main (for its
caches).
"""

import json
import re
from pathlib import Path
import sys
import tomllib

import asm_layout
import bench_arches

MATRIX = Path(__file__).resolve().parent / "rust_matrix.toml"
JOBS = ("rust", "thumb", "cpu")

# The target of a crate of generated code, `crates/verified-garbage-asm-<target>/`,
# and the architecture (`target_arch`) it is compiled for.
ARCHES = {
    "aarch64": "aarch64",
    "arm": "arm",
    "powerpc64le": "powerpc64",
    "riscv64": "riscv64",
    "x86": "x86",
    "x86_64": "x86_64",
}

# Paths that no Rust test reads or runs: the Lean sources (whose output is
# the crates of generated code), the benchmarks (a crate of their own, which only `rust-lint`
# builds, for every target: see `output`), documentation (agents' skills
# too), and the workflows and actions of the Lean build and the benchmarks.
NOT_RUST_PREFIXES = (
    "lean/",
    "bench/",
    "docs/",
    ".agents/",
    ".claude/",
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
    "ci/rust_lint.py",
    "ci/rust_matrix.toml",
    "ci/rust_test_timing.sh",
    "ci/rustdoc_timing.sh",
    "ci/rustdoc_timing.cmd",
}


def arches_of(path):
    """The architectures whose tests a change to `path` runs."""
    # A target's crate of generated code (`asm_layout`), its manifest too.
    if m := re.match(rf"{asm_layout.CRATES}/{asm_layout.PREFIX}([a-z0-9_]+)/", path):
        return {ARCHES[m[1]]} if m[1] in ARCHES else set(ARCHES.values())
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


def cache_of(entry):
    """What a `cpu` job's cache entry depends on but for what every one
    shares. Swatinem/rust-cache keys it by the job's `shared-key`, the
    runner's OS and architecture, the compiler's version (which the
    container's sets: the x86 image's is i686's) and the environment's
    CARGO*/RUST*/CC* variables (the same for every entry), and the
    lockfiles."""
    runner = entry.get("runner") or entry.get("os") or "ubuntu-26.04"
    return (runner.endswith("-arm"), json.dumps(entry.get("container"), sort_keys=True))


def output(matrix, selected, tests=True, bench=False):
    """The outputs of a run testing the architectures `selected` (or, without
    `tests`, building one job per cache), whose changes reach the benchmarks
    if `bench`."""
    everything = sorted(set(ARCHES.values()))
    lines = [
        f"arches={json.dumps(selected if tests else [])}",
        f"all={str(tests and selected == everything).lower()}",
    ]
    for job in JOBS:
        keep = [dict(e, tests=tests) for e in entries(matrix, job)
                if not tests or arch_of(e) in selected]
        if job == "rust":
            keep = [dict(e, bench=arch_of(e) in bench_arches.PLATFORMS) for e in keep]
        if not tests and job == "cpu":
            first = {}
            for e in keep:
                first.setdefault(cache_of(e), e)
            keep = list(first.values())
        lines.append(f"{job}={json.dumps(keep, separators=(',', ':'))}")
    lint = [e for e in matrix["lint"] if bench or not tests or e["arch"] in selected]
    lines.append(f"lint={json.dumps(lint, separators=(',', ':'))}")
    return "".join(line + "\n" for line in lines)


def main(argv):
    matrix = tomllib.loads(MATRIX.read_text())
    everything = sorted(set(ARCHES.values()))
    if argv == ["pull_request"]:
        paths = [line.strip() for line in sys.stdin if line.strip()]
        out = output(matrix, arches(paths), bench=any(p.startswith("bench/") for p in paths))
    elif argv == ["merge_group"]:
        out = output(matrix, everything)
    elif argv == ["push"]:
        out = output(matrix, everything, tests=False)
    else:
        sys.exit(__doc__)
    sys.stdout.write(out)


if __name__ == "__main__":
    main(sys.argv[1:])
