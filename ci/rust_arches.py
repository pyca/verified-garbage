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
every path but those of one architecture and those in `NOT_RUST`. A module
of the library or of the tests reaches only the architectures its `cfg`s let
it compile (`compiled_for`). Each architecture's jobs cover every line it
builds (ci/merge_rust_coverage.py), so a pull request's coverage is checked
for those it tests. The merge queue does the same with the paths its group
changes from the group's base (main, or the group ahead of it), which
passed: an architecture none of them reaches builds and runs exactly what
passed there. What that leaves out, which changes outside the repository
(runners, Rust's releases, Wycheproof's vectors), is tested by the full runs
that the Full CI workflow starts on main every few hours, when main has
moved, and by any run started by hand (`workflow_dispatch`): every job. A
push to main builds without tests, for main's caches: every job of `rust`
and `thumb`, and of `cpu`, whose jobs all build the same tests into one
cache per platform, the first entry of each (see `cache_of`).

  rust_arches.py pull_request [BASE HEAD] < PATHS
  rust_arches.py merge_group [BASE HEAD] < PATHS
      the jobs of the architectures the changed paths (one per line) reach,
      between the commits BASE and HEAD (or in the working tree)
  rust_arches.py workflow_dispatch
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
`rust-lint` lints (ci/rust_lint.py): every one when a run tests some
architecture, those of the others too, so that whatever ci/rust_arches.py
leaves out is still built and linted (one run of Cargo for all of them), but
with `bench`, the benchmarks, only for those tested; every one, with `bench`,
when the benchmarks changed, and on a push to main (for its caches) or a full
run; and none when nothing reaches Rust.
"""

import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

import bench_arches

MATRIX = Path(__file__).resolve().parent / "rust_matrix.toml"
ROOT = Path(__file__).resolve().parent.parent
JOBS = ("rust", "thumb", "cpu")
EVENTS = ("pull_request", "merge_group")

# `src/asm/<target>/`'s target, and the architecture (`target_arch`) it is
# compiled for.
ARCHES = {
    "aarch64": "aarch64",
    "arm": "arm",
    "powerpc64le": "powerpc64",
    "riscv64": "riscv64",
    "x86": "x86",
    "x86_64": "x86_64",
}

# Paths that no Rust test reads or runs: the Lean sources (whose output is
# `src/asm/`), the benchmarks (a crate of their own, which only `rust-lint`
# builds, for every target: see `output`), documentation, and the workflows
# and actions of the Lean build and the benchmarks.
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
    ".github/workflows/full-ci.yml",
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


def arches_of(path, versions=()):
    """The architectures whose tests a change to `path` runs, given the
    versions of the tree it changes between (functions from a path to its
    text, or None where it does not exist)."""
    if path.startswith("src/asm/"):
        target = path.split("/")[2]
        if target in ARCHES and path.count("/") > 2:
            return {ARCHES[target]}
        return set(ARCHES.values())  # src/asm/mod.rs, or a new target
    if path.startswith(NOT_RUST_PREFIXES) or path in NOT_RUST_FILES:
        return set()
    if path.startswith("ci/") and path.count("/") == 1 and path not in RUST_CI:
        return set()
    if is_module(path):
        out, seen = set(), False
        for read in versions:
            if read(path) is not None:
                seen = True
                out |= {a for a in ARCHES.values() if compiled_for(path, a, read)}
        if seen:
            return out
    return set(ARCHES.values())


# A module of the library or of the test binary is compiled only for the
# architectures its `cfg`s admit: its inner `#![cfg(...)]`s, those on its
# `mod` line, and its parent module's, up to the crate's root. So a change to
# it reaches only those, in either version (a change to the `cfg` itself
# reaches the architectures it admitted and those it admits). A predicate
# other than `target_arch` (a feature, `test`) may hold or not, so a module is
# left out only where its `cfg`s are false whatever those are; a file that is
# no module (one `include!`d) has no `mod` line, and is gated by its own
# `cfg`s alone.
ROOTS = ("src/lib.rs", "tests/main.rs")


def is_module(path):
    return path.endswith(".rs") and path.startswith(("src/", "tests/"))


def parent_of(path):
    """The module's name, and the files that may declare it; None at the
    top of `src/` or `tests/`."""
    parts = path.split("/")
    if parts[-1] in ("mod.rs", "main.rs", "lib.rs"):
        name, container = parts[-2], parts[:-2]
    else:
        name, container = parts[-1][: -len(".rs")], parts[:-1]
    if not container:
        return None
    d = "/".join(container)
    return name, [f"{d}/mod.rs", f"{d}/main.rs", f"{d}/lib.rs", f"{d}.rs"]


def ancestors(path):
    """Every file `compiled_for` may read for `path`."""
    out = [path]
    while path not in ROOTS and (parent := parent_of(path)) is not None:
        out += parent[1]
        path = parent[1][0]  # each candidate has the same parent candidates
    return out


def balanced(text, start):
    """The text inside the parentheses opened just before `start`."""
    depth, i = 1, start
    while depth:
        if i == len(text):
            return None
        depth += {"(": 1, ")": -1}.get(text[i], 0)
        i += 1
    return text[start : i - 1]


def cfgs(text, opener):
    out = []
    for m in re.finditer(opener, text):
        body = balanced(text, m.end())
        out.append(body if body is not None else "")
    return out


def mod_cfgs(text, name):
    """The `cfg`s on the line `mod <name>;` of `text`, or None if it has none."""
    m = re.search(rf"(?m)^((?:[ \t]*#\[[^\]]*\][ \t]*\n)*)[ \t]*(?:pub(?:\([^)]*\))?\s+)?mod\s+{name}\s*;", text)
    return None if m is None else cfgs(m.group(1), r"#\[cfg\(")


def evaluate(cfg, arch):
    """Whether `cfg` holds on `arch`: True, False, or None when it depends on
    other predicates."""
    tokens = re.findall(r'"[^"]*"|[A-Za-z_][A-Za-z0-9_]*|[(),=]', cfg)
    pos = 0

    def take():
        nonlocal pos
        pos += 1
        return tokens[pos - 1]

    def pred():
        name = take()
        if pos < len(tokens) and tokens[pos] == "=":
            take()
            value = take().strip('"')
            return value == arch if name == "target_arch" else None
        if pos < len(tokens) and tokens[pos] == "(":
            take()
            args = []
            while tokens[pos] != ")":
                args.append(pred())
                if tokens[pos] == ",":
                    take()
            take()
            if name == "not":
                return None if args[0] is None else not args[0]
            if name == "all":
                return False if False in args else None if None in args else True
            if name == "any":
                return True if True in args else None if None in args else False
        return None

    try:
        return pred()
    except IndexError:
        return None  # unparseable: it may hold


def compiled_for(path, arch, read):
    """Whether the module `path` may be compiled for `arch` in the tree `read`."""
    while True:
        text = read(path)
        if text is None:
            return True
        if any(evaluate(c, arch) is False for c in cfgs(text, r"(?m)^[ \t]*#!\[cfg\(")):
            return False
        if path in ROOTS or parent_of(path) is None:
            return True
        name, candidates = parent_of(path)
        for parent in candidates:
            declared = read(parent)
            on_mod = None if declared is None else mod_cfgs(declared, name)
            if on_mod is not None:
                break
        else:
            return True  # no `mod` line: not a module, or one we cannot find
        if any(evaluate(c, arch) is False for c in on_mod):
            return False
        path = parent


def git_versions(revs, paths):
    """Readers of the trees of the commits `revs`, with every file that
    `arches_of` may read for `paths` read at once: the checkout is a sparse,
    blobless clone, which would otherwise fetch them one by one."""
    wanted = sorted({a for p in paths if is_module(p) for a in ancestors(p)})
    if not wanted:
        return [lambda _: None for _ in revs]
    oids = []
    for rev in revs:
        listing = subprocess.run(["git", "ls-tree", "-z", "--full-tree", rev, "--", *wanted],
                                 check=True, capture_output=True, text=True).stdout
        oids.append({line.split("\t", 1)[1]: line.split()[2]
                     for line in listing.split("\0") if line and line.split()[1] == "blob"})
    every = sorted({o for found in oids for o in found.values()})
    if every:
        present = subprocess.run(["git", "cat-file", "--batch-check"], input="\n".join(every) + "\n",
                                 check=True, capture_output=True, text=True).stdout
        missing = [line.split()[0] for line in present.splitlines() if line.endswith(" missing")]
        if missing:
            subprocess.run(["git", "-c", "fetch.negotiationAlgorithm=noop", "fetch", "-q", "--no-tags",
                            "--no-write-fetch-head", "--filter=blob:none", "origin", *missing], check=True)
    texts = {}
    for o in every:
        texts[o] = subprocess.run(["git", "cat-file", "blob", o], check=True,
                                  capture_output=True).stdout.decode("utf-8", "replace")
    return [lambda path, found=found: texts.get(found.get(path)) for found in oids]


def tree_version(path):
    """The working tree's text of `path`, or None."""
    try:
        return (ROOT / path).read_text()
    except (FileNotFoundError, IsADirectoryError):
        return None


def arches(paths, versions=()):
    out = set()
    for path in paths:
        out |= arches_of(path, versions)
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
    if bench or not tests:
        lint = matrix["lint"]
    elif selected:
        lint = [e if e["arch"] in selected else {k: v for k, v in e.items() if k != "bench"}
                for e in matrix["lint"]]
    else:
        lint = []
    lines.append(f"lint={json.dumps(lint, separators=(',', ':'))}")
    return "".join(line + "\n" for line in lines)


def main(argv):
    matrix = tomllib.loads(MATRIX.read_text())
    everything = sorted(set(ARCHES.values()))
    if len(argv) in (1, 3) and argv[0] in EVENTS:
        paths = [line.strip() for line in sys.stdin if line.strip()]
        versions = git_versions(argv[1:], paths) if len(argv) == 3 else [tree_version]
        out = output(matrix, arches(paths, versions), bench=any(p.startswith("bench/") for p in paths))
    elif argv == ["workflow_dispatch"]:
        out = output(matrix, everything)
    elif argv == ["push"]:
        out = output(matrix, everything, tests=False)
    else:
        sys.exit(__doc__)
    sys.stdout.write(out)


if __name__ == "__main__":
    main(sys.argv[1:])
