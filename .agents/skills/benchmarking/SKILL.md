---
name: benchmarking
description: "Use when a change could make code slower or claims to make it faster, or when running benchmarks or the Benchmarks workflow: how to measure only what the change affects, locally and with a scoped manual workflow run."
---

# Measuring a change's speed

Measure only what the change affects. `python3 ci/bench_arches.py --choices`
lists the architectures, each one's `VG_CPU_FEATURES` configurations and the
features `src/cpu.rs` detects there, and the library modules with the
benchmarks that use each (a benchmark's `USES`). On this machine, for the
features its CPU has (`/proc/cpuinfo`):

```sh
VG_CPU_FEATURES=avx,avx2 python3 ci/bench_compare.py --modules chacha20 path/to/main-checkout .
(cd bench && VG_CPU_FEATURES=none VG_BENCH_MODULES=chacha20 cargo bench -- '^chacha20/verified-garbage/')
```

A benchmark whose code reads a comb's table of hundreds of kilobytes
(P-521's) is up to about 7% faster or slower depending on which physical
pages the kernel gives the table when it first reads the binary, a draw
fixed for each binary file: comparing one run of each side compares two
draws, not the code. So `ci/bench_compare.py` runs those groups
(`FRESH_COPIES`) from `--copies` fresh copies of each side's binary and
compares the fastest of each; add a group there when its code reads such a
table.

For another architecture, or features this CPU lacks, run the Benchmarks
workflow by hand: it never runs on its own (not on pull requests, not on
`main`). Its runners are the ones CI waits for, so scope every run as
narrowly as the change allows. First ask which jobs the change needs:

```sh
git diff --name-only origin/main HEAD | python3 ci/bench_arches.py --base origin/main
```

prints a JSON list, one entry per job, each with its `arch`, `cpu-features`
and `modules` (empty: every benchmark; such architectures it leaves out,
naming them on stderr). Then run the workflow on the pushed branch with
those values, one run per architecture when they differ between
architectures:

```sh
gh workflow run bench.yml --ref my-branch -f base_commit=$(git rev-parse origin/main) \
  -f arches=aarch64 -f cpu_features='- none sha3' -f modules=ecdsa_p256
```

`--ref` is the branch (or tag) measured, at its tip; `base_commit` is any
commit to compare it with, as a full or abbreviated SHA, a branch or a tag,
which the workflow resolves to the full SHA (empty to run the branch alone,
next to OpenSSL and aws-lc-rs). `arches`, `cpu_features` (space-separated configurations,
`-` for none; empty for those choosing among the modules' implementations)
and `modules` narrow the run (`python3 ci/bench_arches.py --choices` lists
their values); `openssl=true` adds OpenSSL's and aws-lc-rs's times to a
comparison, which only costs time: leave it off. To measure a commit that
is no branch's tip, push a branch at it
(`git push origin <sha>:refs/heads/bench/<name>`) and delete it after. The
results are in each job's summary.

Never run every benchmark (`modules` empty: leaving `arches`,
`cpu_features` and `modules` all empty runs every benchmark of every
architecture in about thirty jobs, and `arches` alone every benchmark of
that architecture) unless the change truly needs it and cannot be measured
otherwise: a change to the benchmarks' shared code or `bench/Cargo.lock`,
whose architectures `bench_arches.py` names on stderr. Even then, run only
the architectures it names, and prefer a module or two that show the
change's effect over all of them. Never rerun a benchmark to get a better
number, and never run one for a change that cannot affect speed (Lean
proofs that leave the generated crates as they were, tests, docs, CI).
