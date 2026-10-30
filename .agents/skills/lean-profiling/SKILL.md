---
name: lean-profiling
description: "Use when making Lean proofs or the CI Lean build faster, choosing what to optimize, or measuring a proof-performance change: the build's recorded profile, ci/lean_profile.py, ci/lean_closure.py, perf instruction counts and heartbeat profiles."
---

# Finding what to optimize

Start from the build's own profile, not from a profiling build. Every
module is built with Lean's `profiler` on (`moreLeanArgs` in
`lean/lakefile.toml`): each step over a millisecond is recorded, at its
declaration, in the module's `.trace`. The CI build cache ships them in one
file, which `unpack` writes only with `--logs`
(`… | python3 ci/lean_cache.py unpack --logs lean`; `lean/README.md`). After
restoring the cache so, from the repository root:

```sh
python3 ci/lean_profile.py                        # the 30 costliest declarations
python3 ci/lean_profile.py --sort kernel          # by kernel time alone
python3 ci/lean_profile.py --by module --top 50   # the costliest modules
python3 ci/lean_profile.py --module VerifiedGarbage.Proof.Sha256 --json
python3 ci/lean_profile.py --tests                # with the known-answer tests
python3 ci/check_lit_imports.py                   # checks evaluating code without its literal
python3 ci/lean_closure.py rank                   # modules by what CI spends building them
python3 ci/lean_closure.py rank --by decl         # declarations, likewise
```

A proof's own time is not what CI spends on it: a module that the shards
of a full rebuild share is built by each of them, and one that many changes
reach is rebuilt by each run. `rank` weighs each module's (or declaration's)
time by the times CI builds it per commit, replaying the last 200 commits
of `main` through CI's plan (`--commits`), with its builds in a full
rebuild beside it (two minutes; no builds): prefer its top rows to
`lean_profile.py`'s when choosing what to make faster.

A command that generates declarations (`materialize_code`, `taint_summary`,
`run_cmd`) has no declaration range: its row is its line and the start of
that line of the source, `[line 70] taint_summary winBuildSum : …`. The
known-answer tests in `VerifiedGarbageTest`, which cost spec evaluation
rather than proofs, are left out unless `--tests` (or `--module` naming
them) is given.

Each declaration's time is `kernel` (the kernel checking it: large proof
terms, `decide +kernel`, `taint_decide`, `lit_decide`) and `elab`
(everything else: tactics, `simp`, `omega`, instances, compilation), which
point at different patterns of the `proof-performance` skill (kernel: literals, taint summaries,
`Nat` data; elaboration: symbolic execution, `omega`, unfolding). `blocked`
is time its task waited for another, such as the kernel checking a lemma it
uses: look at that lemma, not at the declaration. The times are wall-clock
times of one CI build, good for ranking. Pick targets from them, then study
a declaration with the per-file profiles below, and measure a change by
instructions or heartbeats, as below, never by this table. Modules you
rebuild locally record your machine's times in place of CI's.

What a module costs CI depends on its imports too: each shard
(`ci/lean_shards.py`) builds its sinks' whole import closures, so a module
two shards need is built twice. `ci/lean_closure.py` shows where (after
`python3 ci/ci_metrics.py fetch .ci-metrics 30`, and `profile` once the cache
is restored): `sinks` ranks the sinks by closure time, `dominators SINK`
gives the time each module brings into SINK's closure alone, and `score`
replays CI's plan of a full rebuild and of the recent runs with the imports
of `origin/main` and of the working tree (or `--drop A:B`; `--merge NEW=A,B`
for merged modules; `--profile-branch`, after building the branch, for
proofs it makes faster). Judge an import
cut by `score`, not by a closure's size: a subtree a sink drags in is often
built in its shard anyway, and the greedy plan moves by a few seconds with
any change.

Lake replays a module's recorded messages, the profile included, whenever
it finds the module built: build with `lake build --log-level=warning` (or
`-q`), as every command here does, to see only warnings and errors. A
module with `#guard_msgs`, which would compare the profile of its command
with the expected messages, turns the profiler off
(`set_option profiler false`; `ci/check_lean_speed.py` checks it).

To see where one declaration spends its time, profile its file (time under
`[Kernel]` is the kernel checking the term):

```sh
lake env lean -DElab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 \
  VerifiedGarbage/Proof/….lean
```

To compare two versions of a file, count its instructions, which (unlike
time) do not depend on the load of the machine; pass the lakefile's options,
as `lake build` does (it turns off Mathlib's style and tactic-analysis
linters, 5–8% of the build: never turn them back on in a module), but not
its profiler:

```sh
lake setup-file --log-level=warning VerifiedGarbage/Proof/….lean > .lake/setup.json
opts=$(grep -oE "^weak\.[A-Za-z_.]+ = (true|false)" lakefile.toml | sed -E 's/ = /=/; s/^/-D/' | tr '\n' ' ')
perf stat -e instructions:u -x, lake env lean --setup .lake/setup.json $opts -Dprofiler=false VerifiedGarbage/Proof/….lean
perf stat -e instructions:u -x, lake env true   # Lake's own startup: subtract it
```

`--setup` loads the precompiled libraries (`Native*` in the lakefile) as
`lake build` does; without it the interpreter runs their tactics, many
times slower. The setup file serves edited copies of the module too.
`lake env` starts Lake for every command (about 3.5e9 instructions), which
a build does once: subtract it before quoting a relative change.

`set_option diagnostics true in` before a slow theorem lists the
definitions unfolded while elaborating it, which finds failing unfoldings.
`#count_heartbeats in` (from `Mathlib.Util.CountHeartbeats`, imported only
while measuring) before a declaration prints the heartbeats it uses
against the 200000 budget.

For allocation-based work comparisons without adding an import, use Lean's
heartbeat profiler. From `lean/`, write the module's setup file, which
supplies the same options and imports as Lake (`lake setup-file` builds the
module's imports, not the module, and prints it; the build cache keeps none):

```sh
lake setup-file --log-level=warning VerifiedGarbage/Proof/MlKem/Arm/Mul.lean > .lake/setup.json
lake env lean --setup .lake/setup.json \
  -j1 -DElab.async=false -Dtrace.profiler=true \
  -Dtrace.profiler.useHeartbeats=true -Dtrace.profiler.threshold=1000000000 \
  -Dtrace.Elab.command=true -Dtrace.Kernel=true \
  VerifiedGarbage/Proof/MlKem/Arm/Mul.lean
```

Traces are inclusive: report the command and kernel counts separately, not
added up. Run elapsed-time benchmarks without tracing.

When changing proof or build performance, compare representative callers of
a shared helper (large proofs, different postcondition shapes), not one;
compare baseline and candidate on the same revision, toolchain, hardware and
cache state; and back a claim of an overall speedup with a clean full build,
audits and golden tests included. Keep the two compiler threads and six Lake
workers measured in [PR #367](https://github.com/pyca/verified-garbage/pull/367)
unless a controlled build comparison on the intended runner supports
changing them.
