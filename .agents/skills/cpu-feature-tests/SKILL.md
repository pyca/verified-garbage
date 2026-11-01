---
name: cpu-feature-tests
description: "Use when adding or changing an implementation chosen by CPU features, its tests, or ci/rust_matrix.toml and the test groups in ci/cpu_tests.py: how each VG_CPU_FEATURES configuration is tested end to end in CI."
---

# Testing CPU-feature configurations

A primitive with implementations for different CPU features is tested (and
benchmarked) end to end in each configuration, never through a special API:
the `cpu-features-env` Cargo feature lets `VG_CPU_FEATURES` restrict the
features detected (see `src/cpu.rs`). CI tests each configuration that
chooses differently on a CPU that has those features: the runner's, or one
Intel SDE presents (`rust-cpu-features` in `ci.yml`, whose CPUs are the
`cpu` entries of `ci/rust_matrix.toml`; SDE runs the SHA
extensions' code very slowly, so the chips that have them run only the
tests that need them); and benchmarks each with
`VG_CPU_FEATURES` (`CPU_FEATURES` in `ci/bench_arches.py`). A configuration
to test is a line of a CPU's `runs` in `ci/rust_matrix.toml`
(`<VG_CPU_FEATURES> | <groups>`), never a step or job of its own, and
each CPU has one line per value of `VG_CPU_FEATURES` (CI checks both), so
a run never repeats another: add groups to a CPU's line for those features.
A group (`GROUPS` in `ci/cpu_tests.py`) names its tests explicitly, by the
path of each test or of the module around it, in the library's unit tests
and in the integration tests (`tests/main.rs` and `tests/cavp.rs`, which
holds those under `cavp::`); a line runs exactly those tests, so a new test of a
primitive that varies by CPU feature goes into its group (or a new group),
never into a line by matching part of its name. CI fails a path that
selects no test on any CPU, and a group that selects none on a line's CPU.
A CPU whose lines take long runs as shards (its `shards = n`: n jobs, each
with a `shard` of `i/n`), which deal out its
lines by the CPU time each took on `main` (`ci/cpu_shards.py`): to speed
one up, add a shard, never split its lines by hand.
To test the baseline ISA's implementations:

```sh
VG_CPU_FEATURES=none WYCHEPROOF_ROOT=/path/to/wycheproof cargo test --features cpu-features-env
```
