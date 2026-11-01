# `ci/`

The scripts CI runs, the checks to run before pushing (CLAUDE.md, "Checks
to run before pushing"), and the tools for measuring the build. Each
script's docstring says how to run it. `python3 ci/run_unit_tests.py` runs
their unit tests, `test_check_*.py` (CI does too).

## Checks

CI runs each of these, and fails if it does:

| Script | Checks |
|---|---|
| `algorithms_table.py --check` | README.md's algorithm tables are current (without `--check`, regenerates them) |
| `audit_negative.py` | The axiom audit rejects an axiom hidden in a Lean module |
| `check_arch_gates.py` | Tests and benchmarks are built on exactly the architectures of the code they run |
| `check_case_collisions.py` | No two tracked paths differ only in case |
| `check_lean_imports.py` | The import discipline between `TCB/`, `Spec/`, `Impl/` and `Proof/` |
| `check_lean_modules.py` | Every file under `lean/VerifiedGarbage/` is a Lean module |
| `check_lean_single_importer.py` | No new proof module has only one importer without saying why |
| `check_lean_speed.py` | The rules of "Keeping proofs fast" that need no build (allowances in `lean_speed_allowed.py`) |
| `check_mcdt.py` | Intel's MCDT instructions run only inside the MXCSR prologue and epilogue |
| `check_registrations.py` | Registration and variant files only bind |
| `check_skills.py` | The skills' frontmatter and links, and CLAUDE.md's list of them |
| `check_variants.py` | Every variant reaches every function built on it |
| `check_vectors.py` | `vectors/sources/` describes the files under `vectors/` |
| `cpu_tests.py lint` | `rust_matrix.toml`'s CPU-feature lines |
| `merge_rust_coverage.py` | 100% line coverage, per architecture and merged (from `export_rust_coverage.py`'s files) |
| `rust_lint.py` | rustfmt, Clippy and a release build for every target |

`check_lean_public_imports.py` is a check that CI does not run, since it
needs the edited modules built: run it before pushing, as CLAUDE.md says.

## CI's own machinery

| File | Does |
|---|---|
| `lean_shards.py` | Plans how the Lean build splits across runners, and keeps the timing manifest |
| `lean_cache.py`, `leantar/` | Packs and restores the per-module Lean cache archives (with a patched `leantar`) |
| `fetch_lean_cache.py` | Streams the published Lean cache, resuming dropped connections (lean/README.md) |
| `rust_arches.py` | The Rust jobs a change needs, from `rust_matrix.toml` |
| `cpu_tests.py`, `cpu_shards.py` | The tests of each CPU-feature line, and their split across shards |
| `export_rust_coverage.py` | Exports an instrumented test run's coverage as lcov |
| `rust_test_timing.sh`, `rustdoc_timing.sh`, `rustdoc_timing.cmd` | Turn on libtest's `--report-time` for the timing metrics |
| `bench_arches.py`, `bench_compare.py`, `bench_cache_key.sh` | The Benchmarks workflow (the `benchmarking` skill) |
| `ci_metrics.py`, `ci_metrics_bundle.py` | Record each run's metrics, and fetch and share them (the `ci-metrics` skill) |
| `runner.Dockerfile`, `arm32-run` | The runner images of the 32-bit, PPC64LE, RISC-V and lint jobs |
| `requirements-coverage.txt` | Python dependencies of the coverage merge |

## Tools

Run by hand; none of these is a check.

| Script | Does |
|---|---|
| `lean_profile.py` | The costliest declarations and modules, from the build's profile (the `lean-profiling` skill) |
| `lean_closure.py` | What each module's imports cost CI, and what a change would save |
| `lit_imports.py` | Kernel checks that evaluate code without its literal, ranked by cost (the `proof-performance` skill) |
| `lean_shard_replay.py` | Compares shard planners on retained CI metrics |
| `trim_lean_imports.py` | Narrows the imports of many modules at once (the `lean-modules` skill) |
| `lean_import_build.py`, `lean_import_graph.py`, `lean_import_replay.py`, `lean_source_evidence.py`, `lean_module_uses.lean`, `stress_lean_imports.py` | The import planner behind `check_lean_public_imports.py --fix` and `trim_lean_imports.py` ([IMPORT_NARROWING.md](IMPORT_NARROWING.md)) |

`fixtures/` holds the unit tests' fixtures.
