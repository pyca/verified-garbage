# x86-64 scrypt investigation, 2026-11-08

The clearest improvement is batching the Rust destructor's wipes: for the
1 GiB case, the isolated, unoptimized coverage build's median public API time
fell from **2.691 s to 2.490 s (7.5%)**. Its measured wipe phase fell from
199.1 ms to 42.3 ms. This is a test-build result, not a production speedup.
Optimized end-to-end results are noisy and do not establish an improvement.

The retained scalar instruction schedule was independently checked against
the existing proofs and reduced median isolated 1 GiB ROMix time by about
2.1% in the confirmation run. The initial standalone BlockMix gain was not
confirmed; no universal native speedup is claimed.
The SIMD bridges and the other spill experiments were rejected.

This does **not** explain the reported 8.072 s x86-64 versus 3.449 s AArch64
CI result. That test runs concurrently with other tests, includes allocation
and wiping, and uses coverage and unoptimized Rust. No AArch64 measurements
were made here. The matched CPU model does not make this VM the CI runner.

## Revisions, hardware, and measurement

- Starting revision: `558496859f64a2d3e32cd38416cdd3cf2a083cc5`.
- Scalar scheduling experiment: `aefcbf1131`.
- Scheduling plus bulk wiping: `8dc7ecc32d`.
- Linux x86-64 KVM VM; AMD EPYC 9V74, five exposed vCPUs. One workload
  thread, one benchmark process at a time; no builds or tests alongside the
  reported final timings. No affinity or frequency changes.
- Rust 1.99.1, Lean 4.35.0. Exact compiler, kernel, CPU details and source
  hashes: [environment.json](environment.json).
- Native phase builds: Cargo release, optimization level 3, no coverage or
  LTO. Kernel driver: `cc -O3`; the timed kernels are opaque assembly.
- Coverage comparison: Cargo dev, optimization level 0,
  `RUSTFLAGS=-Cinstrument-coverage`. Default detected CPU features; the
  derivation selects SHA-NI, and the wipe selects AVX on this host.

The initial repeated baselines preceded source changes. Baseline binaries
were preserved. Initial raw phase data are [initial-phases.csv](initial-phases.csv)
and [initial-coverage-phases.csv](initial-coverage-phases.csv); the initial
text-assembly kernel baselines are `initial-blockmix.csv` and `initial-romix.csv`. Final native kernels have seven samples per side; the
public API/phase comparison has five per side per case and three arms
(original, scheduling only, combined). Coverage has seven samples per side.
A/B order alternates, or rotates for the three-arm runs. The additional
native confirmation uses randomized pair order and twenty samples per side.
All samples, including outliers and regressions, are retained.

The kernel probe decodes the generated Rust crate's `.base64` instructions
verbatim; it does not benchmark a C reimplementation or rely on the text
assembler choosing the same instruction encodings. Existing branches,
symbols, and 64-byte function alignment are retained. Allocation, table
initialization, and destruction are outside its clock. BlockMix alternates
separate input/output buffers; ROMix starts with a deterministic block and
an allocated, initialized table. Output checksums agree between sides.

The phase probe allocates the same aligned chunk layout as the library,
calls the generated public whole-derivation dispatcher, times wiping and
freeing separately, then times another call through the actual public API.
The derived keys agree inside every invocation. Consequently the public API
and phase columns describe **different calls**: allocator/cache state can
make their times differ, and medians must not be summed. Password is
`password`, salt `NaCl`, output 64 bytes. The phase harness is a diagnostic,
not an added public or internal cryptographic API. Snapshots of the measured
drivers are [phases-measured.rs.txt](phases-measured.rs.txt) and
[kernel-measured.c.txt](kernel-measured.c.txt). The shipping probe adds
argument validation and explicitly mirrors the compiler fences; no timing
claims use its smoke-test run.

## Profile and phases

A 128 MiB ROMix profile (`N=131072,r=8`, forty calls, 100 Hz `gprof` samples)
placed approximately **84.6% in BlockMix and 15.5% in ROMix's surrounding
code**: [profile.txt](profile.txt). This attributes time to functions,
including BlockMix's XOR/feed-forward and bookkeeping; it does not attribute
84.6% specifically to spills. The initial profile used the unchanged Lean
text printer output; final kernel timings use the encoded bytes instead.
Hardware counters and instruction counts were not measured.

For `N=1048576,r=8,p=1`, native baseline phase medians in milliseconds were:

| Allocation + initialization | Derivation | Wiping | Freeing | Separate public API call |
|---:|---:|---:|---:|---:|
| 241.3 | 2062.8 | 40.7 | 22.5 | 2393.4 |

The release build's derivation dominates. In the coverage build the baseline
wipe alone costs 199.1 ms. The previous destructor calls `zeroize_raw` via a
slice helper once per 128-byte chunk: **8,388,640 calls** for this case,
including `b` and scratch. The new destructor makes **three** calls, one per
contiguous vector. Each still uses the verified dispatcher and compiler
fence; all buffer bytes are wiped before deallocation.

The library still allocates three vectors with the same lengths and
alignment. Its memory accounting, initialization, parameters, derivation,
CPU dispatch, output, and wiping guarantee are unchanged. No allocation or
memory-footprint reduction is claimed.

## Native measurements

The first interleaved kernel comparison, original versus scheduling only,
reports medians. These are descriptive results; the overlapping samples
motivated the separate confirmation rather than a claim based on the screen.

| Operation | Baseline (ms) | Scheduling (ms) | Median time reduction |
|---|---:|---:|---:|
| BlockMix, r=1, 500,000 calls | 50.596 | 50.973 | -0.74% |
| BlockMix, r=2, 500,000 calls | 100.737 | 98.282 | 2.44% |
| BlockMix, r=8, 500,000 calls | 409.609 | 394.200 | 3.76% |
| BlockMix, r=16, 500,000 calls | 763.038 | 765.073 | -0.27% |
| ROMix, N=16384, r=8 | 29.087 | 28.345 | 2.55% |
| ROMix, N=131072, r=8 | 249.927 | 244.965 | 1.99% |
| ROMix, N=1048576, r=8 | 2070.142 | 2045.388 | 1.20% |

The optimized public API results, original versus combined, remain
**inconclusive**. Each cell gives median [minimum, maximum], milliseconds;
this includes allocation, initialization, derivation, wiping and freeing.

| N, r, p | Baseline (ms) | Combined (ms) |
|---|---:|---:|
| 1024, 1, 1 | 0.23 [0.21, 0.34] | 0.21 [0.21, 0.25] |
| 16384, 2, 1 | 7.90 [7.59, 8.77] | 8.10 [7.59, 9.06] |
| 16384, 16, 1 | 73.87 [64.41, 89.09] | 70.96 [68.88, 80.74] |
| 1024, 8, 16 | 25.93 [25.12, 28.54] | 26.36 [25.17, 26.92] |
| 16384, 8, 1 | 31.71 [31.12, 36.25] | 32.04 [30.39, 33.65] |
| 131072, 8, 1 | 286.91 [275.95, 344.93] | 288.78 [274.69, 310.02] |
| 1048576, 8, 1 | 2393.36 [2303.65, 2427.05] | 2379.14 [2324.95, 2461.48] |

Raw data: [final-kernels.csv](final-kernels.csv),
[final-phases.csv](final-phases.csv). The latter includes the intermediate
scheduling-only build as well.

A separate confirmation used twenty randomized A/B pairs for `r=8` BlockMix
and 1 GiB ROMix, with no concurrent work. BlockMix was
385.825 → 384.301 ms per 500,000 calls;
**the earlier 3.8% BlockMix estimate did not hold up**. Its paired bootstrap
interval includes zero. Large ROMix was
2.137230 → 2.091534 s, a **2.14% median reduction**.
The mean paired percentage reduction was 2.26%
(approximate 95% paired bootstrap interval 0.58% to 4.00%).
The small, eight-line scheduling change is retained for that modest large-ROMix
result, not as an established standalone BlockMix or universal speedup.
No mechanism beyond the changed instruction order was established.

Data: [confirm-kernels.csv](confirm-kernels.csv),
[confirmation-summary.json](confirmation-summary.json). The latter records
10,000 pair resamples and seed 7914. These sampling intervals do not account
for every possible VM/host systematic effect.

## Unoptimized coverage comparison

Median public API elapsed times, original versus combined:

| N, r, p | Baseline (ms) | Combined (ms) | Median time reduction |
|---|---:|---:|---:|
| 1024, 8, 16 | 28.063 | 26.613 | 5.17% |
| 16384, 8, 1 | 38.125 | 34.666 | 9.07% |
| 1048576, 8, 1 | 2691.344 | 2489.698 | 7.49% |

The 1 GiB wipe phase is 199.1 → 42.3 ms, a 78.7% elapsed-time reduction.
This phase result explains much of the local coverage-build improvement;
it does not turn concurrent CI elapsed times into an isolated benchmark.
Raw data: [final-coverage.csv](final-coverage.csv).

## Rejected experiments and limits

Exploratory trials used only Lean-defined code and the Lean printer, never
hand-edited generated crates. They were benchmark prototypes, not new
registered/verified artifacts. Checksum agreement was a screening check,
not a substitute for proofs. None of their unverified code is retained.

| Experiment | Observation and decision |
|---|---|
| SSE2 four-lane Salsa rounds with the scalar interface | About 0.50 s versus 0.39 s for 500,000 `r=8` BlockMix calls; conversion and serialized SIMD work outweighed the reduction in scalar instructions. Rejected. |
| Four spilled words cached in SSE registers | About 0.63 s versus 0.39 s; GPR/SSE transfers and extra instructions regressed. Rejected. |
| Thirteen scalar register words, saving the output pointer across rounds | No clear gain. Rejected. |
| Move spills to diagonal words, exchanging state at the round boundaries | No clear gain after conversion cost. Rejected. |
| Reuse `eax` after scratch stores, with sequential or hybrid schedules | Fewer reloads but slower trials. Rejected. |
| AVX-512VL packed rotations with the scalar interface | Still slower in the bridge trial. A fully SIMD-resident BlockMix is not ruled out by this result. Rejected as implemented. |
| Four-way unrolled ROMix copy/XOR loops | Roughly 2% in an exploratory 128 MiB trial, with overlapping results; insufficient benefit to justify new loop proofs. Rejected. |
| Scalar schedules | 125 dependency-preserving schedules screened once; six checked again. Only the small wave-order change advanced to encoded-byte confirmation. |

Raw exploratory data are the `*-trial.csv` files,
[schedule-screen.csv](schedule-screen.csv) and
[schedule-finalists.csv](schedule-finalists.csv). Trials have three samples
per side in each of two A/B rounds. The screening data do not establish a
speedup. Reducing spill count did not reliably improve this host. A complete
SIMD-resident implementation would need its own measurements, proofs and
proper propagation through all scrypt/PBKDF2 backend combinations.

## Correctness and generation

- `lake build --log-level=warning`: passed, 28,685 jobs, including golden
  tests and the existing correctness, memory-safety, ABI, and leakage proofs.
- All eight RFC 7914 tests passed with feature sets `none`, `avx,avx2`,
  and `sha`; the last RFC vector allocates 1 GiB. Release RFC tests also
  passed. The zeroize unit test passed.
- Formatting, Clippy with warnings denied, public-import checks, and every
  static-check job command passed, including the CI Python unit tests.
- No `TCB/`, `Spec/`, contracts, axioms, or proof resource limits changed.

Assembly was regenerated from Lean. The x86-64 emitter driver passed its
standard-axiom, compiler-override and specification-origin audits, and both
changed BlockMix files exactly match its output. Full `Emit.lean --check`
could not run: this VM has `vm.max_map_count=65530` and no `sudo` with which
to raise it. The supported all-x86-64 `EmitOne` run generated the files but
returned nonzero on two pre-existing, unrelated dispatcher-name parsing
failures (`dispatch/fn_tables.rs`, `dispatch/gcm.rs`); it left those files
unchanged. No checker or trusted code was modified to bypass either issue.
A normal full emitter check and the multi-architecture CI remain necessary
before merging. See [validation.txt](validation.txt) for the local check results.

## Reproduction

Use a normal x86-64 development environment with the repository toolchains
and a C compiler. From this checkout:

```sh
git worktree add /tmp/scrypt-base 558496859f64a2d3e32cd38416cdd3cf2a083cc5
python3 bench/tools/scrypt/build.py /tmp/scrypt-base /tmp/scrypt-base-probe
python3 bench/tools/scrypt/build.py "$PWD" /tmp/scrypt-new-probe
python3 bench/tools/scrypt/compare.py /tmp/scrypt-base-probe /tmp/scrypt-new-probe \
  /tmp/scrypt-results --samples 7
```

Do not build or run other tests alongside timings. `metadata.json` in each
probe directory records its checkout, dirty files, compiler and CPU. To
compare just the scalar schedule, build its revision and use
`--candidate-wipe chunks`. The checked-in raw data preserve that intermediate
comparison even if it is subsequently rejected.

For the dev/coverage context, build both generated manifests without release
optimization, then run just the phase comparison:

```sh
RUSTFLAGS=-Cinstrument-coverage cargo build --manifest-path /tmp/scrypt-base-probe/Cargo.toml
RUSTFLAGS=-Cinstrument-coverage cargo build --manifest-path /tmp/scrypt-new-probe/Cargo.toml
python3 bench/tools/scrypt/compare.py /tmp/scrypt-base-probe /tmp/scrypt-new-probe \
  /tmp/scrypt-coverage-results --profile debug --phases-only --samples 7
```

The production throughput benchmarks also remain available in
`bench/benches/primitives/scrypt.rs`. No GitHub benchmark workflow or PR was
published by this investigation.
