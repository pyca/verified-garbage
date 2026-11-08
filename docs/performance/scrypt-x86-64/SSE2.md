# Baseline SSE2 Salsa20/8

This follow-up replaces the existing x86-64 BlockMix kernel with a packed
SSE2 implementation. It adds **no CPU variants, feature requirements, or
dispatch paths**. SSE2 is part of the x86-64 baseline. The existing PBKDF2
variants all use this same kernel.

The implementation and proofs are in `Impl/Scrypt/X86_64/Packed.lean` and
`Proof/Scrypt/X86_64/Packed*.lean`. Assembly and encoded Rust were generated
from Lean; neither was edited by hand. No TCB, specification, contract,
axiom, compiler override, or proof resource limit changed.

## Design and experiments

Four XMM registers hold all sixteen words in a diagonal layout:

| Register | Salsa word indices |
|---|---|
| xmm0 | 0, 5, 10, 15 |
| xmm1 | 4, 9, 14, 3 |
| xmm2 | 8, 13, 2, 7 |
| xmm3 | 12, 1, 6, 11 |

The state remains in these registers across all eight rounds and successive
Salsa invocations within BlockMix. Four other registers retain the input
for feed-forward addition. Input/output transposes use SSE2 unpack and
shuffle instructions. The GPRs hold the pointers and public loop count.
Scratch-memory stores only save the caller's callee-saved GPRs; there are
no state spills or scalar/vector conversions in the round loop.

Simply moving the old scalar spills into XMM registers was slower, as the
[earlier investigation](README.md) records. A first resident packed SSE2
prototype also failed to improve the large case consistently. Keeping the
state in registers alone was insufficient.

The successful schedule copies the older operand of each commutative sum
before its newest operand becomes available. It computes that sum twice,
allowing the left- and right-shift halves of the rotate to proceed
independently. Although this uses eight instructions per vector line rather
than seven, its shorter dependency chain performed better on this EPYC.
Register renaming exchanges the two row-round operands without extra moves.
The exploratory data are in `sse2-exploration.csv`; only SSE2 was retained. Its `baseline` is the original starting revision; `swap` copies the older operand and `duplicate` also duplicates the addition. The confirmation below uses the already optimized scalar revision instead.

## Measurement

These are isolated wall-clock measurements on the same AMD EPYC 9V74 KVM
host and toolchains documented in [environment.json](environment.json).
They are not the concurrent coverage CI timings. Each A/B pair alternates
order; seven samples per side were collected with no builds or tests running
alongside them. All samples, including outliers, are retained.

The baseline is `5127a0f77a`, including the already verified scalar schedule
and bulk wiping. Thus this comparison measures the additional SSE2 change,
not the earlier wiping improvement. The kernel probe copies the final
encoded machine bytes, rather than reassembling the text listing. Both
sides use the same driver. ROMix excludes allocation, initialization,
wiping, and freeing; the public API includes all of them. Kernel checksums
match for every pair. Phase probes also report each memory phase separately.

### Kernel medians

| Case | Scalar (ms) | SSE2 (ms) | Time reduction |
|---|---:|---:|---:|
| BlockMix, r=1, 500,000 calls | 54.389 | 45.985 | 15.5% |
| BlockMix, r=2, 500,000 calls | 108.329 | 91.468 | 15.6% |
| BlockMix, r=8, 500,000 calls | 395.347 | 344.934 | 12.8% |
| BlockMix, r=16, 500,000 calls | 830.797 | 716.859 | 13.7% |
| ROMix, N=16384, r=8 | 35.124 | 29.251 | 16.7% |
| ROMix, N=131072, r=8 | 280.373 | 238.364 | 15.0% |
| ROMix, N=1048576, r=8 | 2126.194 | 1944.627 | 8.5% |

### Optimized public API medians (N, r, p)

| Case | Scalar (ms) | SSE2 (ms) | Time reduction |
|---|---:|---:|---:|
| 1024, 1, 1 | 0.240 | 0.203 | 15.8% |
| 16384, 2, 1 | 7.808 | 6.956 | 10.9% |
| 16384, 16, 1 | 70.044 | 60.181 | 14.1% |
| 1024, 8, 16 | 26.482 | 23.827 | 10.0% |
| 16384, 8, 1 | 31.871 | 26.684 | 16.3% |
| 131072, 8, 1 | 283.238 | 274.174 | 3.2% |
| 1048576, 8, 1 | 2447.056 | 2204.033 | 9.9% |

### Unoptimized coverage public API medians (N, r, p)

| Case | Scalar (ms) | SSE2 (ms) | Time reduction |
|---|---:|---:|---:|
| 1024, 1, 1 | 0.255 | 0.231 | 9.3% |
| 16384, 2, 1 | 8.606 | 7.219 | 16.1% |
| 16384, 16, 1 | 74.036 | 66.032 | 10.8% |
| 1024, 8, 16 | 27.174 | 24.097 | 11.3% |
| 16384, 8, 1 | 35.242 | 30.277 | 14.1% |
| 131072, 8, 1 | 318.635 | 293.958 | 7.7% |
| 1048576, 8, 1 | 2458.298 | 2263.205 | 7.9% |

### Separating the 1 GiB memory phases

Medians from the optimized phase probe, in milliseconds. The public API is timed separately, so its median need not equal the sum of these medians.

| Phase | Scalar (ms) | SSE2 (ms) |
|---|---:|---:|
| Allocation and initialization | 244.928 | 243.310 |
| Derivation on preallocated buffers | 2065.476 | 1857.142 |
| Wiping | 39.768 | 39.088 |
| Freeing | 21.575 | 19.668 |

For 1 GiB ROMix, the mean paired time reduction is 8.9% (paired bootstrap 95% interval: 6.3–11.6%). For the optimized 1 GiB public API it is 10.6% (8.1–13.9%). These intervals describe this seven-pair VM run, not other CPUs or CI. The 128 MiB public API result is noisy: its mean paired interval includes zero. Bootstrap resampling uses 5,000 draws with seed 7914.

The full raw results are [sse2-kernels.csv](sse2-kernels.csv),
[sse2-phases.csv](sse2-phases.csv), and
[sse2-coverage-phases.csv](sse2-coverage-phases.csv).
The coverage comparison uses unoptimized Rust and `-Cinstrument-coverage`,
with the same default feature detection on both sides. It is isolated and
still cannot reproduce the original concurrent CI comparison.

## Verification and generation

- Full Lean build: 28,693 jobs passed after the final proof organization.
- Correctness, memory frames, ABI preservation, and constant-time proofs
  pass against the existing contracts.
- The RFC 7914 suite passed all eight tests with `VG_CPU_FEATURES=none`,
  `avx,avx2`, and `sha,avx,avx2`, including the 1 GiB vector.
- Rust formatting and clippy passed. The CI static checks and 630 Python
  tests passed; public-import analysis checked all 13 changed Lean modules.
- The official all-x86-64 emitter driver passed the standard-axiom,
  compiler-override, and specification-origin audits. Both changed generated
  files exactly match that driver's final output.

The existing emitter limitations described in [README.md](README.md) remain:
full `Emit.lean --check` exceeds this VM's mapping limit, and `EmitOne`'s copy
step reports two unrelated existing dispatcher-name parse failures. Its
underlying audited driver completes successfully. Full emitter validation
and multi-architecture CI are still required before merging.

## Reproduction

Build the original and candidate probes with `bench/tools/scrypt/build.py`
in separate output directories, preserving each checkout's generated bytes
and public API binary. Then run:

```sh
python3 bench/tools/scrypt/compare.py BASELINE_PROBE CANDIDATE_PROBE RESULTS \
  --samples 7 --baseline-wipe bulk --candidate-wipe bulk
```

Use `--baseline-wipe bulk` because this follow-up's baseline already contains
the bulk-wipe change. For coverage phase probes, build the manifests without
`--release` using `RUSTFLAGS=-Cinstrument-coverage` and run `compare.py` with
`--profile debug --phases-only`. The confirmation source/binary hashes are
recorded in [sse2-environment.json](sse2-environment.json).
