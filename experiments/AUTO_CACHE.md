# Unproved ML-DSA automatic cache experiment

This branch is for native timing/correctness experiments, not a production PR.
New prepared entry points have not been proved. Do not ship them as verified.
The unchanged public key APIs promote independently on their second use under
`alloc` on AArch64; without allocation they retain the ordinary path.
`VG_MLDSA_CACHE_AFTER` is a **compile-time** experiment control (0,1,2,4).
One atomic claim initializes each key's immutable cache; concurrent callers
fall back instead of waiting. Failed initialization permanently falls back.
Caches do not affect equality; clones start cold. Secret caches wipe on drop.

All assembly is emitted from real Lean programs and the trusted printer.
`AutoCachePrototype.lean` checks reconstruction of the ordinary raw and message
functions byte-for-byte, preserves them, and appends prepared functions.
New symbols deliberately do not claim a `Verified` proof or an Artifact.
It duplicates the arithmetic bodies; production should consider sharing those
bodies. This branch's extra emitted code is not a final code-size commitment.

Reproduce from the baseline `3d37034d64a308e5d18de2908d95013cdef5e943`:

1. Create a temporary baseline directory. For `mldsa_common`, `mldsa44`,
   `mldsa65`, `mldsa87`, save `git show BASE:src/NAME.rs` as
   `original-NAME.rs`. For each parameter set, save
   `git show BASE:src/asm/aarch64/mldsaNN.rs` as `baseline-mldsaNN.rs`.
2. With matching Lean dependencies/cache restored, from `lean/`, run
   `lake env lean --run ../experiments/AutoCachePrototype.lean /absolute/baseline /absolute/checkout/src/asm/aarch64`.
3. Run `python3 experiments/auto-rust.py /absolute/baseline /absolute/checkout`.
   Format the edited Rust API files (never format/edit generated assembly).
4. Run the ML-DSA tests in detected and forced-scalar modes, with the published
   Wycheproof checkout available. The modified vector harness repeats each case
   across promotion. The Rust unit tests exercise publication, failure, panic,
   concurrent readers and zeroization observed immediately before deallocation.
5. `VG_MLDSA_CACHE_AFTER=2 cargo build --release --features cpu-features-env --example mldsa-cache-lifetime`.
   Copy the executable out before rebuilding for another policy. For baseline,
   restore the four original Rust API source files, leaving the identical
   measurement harness and unused generated prepared functions in place.
6. Run binaries sequentially and interleave their order; never time during
   builds. The CSV reports median microseconds per complete key lifetime over
   16 samples, with 128 or more operations per sample, across 32 fixed keys.
   Creation and drop are included. Concurrent rows use four shared-key threads
   and report elapsed time divided by total operations, not single-call latency.

Raw measurements belong outside the repository. The existing benchmark workflow invokes this branch's measurement driver
through a guarded branch-only entry in `ci/bench_compare.py`: one native
AArch64 job, three interleaved passes, only these ML-DSA lifetime workloads.
Its workflow definition is unchanged; request modules `mldsa44 mldsa65 mldsa87`,
architecture `aarch64`, and the unrestricted default CPU-feature configuration.
No unrestricted algorithm/architecture benchmark run is needed.
