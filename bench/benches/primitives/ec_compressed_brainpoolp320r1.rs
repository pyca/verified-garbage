//! SEC 1 conversion over brainpoolP320r1: the benchmarks of `ec_compressed.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["ec_brainpoolp320r1_compressed"];

#[cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    crate::ec_compressed::ec_compressed_bench!(
        c,
        verified_garbage::ec::BrainpoolP320r1,
        "brainpoolp320r1",
        40,
        BRAINPOOL_P320R1
    );
}

#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
