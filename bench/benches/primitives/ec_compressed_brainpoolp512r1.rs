//! SEC 1 conversion over brainpoolP512r1: the benchmarks of `ec_compressed.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["ec_brainpoolp512r1_compressed"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    crate::ec_compressed::ec_compressed_bench!(
        c,
        verified_garbage::ecdh::BrainpoolP512r1,
        "brainpoolp512r1",
        64,
        BRAINPOOL_P512R1
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
