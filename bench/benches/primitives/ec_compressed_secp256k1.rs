//! SEC 1 conversion over secp256k1: the benchmarks of `ec_compressed.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["ec_secp256k1_compressed"];

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
        verified_garbage::ecdh::Secp256k1,
        "secp256k1",
        32,
        SECP256K1
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
