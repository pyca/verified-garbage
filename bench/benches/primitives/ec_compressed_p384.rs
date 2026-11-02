//! SEC 1 conversion over P-384: the benchmarks of `ec_compressed.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["ec_p384_compressed"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    crate::ec_compressed::ec_compressed_bench!(
        c,
        verified_garbage::ecdh::P384,
        "p384",
        48,
        SECP384R1
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}
