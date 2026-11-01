//! ML-KEM-768: the benchmarks of `mlkem.rs`.

use criterion::Criterion;

pub const USES: &[&str] = &["mlkem768", "mlkem_common", "mlkem", "sha3"];

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    crate::mlkem::mlkem_bench!(
        c,
        verified_garbage::mlkem768,
        DecapsulationKey768,
        EncapsulationKey768,
        ML_KEM_768,
        ML_KEM_768
    );
}

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}
