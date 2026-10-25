//! SHA-512.

use criterion::Criterion;

pub const USES: &[&str] = &["sha512"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha512::Sha512;

    use crate::hash_group;

    hash_group(
        c,
        "sha512",
        Sha512::digest,
        MessageDigest::sha512(),
        Some(&aws_lc_rs::digest::SHA512),
    );
}
