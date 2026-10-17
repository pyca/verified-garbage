//! SHA-256.

use criterion::Criterion;

pub const USES: &[&str] = &["sha256"];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha256::Sha256;

    use crate::hash_group;

    hash_group(
        c,
        "sha256",
        Sha256::digest,
        MessageDigest::sha256(),
        Some(&aws_lc_rs::digest::SHA256),
    );
}
