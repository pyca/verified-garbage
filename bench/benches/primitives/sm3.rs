//! SM3.
//!
//! aws-lc-rs has no SM3, so there is nothing of its to compare with.

use criterion::Criterion;

pub const USES: &[&str] = &["sm3"];

#[cfg(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sm3::Sm3;

    crate::hash_group(c, "sm3", Sm3::digest, MessageDigest::sm3(), None);
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm")))]
pub fn bench(_: &mut Criterion) {}
