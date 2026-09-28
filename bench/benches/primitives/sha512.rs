//! SHA-512.

use criterion::Criterion;

pub const USES: &[&str] = &["sha512"];

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
