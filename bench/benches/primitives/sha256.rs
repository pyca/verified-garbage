//! SHA-256.

use criterion::Criterion;
use openssl::hash::MessageDigest;
use verified_garbage::hashes::sha256::Sha256;

use crate::hash_group_sizes;

pub const USES: &[&str] = &["sha256"];

/// `SIZES` and the short messages a TLS 1.3 handshake hashes (the
/// transcript's messages, `HKDF-Expand-Label`'s inputs): one block or two,
/// around the 55/56-byte boundary at which the padding takes a second block,
/// up to four blocks.
const SHA256_SIZES: [usize; 10] = [32, 55, 56, 64, 100, 128, 192, 256, 1024, 16384];

pub fn bench(c: &mut Criterion) {
    hash_group_sizes(
        c,
        "sha256",
        &SHA256_SIZES,
        Sha256::digest,
        MessageDigest::sha256(),
        Some(&aws_lc_rs::digest::SHA256),
    );
}
