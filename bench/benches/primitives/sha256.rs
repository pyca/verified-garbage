//! SHA-256.

use criterion::Criterion;

pub const USES: &[&str] = &["sha256"];

/// `SIZES` and the short messages a TLS 1.3 handshake hashes (the
/// transcript's messages, `HKDF-Expand-Label`'s inputs): one block or two,
/// around the 55/56-byte boundary at which the padding takes a second block,
/// up to four blocks.
const SHA256_SIZES: [usize; 10] = [32, 55, 56, 64, 100, 128, 192, 256, 1024, 16384];

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
    use verified_garbage::hashes::sha256::Sha256;

    use crate::{hash_group_sizes, transcript_group};

    hash_group_sizes(
        c,
        "sha256",
        &SHA256_SIZES,
        Sha256::digest,
        MessageDigest::sha256(),
        Some(&aws_lc_rs::digest::SHA256),
    );
    transcript_group::<Sha256>(
        c,
        "sha256-transcript",
        MessageDigest::sha256(),
        &aws_lc_rs::digest::SHA256,
    );
}
