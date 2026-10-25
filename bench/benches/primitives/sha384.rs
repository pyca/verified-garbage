//! SHA-384.

use criterion::Criterion;

pub const USES: &[&str] = &["sha384", "sha512"];

/// `SIZES` and the short messages a TLS 1.3 handshake with
/// `TLS_AES_256_GCM_SHA384` hashes and MACs (the transcript's messages,
/// `HKDF-Expand-Label`'s inputs, a 48-byte digest): one block or two, around
/// the 111/112-byte boundary at which the padding takes a second block, up
/// to four blocks.
pub(crate) const SHA384_SIZES: [usize; 11] =
    [32, 48, 64, 100, 111, 112, 128, 256, 512, 1024, 16384];

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little")
))]
pub fn bench(c: &mut Criterion) {
    use openssl::hash::MessageDigest;
    use verified_garbage::hashes::sha384::Sha384;

    use crate::{hash_group_sizes, transcript_group};

    hash_group_sizes(
        c,
        "sha384",
        &SHA384_SIZES,
        Sha384::digest,
        MessageDigest::sha384(),
        Some(&aws_lc_rs::digest::SHA384),
    );
    transcript_group::<Sha384>(
        c,
        "sha384-transcript",
        MessageDigest::sha384(),
        &aws_lc_rs::digest::SHA384,
    );
}
