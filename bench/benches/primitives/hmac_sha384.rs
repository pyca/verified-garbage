//! HMAC-SHA-384.

use criterion::Criterion;

pub const USES: &[&str] = &["hmac_sha384", "sha384", "sha512"];

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
    use verified_garbage::hashes::sha384::Sha384;
    use verified_garbage::hmac::Hmac;

    crate::hmac_group_sizes(
        c,
        "hmac-sha384",
        &crate::sha384::SHA384_SIZES,
        Hmac::<Sha384>::mac,
        MessageDigest::sha384(),
        Some(aws_lc_rs::hmac::HMAC_SHA384),
    );
    crate::hmac_verify_group::<Sha384>(
        c,
        "hmac-sha384-verify",
        MessageDigest::sha384(),
        Some(aws_lc_rs::hmac::HMAC_SHA384),
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
