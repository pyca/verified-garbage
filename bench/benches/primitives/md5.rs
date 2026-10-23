//! MD5.

use criterion::Criterion;

pub const USES: &[&str] = &["md5"];

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
    use verified_garbage::hashes::md5::Md5;

    use crate::hash_group;

    hash_group(c, "md5", Md5::digest, MessageDigest::md5(), None);
}
