//! RSASSA-PSS on AArch64, where each hash function has its own verified
//! functions, with MGF1 over the same hash function: a module per hash
//! function (on x86-64, `vg_rsa_pss_sign` and `vg_rsa_pss_verify_precomputed`
//! take the hash functions as arguments: `super::any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

pub(super) mod md5;
pub(super) mod sha1;
pub(super) mod sha224;
pub(super) mod sha256;
pub(super) mod sha384;
pub(super) mod sha512;
pub(super) mod sha512_224;
pub(super) mod sha512_256;
