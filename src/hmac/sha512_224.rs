//! HMAC-SHA-512/224.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha512_224::{
    vg_hmac_sha512_224_finalize_auto, vg_hmac_sha512_224_init_auto,
};
use crate::hashes::sha512_224::Sha512_224;

super::streaming_hmac!(
    Sha512_224,
    init: vg_hmac_sha512_224_init_auto,
    finalize: vg_hmac_sha512_224_finalize_auto,
    state: 192,
    output: 28,
);
