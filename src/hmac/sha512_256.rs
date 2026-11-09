//! HMAC-SHA-512/256.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha512_256::{
    vg_hmac_sha512_256_finalize_auto, vg_hmac_sha512_256_init_auto,
};
use crate::hashes::sha512_256::Sha512_256;

super::streaming_hmac!(
    Sha512_256,
    init: vg_hmac_sha512_256_init_auto,
    finalize: vg_hmac_sha512_256_finalize_auto,
    state: 192,
    output: 32,
);
