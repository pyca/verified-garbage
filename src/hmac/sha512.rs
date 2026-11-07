//! HMAC-SHA-512.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha512::{vg_hmac_sha512_finalize_auto, vg_hmac_sha512_init_auto};
use crate::hashes::sha512::Sha512;

super::streaming_hmac!(
    Sha512,
    init: vg_hmac_sha512_init_auto,
    finalize: vg_hmac_sha512_finalize_auto,
    state: 192,
    output: 64,
);
