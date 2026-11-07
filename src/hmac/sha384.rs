//! HMAC-SHA-384.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha384::{vg_hmac_sha384_finalize_auto, vg_hmac_sha384_init_auto};
use crate::hashes::sha384::Sha384;

super::streaming_hmac!(
    Sha384,
    init: vg_hmac_sha384_init_auto,
    finalize: vg_hmac_sha384_finalize_auto,
    state: 192,
    output: 48,
);
