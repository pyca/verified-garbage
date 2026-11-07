//! HMAC-SHA-224.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha224::{vg_hmac_sha224_finalize_auto, vg_hmac_sha224_init_auto};
use crate::hashes::sha224::Sha224;

super::streaming_hmac!(
    Sha224,
    init: vg_hmac_sha224_init_auto,
    finalize: vg_hmac_sha224_finalize_auto,
    state: 96,
    output: 28,
);
