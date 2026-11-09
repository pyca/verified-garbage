//! HMAC-SHA-1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_sha1::{vg_hmac_sha1_finalize_auto, vg_hmac_sha1_init_auto};
use crate::hashes::sha1::Sha1;

super::streaming_hmac!(
    Sha1,
    init: vg_hmac_sha1_init_auto,
    finalize: vg_hmac_sha1_finalize_auto,
    state: 84,
    output: 20,
);
