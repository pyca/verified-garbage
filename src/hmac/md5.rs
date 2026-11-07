//! HMAC-MD5.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::hmac_md5::{vg_hmac_md5_finalize_auto, vg_hmac_md5_init_auto};
use crate::hashes::md5::Md5;

super::streaming_hmac!(
    Md5,
    init: vg_hmac_md5_init_auto,
    finalize: vg_hmac_md5_finalize_auto,
    state: 80,
    output: 16,
);
