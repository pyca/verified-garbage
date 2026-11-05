//! HMAC-MD5.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::hmac_md5::{vg_hmac_md5_finalize, vg_hmac_md5_init};
use crate::hashes::md5::{Md5, Md5Backend};

super::streaming_hmac!(
    Md5 (Md5Backend) {
        Scalar => (vg_hmac_md5_init, vg_hmac_md5_finalize),
    },
    state: 80,
    output: 16,
);
