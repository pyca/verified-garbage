//! PBKDF2-HMAC-MD5.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::pbkdf2_md5::vg_pbkdf2_hmac_md5_auto;
use crate::hashes::md5::Md5;

super::whole_pbkdf2!(Md5, pbkdf2: vg_pbkdf2_hmac_md5_auto, output: 16);
