//! PBKDF2-HMAC-SHA-1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1_auto;
use crate::hashes::sha1::Sha1;

super::whole_pbkdf2!(Sha1, pbkdf2: vg_pbkdf2_hmac_sha1_auto, output: 20);
