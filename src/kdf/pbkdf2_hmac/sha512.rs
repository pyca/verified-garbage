//! PBKDF2-HMAC-SHA-512.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::pbkdf2_sha512::vg_pbkdf2_hmac_sha512_auto;
use crate::hashes::sha512::Sha512;

super::whole_pbkdf2!(Sha512, pbkdf2: vg_pbkdf2_hmac_sha512_auto, output: 64);
