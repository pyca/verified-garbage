//! PBKDF2-HMAC-SHA-384.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::pbkdf2_sha384::vg_pbkdf2_hmac_sha384_auto;
use crate::hashes::sha384::Sha384;

super::whole_pbkdf2!(Sha384, pbkdf2: vg_pbkdf2_hmac_sha384_auto, output: 48);
