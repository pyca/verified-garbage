//! PBKDF2-HMAC-SHA-224.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::pbkdf2_sha224::vg_pbkdf2_hmac_sha224_auto;
use crate::hashes::sha224::Sha224;

super::whole_pbkdf2!(Sha224, pbkdf2: vg_pbkdf2_hmac_sha224_auto, output: 28);
