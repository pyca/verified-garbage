//! PBKDF2-HMAC-SHA-224.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_sha224::vg_pbkdf2_hmac_sha224;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha224::{VG_PBKDF2_HMAC_SHA224_AVX2_FEATURES, vg_pbkdf2_hmac_sha224_avx2};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha224::{VG_PBKDF2_HMAC_SHA224_SHA2_FEATURES, vg_pbkdf2_hmac_sha224_sha2};
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use crate::arch::pbkdf2_sha224::{
    VG_PBKDF2_HMAC_SHA224_SHANI_FEATURES, vg_pbkdf2_hmac_sha224_shani,
};
use crate::hashes::sha224::{Sha224, Sha224Backend};

super::whole_pbkdf2!(
    Sha224 (Sha224Backend) {
        Scalar => vg_pbkdf2_hmac_sha224,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA224_SHA2_FEATURES] => vg_pbkdf2_hmac_sha224_sha2,
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        ShaNi if [VG_PBKDF2_HMAC_SHA224_SHANI_FEATURES] => vg_pbkdf2_hmac_sha224_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA224_AVX2_FEATURES] => vg_pbkdf2_hmac_sha224_avx2,
    },
    output: 28,
);
