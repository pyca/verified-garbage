//! PBKDF2-HMAC-SHA-1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_sha1::vg_pbkdf2_hmac_sha1;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha1::{VG_PBKDF2_HMAC_SHA1_AVX_BMI_FEATURES, vg_pbkdf2_hmac_sha1_avx_bmi};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha1::{VG_PBKDF2_HMAC_SHA1_SHA2_FEATURES, vg_pbkdf2_hmac_sha1_sha2};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::pbkdf2_sha1::{VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES, vg_pbkdf2_hmac_sha1_shani};
use crate::hashes::sha1::{Sha1, Sha1Backend};

super::whole_pbkdf2!(
    Sha1 (Sha1Backend) {
        Scalar => vg_pbkdf2_hmac_sha1,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA1_SHA2_FEATURES] =>
            vg_pbkdf2_hmac_sha1_sha2,
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        ShaNi if [VG_PBKDF2_HMAC_SHA1_SHANI_FEATURES] => vg_pbkdf2_hmac_sha1_shani,
        #[cfg(target_arch = "x86_64")]
        AvxBmi if [VG_PBKDF2_HMAC_SHA1_AVX_BMI_FEATURES] => vg_pbkdf2_hmac_sha1_avx_bmi,
    },
    output: 20,
);
