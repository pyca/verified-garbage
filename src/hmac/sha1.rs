//! HMAC-SHA-1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha1::{
    VG_HMAC_SHA1_FINALIZE_AVX_BMI_FEATURES, VG_HMAC_SHA1_INIT_AVX_BMI_FEATURES,
    vg_hmac_sha1_finalize_avx_bmi, vg_hmac_sha1_init_avx_bmi,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha1::{
    VG_HMAC_SHA1_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA1_INIT_SHA2_FEATURES,
    vg_hmac_sha1_finalize_sha2, vg_hmac_sha1_init_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::hmac_sha1::{
    VG_HMAC_SHA1_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA1_INIT_SHANI_FEATURES,
    vg_hmac_sha1_finalize_shani, vg_hmac_sha1_init_shani,
};
use crate::arch::hmac_sha1::{vg_hmac_sha1_finalize, vg_hmac_sha1_init};
use crate::hashes::sha1::{Sha1, Sha1Backend};

super::streaming_hmac!(
    Sha1 (Sha1Backend) {
        Scalar => (vg_hmac_sha1_init, vg_hmac_sha1_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA1_INIT_SHA2_FEATURES, VG_HMAC_SHA1_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha1_init_sha2, vg_hmac_sha1_finalize_sha2),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        ShaNi if [VG_HMAC_SHA1_INIT_SHANI_FEATURES, VG_HMAC_SHA1_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha1_init_shani, vg_hmac_sha1_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        AvxBmi if [VG_HMAC_SHA1_INIT_AVX_BMI_FEATURES, VG_HMAC_SHA1_FINALIZE_AVX_BMI_FEATURES] =>
            (vg_hmac_sha1_init_avx_bmi, vg_hmac_sha1_finalize_avx_bmi),
    },
    state: 84,
    output: 20,
);
