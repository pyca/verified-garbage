//! HMAC-SHA-256.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA256_INIT_AVX2_FEATURES,
    vg_hmac_sha256_finalize_avx2, vg_hmac_sha256_init_avx2,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA256_INIT_SHA2_FEATURES,
    vg_hmac_sha256_finalize_sha2, vg_hmac_sha256_init_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::hmac_sha256::{
    VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA256_INIT_SHANI_FEATURES,
    vg_hmac_sha256_finalize_shani, vg_hmac_sha256_init_shani,
};
use crate::arch::hmac_sha256::{vg_hmac_sha256_finalize, vg_hmac_sha256_init};
use crate::hashes::sha256::{Sha256, Sha256Backend};

super::streaming_hmac!(
    Sha256 (Sha256Backend) {
        Scalar => (vg_hmac_sha256_init, vg_hmac_sha256_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA256_INIT_SHA2_FEATURES, VG_HMAC_SHA256_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha256_init_sha2, vg_hmac_sha256_finalize_sha2),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        ShaNi if [VG_HMAC_SHA256_INIT_SHANI_FEATURES, VG_HMAC_SHA256_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha256_init_shani, vg_hmac_sha256_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA256_INIT_AVX2_FEATURES, VG_HMAC_SHA256_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha256_init_avx2, vg_hmac_sha256_finalize_avx2),
    },
    state: 96,
    output: 32,
);
