//! HMAC-SHA-224.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha224::{
    VG_HMAC_SHA224_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA224_INIT_AVX2_FEATURES,
    vg_hmac_sha224_finalize_avx2, vg_hmac_sha224_init_avx2,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha224::{
    VG_HMAC_SHA224_FINALIZE_SHA2_FEATURES, VG_HMAC_SHA224_INIT_SHA2_FEATURES,
    vg_hmac_sha224_finalize_sha2, vg_hmac_sha224_init_sha2,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::hmac_sha224::{
    VG_HMAC_SHA224_FINALIZE_SHANI_FEATURES, VG_HMAC_SHA224_INIT_SHANI_FEATURES,
    vg_hmac_sha224_finalize_shani, vg_hmac_sha224_init_shani,
};
use crate::arch::hmac_sha224::{vg_hmac_sha224_finalize, vg_hmac_sha224_init};
use crate::hashes::sha224::{Sha224, Sha224Backend};

super::streaming_hmac!(
    Sha224 (Sha224Backend) {
        Scalar => (vg_hmac_sha224_init, vg_hmac_sha224_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_HMAC_SHA224_INIT_SHA2_FEATURES, VG_HMAC_SHA224_FINALIZE_SHA2_FEATURES] =>
            (vg_hmac_sha224_init_sha2, vg_hmac_sha224_finalize_sha2),
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        ShaNi if [VG_HMAC_SHA224_INIT_SHANI_FEATURES, VG_HMAC_SHA224_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha224_init_shani, vg_hmac_sha224_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA224_INIT_AVX2_FEATURES, VG_HMAC_SHA224_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha224_init_avx2, vg_hmac_sha224_finalize_avx2),
    },
    state: 96,
    output: 28,
);
