//! PBKDF2-HMAC-SHA-256 (RFC 8018 §5.2): one call of the verified
//! `vg_pbkdf2_hmac_sha256` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha256I`), which derives the whole key. Its variants, with the
//! same contract, are chosen on CPUs with the features their `_FEATURES`
//! constants name: on x86-64, `vg_pbkdf2_hmac_sha256_shani` and
//! `vg_pbkdf2_hmac_sha256_avx2`; on x86, `vg_pbkdf2_hmac_sha256_shani`; on
//! AArch64, `vg_pbkdf2_hmac_sha256_sha2`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_sha256::vg_pbkdf2_hmac_sha256;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha256::{VG_PBKDF2_HMAC_SHA256_AVX2_FEATURES, vg_pbkdf2_hmac_sha256_avx2};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha256::{VG_PBKDF2_HMAC_SHA256_SHA2_FEATURES, vg_pbkdf2_hmac_sha256_sha2};
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use crate::arch::pbkdf2_sha256::{
    VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES, vg_pbkdf2_hmac_sha256_shani,
};
use crate::hashes::sha256::{Sha256, Sha256Backend};

super::whole_pbkdf2!(
    Sha256 (Sha256Backend) {
        Scalar => vg_pbkdf2_hmac_sha256,
        #[cfg(target_arch = "aarch64")]
        Sha2 if [VG_PBKDF2_HMAC_SHA256_SHA2_FEATURES] =>
            vg_pbkdf2_hmac_sha256_sha2,
        #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
        ShaNi if [VG_PBKDF2_HMAC_SHA256_SHANI_FEATURES] => vg_pbkdf2_hmac_sha256_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA256_AVX2_FEATURES] => vg_pbkdf2_hmac_sha256_avx2,
    },
    output: 32,
);
