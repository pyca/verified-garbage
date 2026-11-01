//! PBKDF2-HMAC-SHA-384 (RFC 8018 §5.2): one call of the verified
//! `vg_pbkdf2_hmac_sha384` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract` of
//! `VG.Spec.Hmac.sha384I`), which derives the whole key. Its variants, with the
//! same contract, are chosen on CPUs with the features their `_FEATURES`
//! constants name: on x86-64, `vg_pbkdf2_hmac_sha384_shani` and
//! `vg_pbkdf2_hmac_sha384_avx2`; on AArch64, `vg_pbkdf2_hmac_sha384_sha3`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_sha384::vg_pbkdf2_hmac_sha384;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha384::{
    VG_PBKDF2_HMAC_SHA384_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA384_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha384_avx2, vg_pbkdf2_hmac_sha384_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha384::{VG_PBKDF2_HMAC_SHA384_SHA3_FEATURES, vg_pbkdf2_hmac_sha384_sha3};
use crate::hashes::sha384::{Sha384, Sha384Backend};

super::whole_pbkdf2!(
    Sha384 (Sha384Backend) {
        Scalar => vg_pbkdf2_hmac_sha384,
        #[cfg(target_arch = "aarch64")]
        Sha3 if [VG_PBKDF2_HMAC_SHA384_SHA3_FEATURES] => vg_pbkdf2_hmac_sha384_sha3,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA384_SHANI_FEATURES] => vg_pbkdf2_hmac_sha384_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA384_AVX2_FEATURES] => vg_pbkdf2_hmac_sha384_avx2,
    },
    output: 48,
);
