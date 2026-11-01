//! PBKDF2-HMAC-SHA-512/224 (RFC 8018 §5.2): one call of the verified
//! `vg_pbkdf2_hmac_sha512_224` (contract `VG.Spec.Hmac.Instance.pbkdf2Contract`
//! of `VG.Spec.Hmac.sha512_224I`), which derives the whole key. Its variants,
//! with the same contract, are chosen on CPUs with the features their
//! `_FEATURES` constants name: on x86-64, `vg_pbkdf2_hmac_sha512_224_shani` and
//! `vg_pbkdf2_hmac_sha512_224_avx2`; on AArch64,
//! `vg_pbkdf2_hmac_sha512_224_sha3`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::pbkdf2_sha512_224::vg_pbkdf2_hmac_sha512_224;
#[cfg(target_arch = "x86_64")]
use crate::arch::pbkdf2_sha512_224::{
    VG_PBKDF2_HMAC_SHA512_224_AVX2_FEATURES, VG_PBKDF2_HMAC_SHA512_224_SHANI_FEATURES,
    vg_pbkdf2_hmac_sha512_224_avx2, vg_pbkdf2_hmac_sha512_224_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::pbkdf2_sha512_224::{
    VG_PBKDF2_HMAC_SHA512_224_SHA3_FEATURES, vg_pbkdf2_hmac_sha512_224_sha3,
};
use crate::hashes::sha512_224::{Sha512_224, Sha512_224Backend};

super::whole_pbkdf2!(
    Sha512_224 (Sha512_224Backend) {
        Scalar => vg_pbkdf2_hmac_sha512_224,
        #[cfg(target_arch = "aarch64")]
        Sha3 if [VG_PBKDF2_HMAC_SHA512_224_SHA3_FEATURES] => vg_pbkdf2_hmac_sha512_224_sha3,
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_PBKDF2_HMAC_SHA512_224_SHANI_FEATURES] => vg_pbkdf2_hmac_sha512_224_shani,
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_PBKDF2_HMAC_SHA512_224_AVX2_FEATURES] => vg_pbkdf2_hmac_sha512_224_avx2,
    },
    output: 28,
);
