//! HMAC-SHA-224: `vg_hmac_sha224_init`, `vg_sha256_update` and
//! `vg_hmac_sha224_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initAnyKeyContract` of `VG.Spec.Hmac.sha224I`,
//! `VG.Spec.Sha256.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute HMAC with a key of any
//! length, `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmac`),
//! keeping the two SHA-224 streaming states (SHA-256's, from SHA-224's initial
//! hash value).
//!
//! Their variants, with the same contracts, run with the hash function's
//! backend of the same name, which `Sha224` chooses (see
//! `crate::hashes::sha224`): on x86 and x86-64, `vg_hmac_sha224_init_shani` and
//! `vg_hmac_sha224_finalize_shani`, on x86-64 the `_avx2` ones; on AArch64, the
//! `_sha2` ones.

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
