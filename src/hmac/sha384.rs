//! HMAC-SHA-384: `vg_hmac_sha384_init`, `vg_sha512_update` and
//! `vg_hmac_sha384_finalize` (contracts
//! `VG.Spec.Hmac.Instance.initAnyKeyContract` of `VG.Spec.Hmac.sha384I`,
//! `VG.Spec.Sha512.updateContract` and
//! `VG.Spec.Hmac.Instance.finalizeContract`) compute HMAC with a key of any
//! length, `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmac`),
//! keeping the two SHA-384 streaming states.
//!
//! Their variants, with the same contracts, run with the hash function's
//! backend of the same name, which `Sha384` chooses (see
//! `crate::hashes::sha384`): on x86-64, `vg_hmac_sha384_init_shani` and
//! `vg_hmac_sha384_finalize_shani`, then the `_avx2` ones; on AArch64, the
//! `_sha3` ones.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::hmac_sha384::{
    VG_HMAC_SHA384_FINALIZE_AVX2_FEATURES, VG_HMAC_SHA384_FINALIZE_SHANI_FEATURES,
    VG_HMAC_SHA384_INIT_AVX2_FEATURES, VG_HMAC_SHA384_INIT_SHANI_FEATURES,
    vg_hmac_sha384_finalize_avx2, vg_hmac_sha384_finalize_shani, vg_hmac_sha384_init_avx2,
    vg_hmac_sha384_init_shani,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::hmac_sha384::{
    VG_HMAC_SHA384_FINALIZE_SHA3_FEATURES, VG_HMAC_SHA384_INIT_SHA3_FEATURES,
    vg_hmac_sha384_finalize_sha3, vg_hmac_sha384_init_sha3,
};
use crate::arch::hmac_sha384::{vg_hmac_sha384_finalize, vg_hmac_sha384_init};
use crate::hashes::sha384::{Sha384, Sha384Backend};

super::streaming_hmac!(
    Sha384 (Sha384Backend) {
        Scalar => (vg_hmac_sha384_init, vg_hmac_sha384_finalize),
        #[cfg(target_arch = "aarch64")]
        Sha3 if [VG_HMAC_SHA384_INIT_SHA3_FEATURES, VG_HMAC_SHA384_FINALIZE_SHA3_FEATURES] =>
            (vg_hmac_sha384_init_sha3, vg_hmac_sha384_finalize_sha3),
        #[cfg(target_arch = "x86_64")]
        ShaNi if [VG_HMAC_SHA384_INIT_SHANI_FEATURES, VG_HMAC_SHA384_FINALIZE_SHANI_FEATURES] =>
            (vg_hmac_sha384_init_shani, vg_hmac_sha384_finalize_shani),
        #[cfg(target_arch = "x86_64")]
        Avx2 if [VG_HMAC_SHA384_INIT_AVX2_FEATURES, VG_HMAC_SHA384_FINALIZE_AVX2_FEATURES] =>
            (vg_hmac_sha384_init_avx2, vg_hmac_sha384_finalize_avx2),
    },
    state: 192,
    output: 48,
);
