//! RSASSA-PSS with SHA-1 and MGF1 with SHA-1:
//! `vg_rsa_pss_sha1_mgf1_sha1_sign` and `vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha1`), for each
//! implementation of SHA-1's compression function that `Sha1` runs, on AArch64
//! and ARMv7.

#![cfg(all(any(target_arch = "aarch64", target_arch = "arm"), feature = "alloc"))]

#[cfg(target_arch = "aarch64")]
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHA2_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHA2_FEATURES,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_sha2,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_sha2,
};
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    vg_rsa_pss_sha1_mgf1_sha1_sign, vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed,
};
use crate::hashes::sha1::Sha1Backend;

super::pss_hash!(20, Sha1Backend {
    Scalar => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed [],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign [],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_sha2 [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHA2_FEATURES],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_sha2 [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHA2_FEATURES],
    },
});
