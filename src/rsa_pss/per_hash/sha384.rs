//! RSASSA-PSS with SHA-384 and MGF1 with SHA-384:
//! `vg_rsa_pss_sha384_mgf1_sha384_sign` and `vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha384`), for each
//! implementation of SHA-384's compression function that `Sha384` runs and,
//! of the RSA operation, on AArch64 (on x86-64, `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` take the hash functions as arguments:
//! `any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_pss_sha384_mgf1_sha384::{
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHA3_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHA3_FEATURES,
    vg_rsa_pss_sha384_mgf1_sha384_sign, vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_sha3,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_sha3,
};
use crate::hashes::sha384::Sha384Backend;

super::super::pss_hash!(48, Sha384Backend {
    Scalar => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed [],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign [],
    },
    Sha3 => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_sha3 [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHA3_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_sha3 [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHA3_FEATURES],
    },
});
