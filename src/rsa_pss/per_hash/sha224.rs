//! RSASSA-PSS with SHA-224 and MGF1 with SHA-224:
//! `vg_rsa_pss_sha224_mgf1_sha224_sign` and `vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha224`), for each
//! implementation of SHA-224's compression function that `Sha224` runs and,
//! of the RSA operation, on AArch64 (on x86-64, `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` take the hash functions as arguments:
//! `any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_pss_sha224_mgf1_sha224::{
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHA2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHA2_FEATURES,
    vg_rsa_pss_sha224_mgf1_sha224_sign, vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_sha2,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_sha2,
};
use crate::hashes::sha224::Sha224Backend;

super::super::pss_hash!(28, Sha224Backend {
    Scalar => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed [],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign [],
    },
    Sha2 => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_sha2 [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHA2_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_sha2 [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHA2_FEATURES],
    },
});
