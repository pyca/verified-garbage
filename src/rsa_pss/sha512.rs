//! RSASSA-PSS with SHA-512 and MGF1 with SHA-512:
//! `vg_rsa_pss_sha512_mgf1_sha512_sign` and `vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha512`), for each
//! implementation of SHA-512's compression function that `Sha512` runs and,
//! of the RSA operation, on AArch64 (on x86-64, `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` take the hash functions as arguments:
//! `any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_pss_sha512_mgf1_sha512::{VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHA3_FEATURES, VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_PRECOMPUTED_SHA512_SHA3_FEATURES, vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_sha3, vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed_sha512_sha3, vg_rsa_pss_sha512_mgf1_sha512_sign, vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed};
use crate::hashes::sha512::Sha512Backend;

super::pss_hash!(64, Sha512Backend {
    Scalar => {
        verify: vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed [],
        sign: vg_rsa_pss_sha512_mgf1_sha512_sign [],
    },
    Sha3 => {
        verify: vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed_sha512_sha3 [VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_PRECOMPUTED_SHA512_SHA3_FEATURES],
        sign: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_sha3 [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHA3_FEATURES],
    },
});
