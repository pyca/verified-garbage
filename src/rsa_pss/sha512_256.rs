//! RSASSA-PSS with SHA-512/256 and MGF1 with SHA-512/256:
//! `vg_rsa_pss_sha512_256_mgf1_sha512_256_sign` and `vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha512_256`), for each
//! implementation of SHA-512/256's compression function that `Sha512_256` runs and,
//! of the RSA operation, on AArch64 (on x86-64, `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` take the hash functions as arguments:
//! `any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_pss_sha512_256_mgf1_sha512_256::{
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHA3_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_PRECOMPUTED_SHA512_256_SHA3_FEATURES,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_sha3,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed_sha512_256_sha3,
};
use crate::hashes::sha512_256::Sha512_256Backend;

super::pss_hash!(32, Sha512_256Backend {
    Scalar => {
        verify: vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed [],
        sign: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign [],
    },
    Sha3 => {
        verify: vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_precomputed_sha512_256_sha3 [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_PRECOMPUTED_SHA512_256_SHA3_FEATURES],
        sign: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_sha3 [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHA3_FEATURES],
    },
});
