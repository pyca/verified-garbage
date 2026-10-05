//! RSASSA-PSS with SHA-1 and MGF1 with SHA-1:
//! `vg_rsa_pss_sha1_mgf1_sha1_sign` and `vg_rsa_pss_sha1_mgf1_sha1_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.sha1`), for each
//! implementation of SHA-1's compression function that `Sha1` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_SHANI_FEATURES, vg_rsa_pss_sha1_mgf1_sha1_sign,
    vg_rsa_pss_sha1_mgf1_sha1_sign_crt_adx, vg_rsa_pss_sha1_mgf1_sha1_sign_crt_ifma,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani, vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_adx,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_ifma, vg_rsa_pss_sha1_mgf1_sha1_verify,
    vg_rsa_pss_sha1_mgf1_sha1_verify_shani,
};
use crate::hashes::sha1::Sha1Backend;

super::pss_hash!(20, Sha1Backend {
    Scalar => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify [],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign [],
        adx: vg_rsa_pss_sha1_mgf1_sha1_sign_crt_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha1_mgf1_sha1_sign_crt_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_SHANI_FEATURES],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES],
        adx: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_IFMA_FEATURES],
    },
});
