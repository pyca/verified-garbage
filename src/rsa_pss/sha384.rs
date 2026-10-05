//! RSASSA-PSS with SHA-384 and MGF1 with SHA-384:
//! `vg_rsa_pss_sha384_mgf1_sha384_sign` and `vg_rsa_pss_sha384_mgf1_sha384_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.sha384`), for each
//! implementation of SHA-384's compression function that `Sha384` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha384_mgf1_sha384::{
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_AVX2_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_SHANI_FEATURES,
    vg_rsa_pss_sha384_mgf1_sha384_sign,
    vg_rsa_pss_sha384_mgf1_sha384_sign_crt_adx,
    vg_rsa_pss_sha384_mgf1_sha384_sign_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_adx,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_adx,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_verify,
    vg_rsa_pss_sha384_mgf1_sha384_verify_avx2,
    vg_rsa_pss_sha384_mgf1_sha384_verify_shani,
};
use crate::hashes::sha384::Sha384Backend;

super::pss_hash!(Sha384Backend {
    Scalar => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify [],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign [],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_shani [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_SHANI_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_FEATURES],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_avx2 [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_AVX2_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2 [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_FEATURES],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_IFMA_FEATURES],
    },
});
