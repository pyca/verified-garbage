//! RSASSA-PSS with SHA-512 and MGF1 with SHA-512:
//! `vg_rsa_pss_sha512_mgf1_sha512_sign` and `vg_rsa_pss_sha512_mgf1_sha512_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.sha512`), for each
//! implementation of SHA-512's compression function that `Sha512` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha512_mgf1_sha512::{
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_SHANI_FEATURES, vg_rsa_pss_sha512_mgf1_sha512_sign,
    vg_rsa_pss_sha512_mgf1_sha512_sign_crt_adx, vg_rsa_pss_sha512_mgf1_sha512_sign_crt_ifma,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2_crt_adx,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2_crt_ifma,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani_crt_adx,
    vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani_crt_ifma, vg_rsa_pss_sha512_mgf1_sha512_verify,
    vg_rsa_pss_sha512_mgf1_sha512_verify_avx2, vg_rsa_pss_sha512_mgf1_sha512_verify_shani,
};
use crate::hashes::sha512::Sha512Backend;

super::pss_hash!(64, Sha512Backend {
    Scalar => {
        verify: vg_rsa_pss_sha512_mgf1_sha512_verify [],
        sign: vg_rsa_pss_sha512_mgf1_sha512_sign [],
        adx: vg_rsa_pss_sha512_mgf1_sha512_sign_crt_adx [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_mgf1_sha512_sign_crt_ifma [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha512_mgf1_sha512_verify_shani [VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_SHANI_FEATURES],
        sign: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_FEATURES],
        adx: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani_crt_adx [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_shani_crt_ifma [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        verify: vg_rsa_pss_sha512_mgf1_sha512_verify_avx2 [VG_RSA_PSS_SHA512_MGF1_SHA512_VERIFY_AVX2_FEATURES],
        sign: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2 [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_FEATURES],
        adx: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2_crt_adx [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_mgf1_sha512_sign_sha512_avx2_crt_ifma [VG_RSA_PSS_SHA512_MGF1_SHA512_SIGN_SHA512_AVX2_CRT_IFMA_FEATURES],
    },
});
