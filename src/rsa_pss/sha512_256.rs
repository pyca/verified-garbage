//! RSASSA-PSS with SHA-512/256 and MGF1 with SHA-512/256:
//! `vg_rsa_pss_sha512_256_mgf1_sha512_256_sign` and `vg_rsa_pss_sha512_256_mgf1_sha512_256_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.sha512_256`), for each
//! implementation of SHA-512/256's compression function that `Sha512_256` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha512_256_mgf1_sha512_256::{
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_SHANI_FEATURES,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_crt_adx,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_crt_ifma,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2_crt_adx,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2_crt_ifma,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani_crt_adx,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani_crt_ifma,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_verify,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_avx2,
    vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_shani,
};
use crate::hashes::sha512_256::Sha512_256Backend;

super::pss_hash!(Sha512_256Backend {
    Scalar => {
        verify: vg_rsa_pss_sha512_256_mgf1_sha512_256_verify [],
        sign: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign [],
        adx: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_crt_adx [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_crt_ifma [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_shani [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_SHANI_FEATURES],
        sign: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_FEATURES],
        adx: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani_crt_adx [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_shani_crt_ifma [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        verify: vg_rsa_pss_sha512_256_mgf1_sha512_256_verify_avx2 [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_VERIFY_AVX2_FEATURES],
        sign: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2 [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_FEATURES],
        adx: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2_crt_adx [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_256_mgf1_sha512_256_sign_sha512_256_avx2_crt_ifma [VG_RSA_PSS_SHA512_256_MGF1_SHA512_256_SIGN_SHA512_256_AVX2_CRT_IFMA_FEATURES],
    },
});
