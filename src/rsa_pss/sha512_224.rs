//! RSASSA-PSS with SHA-512/224 and MGF1 with SHA-512/224:
//! `vg_rsa_pss_sha512_224_mgf1_sha512_224_sign` and `vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha512_224`), for each
//! implementation of SHA-512/224's compression function that `Sha512_224` runs and,
//! of the RSA operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha512_224_mgf1_sha512_224::{
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_AVX2_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_AVX2_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_SHANI_FEATURES,
    VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_SHANI_RSA_ADX_FEATURES,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign, vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_crt_adx,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_crt_ifma,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2_crt_adx,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2_crt_ifma,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani_crt_adx,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani_crt_ifma,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_rsa_adx,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_avx2,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_avx2_rsa_adx,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_shani,
    vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_shani_rsa_adx,
};
use crate::hashes::sha512_224::Sha512_224Backend;

super::pss_hash!(28, Sha512_224Backend {
    Scalar => {
        verify: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed [],
        verify_adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_rsa_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        sign: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign [],
        adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_crt_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_crt_ifma [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_shani [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_SHANI_FEATURES],
        verify_adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_shani_rsa_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_SHANI_RSA_ADX_FEATURES],
        sign: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_FEATURES],
        adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani_crt_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_shani_crt_ifma [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        verify: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_avx2 [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_AVX2_FEATURES],
        verify_adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_verify_precomputed_sha512_224_avx2_rsa_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_VERIFY_PRECOMPUTED_SHA512_224_AVX2_RSA_ADX_FEATURES],
        sign: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2 [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_FEATURES],
        adx: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2_crt_adx [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha512_224_mgf1_sha512_224_sign_sha512_224_avx2_crt_ifma [VG_RSA_PSS_SHA512_224_MGF1_SHA512_224_SIGN_SHA512_224_AVX2_CRT_IFMA_FEATURES],
    },
});
