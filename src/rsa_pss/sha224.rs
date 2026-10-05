//! RSASSA-PSS with SHA-224 and MGF1 with SHA-224:
//! `vg_rsa_pss_sha224_mgf1_sha224_sign` and `vg_rsa_pss_sha224_mgf1_sha224_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.sha224`), for each
//! implementation of SHA-224's compression function that `Sha224` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_sha224_mgf1_sha224::{
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_AVX2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_SHANI_FEATURES, vg_rsa_pss_sha224_mgf1_sha224_sign,
    vg_rsa_pss_sha224_mgf1_sha224_sign_crt_adx, vg_rsa_pss_sha224_mgf1_sha224_sign_crt_ifma,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_adx,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_ifma,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_adx,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_ifma, vg_rsa_pss_sha224_mgf1_sha224_verify,
    vg_rsa_pss_sha224_mgf1_sha224_verify_avx2, vg_rsa_pss_sha224_mgf1_sha224_verify_shani,
};
use crate::hashes::sha224::Sha224Backend;

super::pss_hash!(28, Sha224Backend {
    Scalar => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify [],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign [],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_shani [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_SHANI_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_FEATURES],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_avx2 [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_AVX2_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2 [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_FEATURES],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_IFMA_FEATURES],
    },
});
