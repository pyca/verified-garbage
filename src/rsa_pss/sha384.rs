//! RSASSA-PSS with SHA-384 and MGF1 with SHA-384:
//! `vg_rsa_pss_sha384_mgf1_sha384_sign` and `vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha384`), for each
//! implementation of SHA-384's compression function that `Sha384` runs and,
//! of the RSA operation.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pss_sha384_mgf1_sha384::{
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_AVX2_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_AVX2_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHANI_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHANI_RSA_ADX_FEATURES,
    vg_rsa_pss_sha384_mgf1_sha384_sign_crt_adx, vg_rsa_pss_sha384_mgf1_sha384_sign_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_adx,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_adx,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_ifma,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_rsa_adx,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_avx2,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_avx2_rsa_adx,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_shani,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_shani_rsa_adx,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::rsa_pss_sha384_mgf1_sha384::{
    VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHA3_FEATURES,
    VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHA3_FEATURES,
    vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_sha3,
    vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_sha3,
};
use crate::arch::rsa_pss_sha384_mgf1_sha384::{
    vg_rsa_pss_sha384_mgf1_sha384_sign, vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed,
};
use crate::hashes::sha384::Sha384Backend;

super::pss_hash!(48, Sha384Backend {
    Scalar => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed [],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign [],
        verify_adx: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_rsa_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_shani [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHANI_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_FEATURES],
        verify_adx: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_shani_rsa_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHANI_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_shani_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    Avx2 => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_avx2 [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_AVX2_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2 [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_FEATURES],
        verify_adx: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_avx2_rsa_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_AVX2_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_adx [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_avx2_crt_ifma [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha3 => {
        verify: vg_rsa_pss_sha384_mgf1_sha384_verify_precomputed_sha384_sha3 [VG_RSA_PSS_SHA384_MGF1_SHA384_VERIFY_PRECOMPUTED_SHA384_SHA3_FEATURES],
        sign: vg_rsa_pss_sha384_mgf1_sha384_sign_sha384_sha3 [VG_RSA_PSS_SHA384_MGF1_SHA384_SIGN_SHA384_SHA3_FEATURES],
    },
});
