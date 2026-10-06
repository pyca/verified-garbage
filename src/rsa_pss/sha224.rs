//! RSASSA-PSS with SHA-224 and MGF1 with SHA-224:
//! `vg_rsa_pss_sha224_mgf1_sha224_sign` and `vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha224`), for each
//! implementation of SHA-224's compression function that `Sha224` runs and,
//! of the RSA operation.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pss_sha224_mgf1_sha224::{
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_AVX2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_AVX2_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHANI_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHANI_RSA_ADX_FEATURES,
    vg_rsa_pss_sha224_mgf1_sha224_sign_crt_adx, vg_rsa_pss_sha224_mgf1_sha224_sign_crt_ifma,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_adx,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_ifma,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_adx,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_ifma,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_rsa_adx,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2_rsa_adx,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani_rsa_adx,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::rsa_pss_sha224_mgf1_sha224::{
    VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHA2_FEATURES,
    VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHA2_FEATURES,
    vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_sha2,
    vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_sha2,
};
use crate::arch::rsa_pss_sha224_mgf1_sha224::{
    vg_rsa_pss_sha224_mgf1_sha224_sign, vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed,
};
use crate::hashes::sha224::Sha224Backend;

super::pss_hash!(28, Sha224Backend {
    Scalar => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed [],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign [],
        verify_adx: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_rsa_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHANI_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_FEATURES],
        verify_adx: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_shani_rsa_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHANI_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_shani_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    Avx2 => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2 [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_AVX2_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2 [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_FEATURES],
        verify_adx: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_avx2_rsa_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_AVX2_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_adx [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_avx2_crt_ifma [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        verify: vg_rsa_pss_sha224_mgf1_sha224_verify_precomputed_sha224_sha2 [VG_RSA_PSS_SHA224_MGF1_SHA224_VERIFY_PRECOMPUTED_SHA224_SHA2_FEATURES],
        sign: vg_rsa_pss_sha224_mgf1_sha224_sign_sha224_sha2 [VG_RSA_PSS_SHA224_MGF1_SHA224_SIGN_SHA224_SHA2_FEATURES],
    },
});
