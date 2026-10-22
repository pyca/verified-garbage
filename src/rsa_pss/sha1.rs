//! RSASSA-PSS with SHA-1 and MGF1 with SHA-1:
//! `vg_rsa_pss_sha1_mgf1_sha1_sign` and `vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.sha1`), for each
//! implementation of SHA-1's compression function that `Sha1` runs and,
//! of the RSA operation.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm"
    ),
    feature = "alloc"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_RSA_IFMA_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_RSA_ADX_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_RSA_IFMA_FEATURES,
    vg_rsa_pss_sha1_mgf1_sha1_sign_crt_adx, vg_rsa_pss_sha1_mgf1_sha1_sign_crt_ifma,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani, vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_adx,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_ifma,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_rsa_adx,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_rsa_ifma,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani_rsa_adx,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani_rsa_ifma,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHA2_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHA2_FEATURES,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_sha2,
    vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_sha2,
};
#[cfg(target_arch = "x86")]
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHANI_FEATURES,
    vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani, vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_shani,
};
#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_UMAAL_FEATURES,
    VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_UMAAL_FEATURES,
    vg_rsa_pss_sha1_mgf1_sha1_sign_umaal, vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_umaal,
};
use crate::arch::rsa_pss_sha1_mgf1_sha1::{
    vg_rsa_pss_sha1_mgf1_sha1_sign, vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed,
};
use crate::hashes::sha1::Sha1Backend;

super::pss_hash!(20, Sha1Backend {
    Scalar => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed [],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign [],
        verify_adx: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_rsa_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        verify_ifma: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_rsa_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_RSA_IFMA_FEATURES],
        adx: vg_rsa_pss_sha1_mgf1_sha1_sign_crt_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha1_mgf1_sha1_sign_crt_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_CRT_IFMA_FEATURES],
        umaal: vg_rsa_pss_sha1_mgf1_sha1_sign_umaal [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_UMAAL_FEATURES],
        verify_umaal: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_umaal [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86")]
    ShaNi => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHANI_FEATURES],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_FEATURES],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_FEATURES],
        verify_adx: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani_rsa_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_RSA_ADX_FEATURES],
        verify_ifma: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_shani_rsa_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHANI_RSA_IFMA_FEATURES],
        adx: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_adx [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_shani_crt_ifma [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        verify: vg_rsa_pss_sha1_mgf1_sha1_verify_precomputed_sha1_sha2 [VG_RSA_PSS_SHA1_MGF1_SHA1_VERIFY_PRECOMPUTED_SHA1_SHA2_FEATURES],
        sign: vg_rsa_pss_sha1_mgf1_sha1_sign_sha1_sha2 [VG_RSA_PSS_SHA1_MGF1_SHA1_SIGN_SHA1_SHA2_FEATURES],
    },
});
