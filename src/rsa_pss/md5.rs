//! RSASSA-PSS with MD5 and MGF1 with MD5:
//! `vg_rsa_pss_md5_mgf1_md5_sign` and `vg_rsa_pss_md5_mgf1_md5_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.md5`), for each
//! implementation of MD5's compression function that `Md5` runs and,
//! of the RSA operation.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pss_md5_mgf1_md5::{
    VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_ADX_FEATURES, VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_MD5_MGF1_MD5_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES,
    vg_rsa_pss_md5_mgf1_md5_sign_crt_adx, vg_rsa_pss_md5_mgf1_md5_sign_crt_ifma,
    vg_rsa_pss_md5_mgf1_md5_verify_precomputed_rsa_adx,
};
use crate::arch::rsa_pss_md5_mgf1_md5::{
    vg_rsa_pss_md5_mgf1_md5_sign, vg_rsa_pss_md5_mgf1_md5_verify_precomputed,
};
use crate::hashes::md5::Md5Backend;

super::pss_hash!(16, Md5Backend {
    Scalar => {
        verify: vg_rsa_pss_md5_mgf1_md5_verify_precomputed [],
        sign: vg_rsa_pss_md5_mgf1_md5_sign [],
        verify_adx: vg_rsa_pss_md5_mgf1_md5_verify_precomputed_rsa_adx [VG_RSA_PSS_MD5_MGF1_MD5_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        adx: vg_rsa_pss_md5_mgf1_md5_sign_crt_adx [VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_md5_mgf1_md5_sign_crt_ifma [VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_IFMA_FEATURES],
    },
});
