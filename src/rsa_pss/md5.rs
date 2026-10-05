//! RSASSA-PSS with MD5 and MGF1 with MD5:
//! `vg_rsa_pss_md5_mgf1_md5_sign` and `vg_rsa_pss_md5_mgf1_md5_verify`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyContract` of `VG.Spec.Mgf1.md5`), for each
//! implementation of MD5's compression function that `Md5` runs and,
//! when signing, of the private-key operation.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss_md5_mgf1_md5::{
    VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_ADX_FEATURES,
    VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_IFMA_FEATURES,
    vg_rsa_pss_md5_mgf1_md5_sign,
    vg_rsa_pss_md5_mgf1_md5_sign_crt_adx,
    vg_rsa_pss_md5_mgf1_md5_sign_crt_ifma,
    vg_rsa_pss_md5_mgf1_md5_verify,
};
use crate::hashes::md5::Md5Backend;

super::pss_hash!(Md5Backend {
    Scalar => {
        verify: vg_rsa_pss_md5_mgf1_md5_verify [],
        sign: vg_rsa_pss_md5_mgf1_md5_sign [],
        adx: vg_rsa_pss_md5_mgf1_md5_sign_crt_adx [VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_ADX_FEATURES],
        ifma: vg_rsa_pss_md5_mgf1_md5_sign_crt_ifma [VG_RSA_PSS_MD5_MGF1_MD5_SIGN_CRT_IFMA_FEATURES],
    },
});
