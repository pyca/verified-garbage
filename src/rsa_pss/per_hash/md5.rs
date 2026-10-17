//! RSASSA-PSS with MD5 and MGF1 with MD5:
//! `vg_rsa_pss_md5_mgf1_md5_sign` and `vg_rsa_pss_md5_mgf1_md5_verify_precomputed`
//! (contracts `VG.Spec.RsaPss.signContract` and
//! `VG.Spec.RsaPss.verifyPrecomputedContract` of `VG.Spec.Mgf1.md5`), for each
//! implementation of MD5's compression function that `Md5` runs and,
//! of the RSA operation, on AArch64 (on x86-64, `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` take the hash functions as arguments:
//! `any_hash`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_pss_md5_mgf1_md5::{
    vg_rsa_pss_md5_mgf1_md5_sign, vg_rsa_pss_md5_mgf1_md5_verify_precomputed,
};
use crate::hashes::md5::Md5Backend;

super::super::pss_hash!(16, Md5Backend {
    Scalar => {
        verify: vg_rsa_pss_md5_mgf1_md5_verify_precomputed [],
        sign: vg_rsa_pss_md5_mgf1_md5_sign [],
    },
});
