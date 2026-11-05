//! RSASSA-PSS's verified functions on x86-64.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_pss::{
    vg_rsa_pss_sign, vg_rsa_pss_sign_crt_adx, vg_rsa_pss_sign_crt_ifma,
    vg_rsa_pss_verify_precomputed, vg_rsa_pss_verify_precomputed_rsa_adx,
    vg_rsa_pss_verify_precomputed_rsa_ifma,
};

super::table::pss_functions! {
    sign: {
        Baseline => vg_rsa_pss_sign [],
        Adx => vg_rsa_pss_sign_crt_adx [crate::arch::rsa_pss::VG_RSA_PSS_SIGN_CRT_ADX_FEATURES],
        Ifma => vg_rsa_pss_sign_crt_ifma [crate::arch::rsa_pss::VG_RSA_PSS_SIGN_CRT_IFMA_FEATURES],
    },
    verify: {
        Baseline => vg_rsa_pss_verify_precomputed [],
        Adx => vg_rsa_pss_verify_precomputed_rsa_adx [crate::arch::rsa_pss::VG_RSA_PSS_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES],
        Ifma => vg_rsa_pss_verify_precomputed_rsa_ifma [crate::arch::rsa_pss::VG_RSA_PSS_VERIFY_PRECOMPUTED_RSA_IFMA_FEATURES],
    },
}
