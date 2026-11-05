//! RSASSA-PSS's verified functions on ARMv7: `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` (contracts
//! `VG.Spec.RsaPss.signTableContract` and `verifyPrecomputedTableContract`),
//! which take the hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::pss_functions!` chooses from.

#![cfg(all(target_arch = "arm", feature = "alloc"))]

use crate::arch::rsa_pss::{vg_rsa_pss_sign, vg_rsa_pss_verify_precomputed};
#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd"
))]
use crate::arch::rsa_pss::{vg_rsa_pss_sign_umaal, vg_rsa_pss_verify_precomputed_umaal};

super::table::pss_functions! {
    sign: {
        Baseline => vg_rsa_pss_sign [],
        #[cfg(any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        ))]
        Umaal => vg_rsa_pss_sign_umaal [crate::arch::rsa_pss::VG_RSA_PSS_SIGN_UMAAL_FEATURES],
    },
    verify: {
        Baseline => vg_rsa_pss_verify_precomputed [],
        #[cfg(any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        ))]
        Umaal => vg_rsa_pss_verify_precomputed_umaal [crate::arch::rsa_pss::VG_RSA_PSS_VERIFY_PRECOMPUTED_UMAAL_FEATURES],
    },
}
