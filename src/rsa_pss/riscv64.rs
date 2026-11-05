//! RSASSA-PSS's verified functions on 64-bit RISC-V: `vg_rsa_pss_sign` and
//! `vg_rsa_pss_verify_precomputed` (contracts
//! `VG.Spec.RsaPss.signTableContract` and `verifyPrecomputedTableContract`),
//! which take the hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::pss_functions!` chooses from.

#![cfg(all(target_arch = "riscv64", feature = "alloc"))]

use crate::arch::rsa_pss::{vg_rsa_pss_sign, vg_rsa_pss_verify_precomputed};

super::table::pss_functions! {
    sign: {
        Baseline => vg_rsa_pss_sign [],
    },
    verify: {
        Baseline => vg_rsa_pss_verify_precomputed [],
    },
}
