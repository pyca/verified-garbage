//! RSASSA-PSS's verified functions on 64-bit RISC-V.

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
