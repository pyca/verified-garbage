//! RSAES-OAEP's verified functions on 64-bit RISC-V.

#![cfg(all(target_arch = "riscv64", feature = "alloc"))]

use crate::arch::rsa_oaep::{vg_rsa_oaep_decrypt, vg_rsa_oaep_encrypt_precomputed};

crate::rsa::oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
    },
}
