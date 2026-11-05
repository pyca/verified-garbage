//! RSAES-OAEP's verified functions on AArch64.

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep::{vg_rsa_oaep_decrypt, vg_rsa_oaep_encrypt_precomputed};

crate::rsa::oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
    },
}
