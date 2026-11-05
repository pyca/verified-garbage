//! RSAES-OAEP's verified functions on 32-bit x86: `vg_rsa_oaep_encrypt_precomputed`
//! and `vg_rsa_oaep_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptTablesContract` and `decryptTablesContract`),
//! which take the label's hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::oaep_functions!` chooses from.

#![cfg(all(target_arch = "x86", feature = "alloc"))]

use crate::arch::rsa_oaep::{vg_rsa_oaep_decrypt, vg_rsa_oaep_encrypt_precomputed};

crate::rsa_oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
    },
}
