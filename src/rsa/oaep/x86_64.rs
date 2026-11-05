//! RSAES-OAEP's verified functions on x86-64: `vg_rsa_oaep_encrypt_precomputed`
//! and `vg_rsa_oaep_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptTablesContract` and `decryptTablesContract`),
//! which take the label's hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::oaep_functions!` chooses from.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_oaep::{
    VG_RSA_OAEP_DECRYPT_CRT_ADX_FEATURES, VG_RSA_OAEP_DECRYPT_CRT_IFMA_FEATURES,
    VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES,
    VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES, vg_rsa_oaep_decrypt,
    vg_rsa_oaep_decrypt_crt_adx, vg_rsa_oaep_decrypt_crt_ifma, vg_rsa_oaep_encrypt_precomputed,
    vg_rsa_oaep_encrypt_precomputed_rsa_adx, vg_rsa_oaep_encrypt_precomputed_rsa_ifma,
};

crate::rsa::oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
        Adx => vg_rsa_oaep_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        Ifma => vg_rsa_oaep_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
        Adx => vg_rsa_oaep_decrypt_crt_adx [VG_RSA_OAEP_DECRYPT_CRT_ADX_FEATURES],
        Ifma => vg_rsa_oaep_decrypt_crt_ifma [VG_RSA_OAEP_DECRYPT_CRT_IFMA_FEATURES],
    },
}
