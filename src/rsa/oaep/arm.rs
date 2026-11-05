//! RSAES-OAEP's verified functions on ARMv7: `vg_rsa_oaep_encrypt_precomputed`
//! and `vg_rsa_oaep_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptTablesContract` and `decryptTablesContract`),
//! which take the label's hash function and MGF1's as tables, for each
//! implementation of the RSA operations (`crate::rsa::Backend`), which
//! `table::oaep_functions!` chooses from.

#![cfg(all(target_arch = "arm", feature = "alloc"))]

#[cfg(any(
    target_os = "linux",
    target_os = "android",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd"
))]
use crate::arch::rsa_oaep::{
    VG_RSA_OAEP_DECRYPT_UMAAL_FEATURES, VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES,
    vg_rsa_oaep_decrypt_umaal, vg_rsa_oaep_encrypt_precomputed_umaal,
};
use crate::arch::rsa_oaep::{vg_rsa_oaep_decrypt, vg_rsa_oaep_encrypt_precomputed};

crate::rsa::oaep::table::oaep_functions! {
    encrypt: {
        Baseline => vg_rsa_oaep_encrypt_precomputed [],
        #[cfg(any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        ))]
        Umaal => vg_rsa_oaep_encrypt_precomputed_umaal [VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    decrypt: {
        Baseline => vg_rsa_oaep_decrypt [],
        #[cfg(any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        ))]
        Umaal => vg_rsa_oaep_decrypt_umaal [VG_RSA_OAEP_DECRYPT_UMAAL_FEATURES],
    },
}
