//! RSAES-OAEP with SHA-256 and MGF1 with SHA-256: the verified
//! `vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed` and
//! `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha256` for both), for each implementation
//! of the hash function's compression function
//! (`Sha256Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
use crate::hashes::sha256::Sha256Backend;

super::oaep_pair!(32, Sha256Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt [],
        decrypt_umaal: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_umaal [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_UMAAL_FEATURES],
        encrypt_umaal: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_umaal [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_shani [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHANI_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHA2_FEATURES],
    },
});
