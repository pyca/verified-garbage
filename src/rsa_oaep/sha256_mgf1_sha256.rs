//! RSAES-OAEP with SHA-256 and MGF1 with SHA-256: the verified
//! `vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed` and
//! `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha256` for both), for each implementation
//! of the hash function's compression function
//! (`Sha256Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
use crate::hashes::sha256::Sha256Backend;

super::oaep_pair!(32, Sha256Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt [],
    },
    Sha2 => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHA2_FEATURES],
    },
});
