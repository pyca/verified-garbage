//! RSAES-OAEP with SHA-1 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha1_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha1` for both), for each implementation
//! of the hash function's compression function
//! (`Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;

super::oaep_pair!(20, Sha1Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt [],
    },
    Sha2 => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_sha1_sha2 [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_sha2 [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHA2_FEATURES],
    },
});
