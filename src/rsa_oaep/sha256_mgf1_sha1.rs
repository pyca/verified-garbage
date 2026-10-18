//! RSAES-OAEP with SHA-256 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha256_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha256` and `VG.Spec.Mgf1.sha1`), for each implementation
//! of the hash functions' compression functions
//! (`Sha256Backend`, `Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha256_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha256::Sha256Backend;

super::oaep_pair!(32, Sha256Backend, Sha1Backend {
    (Scalar, Scalar) => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha1_decrypt [],
    },
    (Sha2, Sha2) => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_sha2_mgf1_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA256_SHA2_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_sha2_mgf1_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_DECRYPT_SHA256_SHA2_MGF1_SHA2_FEATURES],
    },
} never {
    // SHA-1's and SHA-256's code with the SHA-2 instructions needs the same
    // feature (`sha2`): no CPU selects these pairs (`backend_features`
    // checks it).
    (Scalar, Sha2) => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_mgf1_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha1_decrypt_mgf1_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_DECRYPT_MGF1_SHA2_FEATURES],
    },
    (Sha2, Scalar) => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha1_encrypt_precomputed_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA256_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha1_decrypt_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA1_DECRYPT_SHA256_SHA2_FEATURES],
    },
});
