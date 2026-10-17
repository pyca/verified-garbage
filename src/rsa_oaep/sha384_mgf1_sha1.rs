//! RSAES-OAEP with SHA-384 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha384_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha384_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha384` and `VG.Spec.Mgf1.sha1`), for each implementation
//! of the hash functions' compression functions
//! (`Sha384Backend`, `Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha384_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha384::Sha384Backend;

super::oaep_pair!(48, Sha384Backend, Sha1Backend {
    (Scalar, Scalar) => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha1_decrypt [],
    },
    (Scalar, Sha2) => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha1_encrypt_precomputed_mgf1_sha2 [VG_RSA_OAEP_SHA384_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha1_decrypt_mgf1_sha2 [VG_RSA_OAEP_SHA384_MGF1_SHA1_DECRYPT_MGF1_SHA2_FEATURES],
    },
    (Sha3, Scalar) => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha1_encrypt_precomputed_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA384_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA1_DECRYPT_SHA384_SHA3_FEATURES],
    },
    (Sha3, Sha2) => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha1_encrypt_precomputed_sha384_sha3_mgf1_sha2 [VG_RSA_OAEP_SHA384_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA384_SHA3_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha1_decrypt_sha384_sha3_mgf1_sha2 [VG_RSA_OAEP_SHA384_MGF1_SHA1_DECRYPT_SHA384_SHA3_MGF1_SHA2_FEATURES],
    },
} never {
    // None: SHA-384's implementations and SHA-1's are chosen by
    // different features, so every pair of them is chosen by some CPU.
});
