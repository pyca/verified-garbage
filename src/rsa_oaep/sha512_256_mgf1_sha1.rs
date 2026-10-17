//! RSAES-OAEP with SHA-512/256 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha512_256` and `VG.Spec.Mgf1.sha1`), for each implementation
//! of the hash functions' compression functions
//! (`Sha512_256Backend`, `Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha512_256_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha512_256::Sha512_256Backend;

super::oaep_pair!(32, Sha512_256Backend, Sha1Backend {
    (Scalar, Scalar) => {
        encrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt [],
    },
    (Scalar, Sha2) => {
        encrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_precomputed_mgf1_sha2 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_mgf1_sha2 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_DECRYPT_MGF1_SHA2_FEATURES],
    },
    (Sha3, Scalar) => {
        encrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_precomputed_sha512_256_sha3 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA512_256_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_sha3 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_DECRYPT_SHA512_256_SHA3_FEATURES],
    },
    (Sha3, Sha2) => {
        encrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_encrypt_precomputed_sha512_256_sha3_mgf1_sha2 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA512_256_SHA3_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha512_256_mgf1_sha1_decrypt_sha512_256_sha3_mgf1_sha2 [VG_RSA_OAEP_SHA512_256_MGF1_SHA1_DECRYPT_SHA512_256_SHA3_MGF1_SHA2_FEATURES],
    },
} never {
    // None: SHA-512/256's implementations and SHA-1's are chosen by
    // different features, so every pair of them is chosen by some CPU.
});
