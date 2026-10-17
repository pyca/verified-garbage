//! RSAES-OAEP with SHA-224 and MGF1 with SHA-224: the verified
//! `vg_rsa_oaep_sha224_mgf1_sha224_encrypt_precomputed` and
//! `vg_rsa_oaep_sha224_mgf1_sha224_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha224` for both), for each implementation
//! of the hash function's compression function
//! (`Sha224Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha224_mgf1_sha224::*;
use crate::hashes::sha224::Sha224Backend;

super::oaep_pair!(28, Sha224Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha224_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha224_decrypt [],
    },
    Sha2 => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha224_encrypt_precomputed_sha224_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA224_ENCRYPT_PRECOMPUTED_SHA224_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha224_decrypt_sha224_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA224_DECRYPT_SHA224_SHA2_FEATURES],
    },
});
