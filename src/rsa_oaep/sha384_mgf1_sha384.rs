//! RSAES-OAEP with SHA-384 and MGF1 with SHA-384: the verified
//! `vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed` and
//! `vg_rsa_oaep_sha384_mgf1_sha384_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha384` for both), for each implementation
//! of the hash function's compression function
//! (`Sha384Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "aarch64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
use crate::hashes::sha384::Sha384Backend;

super::oaep_pair!(48, Sha384Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt [],
    },
    Sha3 => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_SHA3_FEATURES],
    },
});
