//! RSAES-OAEP with SHA-512/224 and MGF1 with SHA-512/224: the verified
//! `vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_precomputed` and
//! `vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha512_224` for both), for each implementation
//! of the hash function's compression function
//! (`Sha512_224Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha512_224_mgf1_sha512_224::*;
use crate::hashes::sha512_224::Sha512_224Backend;

super::oaep_pair!(28, Sha512_224Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt [],
        decrypt_umaal: vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_umaal [VG_RSA_OAEP_SHA512_224_MGF1_SHA512_224_DECRYPT_UMAAL_FEATURES],
        encrypt_umaal: vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_precomputed_umaal [VG_RSA_OAEP_SHA512_224_MGF1_SHA512_224_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha3 => {
        encrypt: vg_rsa_oaep_sha512_224_mgf1_sha512_224_encrypt_precomputed_sha512_224_sha3 [VG_RSA_OAEP_SHA512_224_MGF1_SHA512_224_ENCRYPT_PRECOMPUTED_SHA512_224_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha512_224_mgf1_sha512_224_decrypt_sha512_224_sha3 [VG_RSA_OAEP_SHA512_224_MGF1_SHA512_224_DECRYPT_SHA512_224_SHA3_FEATURES],
    },
});
