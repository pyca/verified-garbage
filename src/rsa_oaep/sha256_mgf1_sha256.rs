//! RSAES-OAEP with SHA-256 and MGF1 with SHA-256: the verified
//! `vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed` and
//! `vg_rsa_oaep_sha256_mgf1_sha256_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha256` for both), for each implementation
//! of the hash function's compression function
//! (`Sha256Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha256_mgf1_sha256::*;
use crate::hashes::sha256::Sha256Backend;

super::oaep_pair!(32, Sha256Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_crt_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_shani [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_shani_rsa_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_shani_rsa_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_shani_crt_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    Avx2 => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_avx2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_AVX2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_AVX2_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_avx2_rsa_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_AVX2_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_avx2_rsa_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_AVX2_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_adx [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_AVX2_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_avx2_crt_ifma [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        encrypt: vg_rsa_oaep_sha256_mgf1_sha256_encrypt_precomputed_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_ENCRYPT_PRECOMPUTED_SHA256_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha256_mgf1_sha256_decrypt_sha256_sha2 [VG_RSA_OAEP_SHA256_MGF1_SHA256_DECRYPT_SHA256_SHA2_FEATURES],
    },
});
