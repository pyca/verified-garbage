//! RSAES-OAEP with SHA-1 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha1_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha1` for both), for each implementation
//! of the hash function's compression function
//! (`Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64"
    ),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha1_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;

super::oaep_pair!(20, Sha1Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_adx [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_crt_ifma [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_CRT_IFMA_FEATURES],
        decrypt_umaal: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_umaal [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_UMAAL_FEATURES],
        encrypt_umaal: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_umaal [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_shani [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHANI_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_sha1_shani [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_sha1_shani_rsa_adx [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_sha1_shani_rsa_ifma [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_adx [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_shani_crt_ifma [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha2 => {
        encrypt: vg_rsa_oaep_sha1_mgf1_sha1_encrypt_precomputed_sha1_sha2 [VG_RSA_OAEP_SHA1_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha1_mgf1_sha1_decrypt_sha1_sha2 [VG_RSA_OAEP_SHA1_MGF1_SHA1_DECRYPT_SHA1_SHA2_FEATURES],
    },
});
