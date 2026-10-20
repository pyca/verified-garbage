//! RSAES-OAEP with SHA-512 and MGF1 with SHA-512: the verified
//! `vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed` and
//! `vg_rsa_oaep_sha512_mgf1_sha512_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha512` for both), for each implementation
//! of the hash function's compression function
//! (`Sha512Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "arm"),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha512_mgf1_sha512::*;
use crate::hashes::sha512::Sha512Backend;

super::oaep_pair!(64, Sha512Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha512_mgf1_sha512_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_crt_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_CRT_IFMA_FEATURES],
        decrypt_umaal: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_umaal [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_shani [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_shani_rsa_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_shani_rsa_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_shani_crt_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    Avx2 => {
        encrypt: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_avx2 [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_FEATURES],
        decrypt: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2 [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_AVX2_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_avx2_rsa_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_avx2_rsa_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_adx [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_AVX2_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_avx2_crt_ifma [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha3 => {
        encrypt: vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed_sha512_sha3 [VG_RSA_OAEP_SHA512_MGF1_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha512_mgf1_sha512_decrypt_sha512_sha3 [VG_RSA_OAEP_SHA512_MGF1_SHA512_DECRYPT_SHA512_SHA3_FEATURES],
    },
});
