//! RSAES-OAEP with SHA-384 and MGF1 with SHA-384: the verified
//! `vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed` and
//! `vg_rsa_oaep_sha384_mgf1_sha384_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha384` for both), for each implementation
//! of the hash function's compression function
//! (`Sha384Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm"
    ),
    feature = "alloc"
))]

use crate::arch::rsa_oaep_sha384_mgf1_sha384::*;
use crate::hashes::sha384::Sha384Backend;

super::oaep_pair!(48, Sha384Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_crt_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_CRT_IFMA_FEATURES],
        decrypt_umaal: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_umaal [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_UMAAL_FEATURES],
        encrypt_umaal: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_umaal [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    ShaNi => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_shani [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_shani_rsa_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_shani_rsa_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_shani_crt_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    Avx2 => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_avx2 [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_AVX2_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2 [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_AVX2_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_avx2_rsa_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_AVX2_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_avx2_rsa_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_AVX2_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_adx [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_AVX2_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_avx2_crt_ifma [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    Sha3 => {
        encrypt: vg_rsa_oaep_sha384_mgf1_sha384_encrypt_precomputed_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA384_ENCRYPT_PRECOMPUTED_SHA384_SHA3_FEATURES],
        decrypt: vg_rsa_oaep_sha384_mgf1_sha384_decrypt_sha384_sha3 [VG_RSA_OAEP_SHA384_MGF1_SHA384_DECRYPT_SHA384_SHA3_FEATURES],
    },
});
