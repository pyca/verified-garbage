//! RSAES-OAEP with SHA-512 on x86-64: the verified
//! `vg_rsa_oaep_sha512_encrypt_precomputed` and `vg_rsa_oaep_sha512_decrypt`
//! (contracts `VG.Spec.RsaOaep.encryptTableContract` and
//! `decryptTableContract` of `VG.Spec.Mgf1.sha512`), which take MGF1's hash
//! function as a table, for each implementation of SHA-512's compression
//! function (`Sha512Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha512::*;
use crate::hashes::sha512::Sha512Backend;

super::oaep_hash!(64, Sha512Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha512_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha512_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha512_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_decrypt_crt_adx [VG_RSA_OAEP_SHA512_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_decrypt_crt_ifma [VG_RSA_OAEP_SHA512_DECRYPT_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        encrypt: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_shani [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha512_decrypt_sha512_shani [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_shani_rsa_adx [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_shani_rsa_ifma [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_decrypt_sha512_shani_crt_adx [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_decrypt_sha512_shani_crt_ifma [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_SHANI_CRT_IFMA_FEATURES],
    },
    Avx2 => {
        encrypt: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_avx2 [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_FEATURES],
        decrypt: vg_rsa_oaep_sha512_decrypt_sha512_avx2 [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_AVX2_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_avx2_rsa_adx [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha512_encrypt_precomputed_sha512_avx2_rsa_ifma [VG_RSA_OAEP_SHA512_ENCRYPT_PRECOMPUTED_SHA512_AVX2_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha512_decrypt_sha512_avx2_crt_adx [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_AVX2_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha512_decrypt_sha512_avx2_crt_ifma [VG_RSA_OAEP_SHA512_DECRYPT_SHA512_AVX2_CRT_IFMA_FEATURES],
    },
});
