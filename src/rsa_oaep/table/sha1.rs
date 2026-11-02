//! RSAES-OAEP with SHA-1 on x86-64: the verified
//! `vg_rsa_oaep_sha1_encrypt_precomputed` and `vg_rsa_oaep_sha1_decrypt`
//! (contracts `VG.Spec.RsaOaep.encryptTableContract` and
//! `decryptTableContract` of `VG.Spec.Mgf1.sha1`), which take MGF1's hash
//! function as a table, for each implementation of SHA-1's compression
//! function (`Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use crate::arch::rsa_oaep_sha1::*;
use crate::hashes::sha1::Sha1Backend;

super::oaep_hash!(20, Sha1Backend {
    Scalar => {
        encrypt: vg_rsa_oaep_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha1_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha1_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA1_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha1_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA1_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha1_decrypt_crt_adx [VG_RSA_OAEP_SHA1_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha1_decrypt_crt_ifma [VG_RSA_OAEP_SHA1_DECRYPT_CRT_IFMA_FEATURES],
    },
    ShaNi => {
        encrypt: vg_rsa_oaep_sha1_encrypt_precomputed_sha1_shani [VG_RSA_OAEP_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha1_decrypt_sha1_shani [VG_RSA_OAEP_SHA1_DECRYPT_SHA1_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha1_encrypt_precomputed_sha1_shani_rsa_adx [VG_RSA_OAEP_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha1_encrypt_precomputed_sha1_shani_rsa_ifma [VG_RSA_OAEP_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha1_decrypt_sha1_shani_crt_adx [VG_RSA_OAEP_SHA1_DECRYPT_SHA1_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha1_decrypt_sha1_shani_crt_ifma [VG_RSA_OAEP_SHA1_DECRYPT_SHA1_SHANI_CRT_IFMA_FEATURES],
    },
});
