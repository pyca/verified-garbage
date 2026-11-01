//! RSAES-OAEP with SHA-224 and MGF1 with SHA-1: the verified
//! `vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed` and
//! `vg_rsa_oaep_sha224_mgf1_sha1_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptPrecomputedContract` and `decryptContract` of
//! `VG.Spec.Mgf1.sha224` and `VG.Spec.Mgf1.sha1`), for each implementation
//! of the hash functions' compression functions
//! (`Sha224Backend`, `Sha1Backend`) and of the RSA operation (`crate::rsa::Backend`).

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

use crate::arch::rsa_oaep_sha224_mgf1_sha1::*;
use crate::hashes::sha1::Sha1Backend;
use crate::hashes::sha224::Sha224Backend;

super::oaep_pair!(28, Sha224Backend, Sha1Backend {
    (Scalar, Scalar) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed [],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt [],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_CRT_IFMA_FEATURES],
        decrypt_umaal: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_umaal [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_UMAAL_FEATURES],
        encrypt_umaal: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_umaal [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_UMAAL_FEATURES],
    },
    #[cfg(target_arch = "x86")]
    (ShaNi, ShaNi) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha256_shani_sha1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA256_SHANI_SHA1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha256_shani_sha1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA256_SHANI_SHA1_SHANI_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    (ShaNi, ShaNi) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_MGF1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_MGF1_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani_mgf1_shani_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_MGF1_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani_mgf1_shani_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_MGF1_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_MGF1_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_mgf1_shani_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_MGF1_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    (Avx2, Scalar) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    (Sha2, Sha2) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_sha2_mgf1_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHA2_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2_mgf1_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHA2_MGF1_SHA2_FEATURES],
    },
} never {
    // SHA-1's and SHA-224's `_shani` variants need the same features
    // (`sha` and `ssse3`; on AArch64, their `_sha2` ones `sha2`), and
    // SHA-224's `_avx2` is chosen only without them: no CPU selects these
    // pairs (`backend_features` checks it).
    #[cfg(target_arch = "x86")]
    (Scalar, ShaNi) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA1_SHANI_FEATURES],
    },
    #[cfg(target_arch = "x86")]
    (ShaNi, Scalar) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha256_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA256_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha256_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA256_SHANI_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    (Scalar, ShaNi) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_MGF1_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_mgf1_shani_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_mgf1_shani_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_MGF1_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_shani_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_MGF1_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    (ShaNi, Scalar) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_shani_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_shani_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "x86_64")]
    (Avx2, ShaNi) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_MGF1_SHANI_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_MGF1_SHANI_FEATURES],
        encrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2_mgf1_shani_rsa_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_MGF1_SHANI_RSA_ADX_FEATURES],
        encrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_avx2_mgf1_shani_rsa_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_AVX2_MGF1_SHANI_RSA_IFMA_FEATURES],
        decrypt_adx: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_adx [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_MGF1_SHANI_CRT_ADX_FEATURES],
        decrypt_ifma: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_avx2_mgf1_shani_crt_ifma [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_AVX2_MGF1_SHANI_CRT_IFMA_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    (Scalar, Sha2) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_mgf1_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_MGF1_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_mgf1_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_MGF1_SHA2_FEATURES],
    },
    #[cfg(target_arch = "aarch64")]
    (Sha2, Scalar) => {
        encrypt: vg_rsa_oaep_sha224_mgf1_sha1_encrypt_precomputed_sha224_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_ENCRYPT_PRECOMPUTED_SHA224_SHA2_FEATURES],
        decrypt: vg_rsa_oaep_sha224_mgf1_sha1_decrypt_sha224_sha2 [VG_RSA_OAEP_SHA224_MGF1_SHA1_DECRYPT_SHA224_SHA2_FEATURES],
    },
});
