//! RSAES-OAEP with the hash functions as arguments: the verified
//! `vg_rsa_oaep_encrypt_precomputed` and `vg_rsa_oaep_decrypt` (contracts
//! `VG.Spec.RsaOaep.encryptAnyContract` and `decryptAnyContract`), which take
//! the label's hash function and MGF1's by their numbers
//! (`VG.Spec.HashId`, as [`Hash`](super::Hash) numbers them), for each tier
//! of implementations of the hash functions' compression functions
//! ([`Tier`]) and each implementation of the RSA operation
//! (`crate::rsa::Backend`).

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use crate::arch::rsa_oaep::*;
use crate::cpu::Features;
use crate::hashes::tier::Tier;
use crate::rsa::Backend;

/// The implementations of one tier, each with the generated constant of the
/// CPU features it needs (none for the baseline ISA's): encryption calling
/// RSA's baseline code (and on x86-64 its ADX code), and decryption calling
/// RSA's baseline code (and on x86-64 its ADX and AVX512_IFMA code).
struct TierFns {
    encrypt: (super::EncryptAnyFn, Features),
    #[cfg(target_arch = "x86_64")]
    encrypt_adx: (super::EncryptAnyFn, Features),
    decrypt: (super::DecryptAnyFn, Features),
    #[cfg(target_arch = "x86_64")]
    decrypt_adx: (super::DecryptAnyFn, Features),
    #[cfg(target_arch = "x86_64")]
    decrypt_ifma: (super::DecryptAnyFn, Features),
}

/// The functions of the tier `t`.
#[cfg(target_arch = "x86_64")]
fn tier(t: Tier) -> TierFns {
    match t {
        Tier::Base => TierFns {
            encrypt: (vg_rsa_oaep_encrypt_precomputed, Features::all(&[])),
            encrypt_adx: (
                vg_rsa_oaep_encrypt_precomputed_rsa_adx,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_RSA_ADX_FEATURES,
            ),
            decrypt: (vg_rsa_oaep_decrypt, Features::all(&[])),
            decrypt_adx: (
                vg_rsa_oaep_decrypt_crt_adx,
                VG_RSA_OAEP_DECRYPT_CRT_ADX_FEATURES,
            ),
            decrypt_ifma: (
                vg_rsa_oaep_decrypt_crt_ifma,
                VG_RSA_OAEP_DECRYPT_CRT_IFMA_FEATURES,
            ),
        },
        Tier::Avx2 => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_avx2,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_AVX2_FEATURES,
            ),
            encrypt_adx: (
                vg_rsa_oaep_encrypt_precomputed_hash_avx2_rsa_adx,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_AVX2_RSA_ADX_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_avx2,
                VG_RSA_OAEP_DECRYPT_HASH_AVX2_FEATURES,
            ),
            decrypt_adx: (
                vg_rsa_oaep_decrypt_hash_avx2_crt_adx,
                VG_RSA_OAEP_DECRYPT_HASH_AVX2_CRT_ADX_FEATURES,
            ),
            decrypt_ifma: (
                vg_rsa_oaep_decrypt_hash_avx2_crt_ifma,
                VG_RSA_OAEP_DECRYPT_HASH_AVX2_CRT_IFMA_FEATURES,
            ),
        },
        Tier::ShaNi => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_FEATURES,
            ),
            encrypt_adx: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani_rsa_adx,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_RSA_ADX_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_shani,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_FEATURES,
            ),
            decrypt_adx: (
                vg_rsa_oaep_decrypt_hash_shani_crt_adx,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_CRT_ADX_FEATURES,
            ),
            decrypt_ifma: (
                vg_rsa_oaep_decrypt_hash_shani_crt_ifma,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_CRT_IFMA_FEATURES,
            ),
        },
        Tier::ShaNiAvx2 => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani_avx2,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_AVX2_FEATURES,
            ),
            encrypt_adx: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani_avx2_rsa_adx,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_AVX2_RSA_ADX_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_shani_avx2,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_AVX2_FEATURES,
            ),
            decrypt_adx: (
                vg_rsa_oaep_decrypt_hash_shani_avx2_crt_adx,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_AVX2_CRT_ADX_FEATURES,
            ),
            decrypt_ifma: (
                vg_rsa_oaep_decrypt_hash_shani_avx2_crt_ifma,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_AVX2_CRT_IFMA_FEATURES,
            ),
        },
        Tier::ShaNiSha512 => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani_sha512,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_SHA512_FEATURES,
            ),
            encrypt_adx: (
                vg_rsa_oaep_encrypt_precomputed_hash_shani_sha512_rsa_adx,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHANI_SHA512_RSA_ADX_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_shani_sha512,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_SHA512_FEATURES,
            ),
            decrypt_adx: (
                vg_rsa_oaep_decrypt_hash_shani_sha512_crt_adx,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_SHA512_CRT_ADX_FEATURES,
            ),
            decrypt_ifma: (
                vg_rsa_oaep_decrypt_hash_shani_sha512_crt_ifma,
                VG_RSA_OAEP_DECRYPT_HASH_SHANI_SHA512_CRT_IFMA_FEATURES,
            ),
        },
    }
}

/// The functions of the tier `t`.
#[cfg(target_arch = "aarch64")]
fn tier(t: Tier) -> TierFns {
    match t {
        Tier::Base => TierFns {
            encrypt: (vg_rsa_oaep_encrypt_precomputed, Features::all(&[])),
            decrypt: (vg_rsa_oaep_decrypt, Features::all(&[])),
        },
        Tier::Sha2 => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_sha2,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHA2_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_sha2,
                VG_RSA_OAEP_DECRYPT_HASH_SHA2_FEATURES,
            ),
        },
        Tier::Sha2Sha3 => TierFns {
            encrypt: (
                vg_rsa_oaep_encrypt_precomputed_hash_sha2_sha3,
                VG_RSA_OAEP_ENCRYPT_PRECOMPUTED_HASH_SHA2_SHA3_FEATURES,
            ),
            decrypt: (
                vg_rsa_oaep_decrypt_hash_sha2_sha3,
                VG_RSA_OAEP_DECRYPT_HASH_SHA2_SHA3_FEATURES,
            ),
        },
    }
}

/// Encryption and decryption, each with the CPU features it needs, for the
/// implementations a CPU with the features `f` runs best: its tier's, with
/// its RSA backend (encryption's public-key operation is the ADX code's for
/// `Ifma` too).
fn chosen(
    f: Features,
) -> (
    (super::EncryptAnyFn, Features),
    (super::DecryptAnyFn, Features),
) {
    let t = tier(Tier::select(f));
    match Backend::select(f) {
        Backend::Baseline => (t.encrypt, t.decrypt),
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => (t.encrypt_adx, t.decrypt_adx),
        #[cfg(target_arch = "x86_64")]
        Backend::Ifma => (t.encrypt_adx, t.decrypt_ifma),
    }
}

/// The functions, `(encrypt, decrypt)`, for the implementations that a CPU
/// with the features `f` runs best.
pub(super) fn functions(f: Features) -> (super::EncryptAnyFn, super::DecryptAnyFn) {
    let ((encrypt, _), (decrypt, _)) = chosen(f);
    (encrypt, decrypt)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each function chosen needs no CPU feature that the implementations
    /// it calls were not chosen for: on every set of features.
    #[test]
    fn backend_features() {
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            let ((_, encrypt), (_, decrypt)) = chosen(f);
            assert!(f.contains(encrypt) && f.contains(decrypt), "{bits:#b}");
        }
    }
}
