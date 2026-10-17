//! RSASSA-PSS on x86-64 with the hash functions as arguments:
//! `vg_rsa_pss_sign` and `vg_rsa_pss_verify_precomputed` (contracts
//! `VG.Spec.RsaPss.signAnyContract` and `VG.Spec.RsaPss.verifyAnyContract`),
//! which take the hash value's hash function and MGF1's by their numbers
//! (`VG.Spec.HashId.mgf1`, [`Hash::id`]), for each tier of the hash
//! functions' implementations ([`Tier`]) and each implementation of the RSA
//! operation ([`Backend`]).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use super::{Hash, public_scratch_words, scratch_words};
use crate::arch::rsa_pss::{
    VG_RSA_PSS_SIGN_CRT_ADX_FEATURES, VG_RSA_PSS_SIGN_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SIGN_HASH_AVX2_CRT_ADX_FEATURES, VG_RSA_PSS_SIGN_HASH_AVX2_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SIGN_HASH_AVX2_FEATURES, VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_CRT_ADX_FEATURES,
    VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_CRT_IFMA_FEATURES, VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_FEATURES,
    VG_RSA_PSS_SIGN_HASH_SHANI_CRT_ADX_FEATURES, VG_RSA_PSS_SIGN_HASH_SHANI_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SIGN_HASH_SHANI_FEATURES, VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_CRT_ADX_FEATURES,
    VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_CRT_IFMA_FEATURES,
    VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_FEATURES, VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_AVX2_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_AVX2_RSA_ADX_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_AVX2_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_AVX2_RSA_ADX_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_RSA_ADX_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_SHA512_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_SHA512_RSA_ADX_FEATURES,
    VG_RSA_PSS_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES, vg_rsa_pss_sign, vg_rsa_pss_sign_crt_adx,
    vg_rsa_pss_sign_crt_ifma, vg_rsa_pss_sign_hash_avx2, vg_rsa_pss_sign_hash_avx2_crt_adx,
    vg_rsa_pss_sign_hash_avx2_crt_ifma, vg_rsa_pss_sign_hash_shani,
    vg_rsa_pss_sign_hash_shani_avx2, vg_rsa_pss_sign_hash_shani_avx2_crt_adx,
    vg_rsa_pss_sign_hash_shani_avx2_crt_ifma, vg_rsa_pss_sign_hash_shani_crt_adx,
    vg_rsa_pss_sign_hash_shani_crt_ifma, vg_rsa_pss_sign_hash_shani_sha512,
    vg_rsa_pss_sign_hash_shani_sha512_crt_adx, vg_rsa_pss_sign_hash_shani_sha512_crt_ifma,
    vg_rsa_pss_verify_precomputed, vg_rsa_pss_verify_precomputed_hash_avx2,
    vg_rsa_pss_verify_precomputed_hash_avx2_rsa_adx, vg_rsa_pss_verify_precomputed_hash_shani,
    vg_rsa_pss_verify_precomputed_hash_shani_avx2,
    vg_rsa_pss_verify_precomputed_hash_shani_avx2_rsa_adx,
    vg_rsa_pss_verify_precomputed_hash_shani_rsa_adx,
    vg_rsa_pss_verify_precomputed_hash_shani_sha512,
    vg_rsa_pss_verify_precomputed_hash_shani_sha512_rsa_adx, vg_rsa_pss_verify_precomputed_rsa_adx,
};
use crate::cpu::Features;
use crate::hashes::tier::Tier;
use crate::rsa::{Backend, PrivateKey, PublicKey};

/// `vg_rsa_pss_sign`'s signature.
type SignFn = unsafe extern "sysv64" fn(
    *mut u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *mut u64,
    usize,
    usize,
    usize,
) -> u32;

/// `vg_rsa_pss_verify_precomputed`'s signature.
type VerifyFn = unsafe extern "sysv64" fn(
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    u32,
    usize,
    *mut u64,
    usize,
    *const u64,
    usize,
    usize,
    usize,
) -> u32;

/// For each tier, its `sign` for each RSA backend and its `verify` for
/// the baseline public-key operation and the ADX one, with the CPU
/// features each needs: `functions(f)`, those of a CPU with the features
/// `f`, and the features they need.
macro_rules! tiers {
    ($(
        $tier:ident => {
            sign: [$s:path [$($sr:path),*], $sa:path [$($sar:path),*], $si:path [$($sir:path),*]],
            verify: [$v:path [$($vr:path),*], $va:path [$($var:path),*]] $(,)?
        }
    ),* $(,)?) => {
        /// The functions a CPU with the features `f` runs best, each with
        /// the features it needs.
        fn functions(f: Features) -> ((SignFn, Features), (VerifyFn, Features)) {
            let rsa = Backend::select(f);
            match Tier::select(f) {
                $(
                    Tier::$tier => (
                        match rsa {
                            Backend::Baseline => ($s as SignFn, Features::all(&[$($sr),*])),
                            Backend::Adx => ($sa as SignFn, Features::all(&[$($sar),*])),
                            Backend::Ifma => ($si as SignFn, Features::all(&[$($sir),*])),
                        },
                        match rsa {
                            Backend::Baseline => ($v as VerifyFn, Features::all(&[$($vr),*])),
                            Backend::Adx | Backend::Ifma => ($va as VerifyFn, Features::all(&[$($var),*])),
                        },
                    ),
                )*
            }
        }
    };
}

tiers! {
    Base => {
        sign: [
            vg_rsa_pss_sign [],
            vg_rsa_pss_sign_crt_adx [VG_RSA_PSS_SIGN_CRT_ADX_FEATURES],
            vg_rsa_pss_sign_crt_ifma [VG_RSA_PSS_SIGN_CRT_IFMA_FEATURES]
        ],
        verify: [
            vg_rsa_pss_verify_precomputed [],
            vg_rsa_pss_verify_precomputed_rsa_adx [VG_RSA_PSS_VERIFY_PRECOMPUTED_RSA_ADX_FEATURES]
        ],
    },
    Avx2 => {
        sign: [
            vg_rsa_pss_sign_hash_avx2 [VG_RSA_PSS_SIGN_HASH_AVX2_FEATURES],
            vg_rsa_pss_sign_hash_avx2_crt_adx [VG_RSA_PSS_SIGN_HASH_AVX2_CRT_ADX_FEATURES],
            vg_rsa_pss_sign_hash_avx2_crt_ifma [VG_RSA_PSS_SIGN_HASH_AVX2_CRT_IFMA_FEATURES]
        ],
        verify: [
            vg_rsa_pss_verify_precomputed_hash_avx2 [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_AVX2_FEATURES],
            vg_rsa_pss_verify_precomputed_hash_avx2_rsa_adx [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_AVX2_RSA_ADX_FEATURES]
        ],
    },
    ShaNi => {
        sign: [
            vg_rsa_pss_sign_hash_shani [VG_RSA_PSS_SIGN_HASH_SHANI_FEATURES],
            vg_rsa_pss_sign_hash_shani_crt_adx [VG_RSA_PSS_SIGN_HASH_SHANI_CRT_ADX_FEATURES],
            vg_rsa_pss_sign_hash_shani_crt_ifma [VG_RSA_PSS_SIGN_HASH_SHANI_CRT_IFMA_FEATURES]
        ],
        verify: [
            vg_rsa_pss_verify_precomputed_hash_shani [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_FEATURES],
            vg_rsa_pss_verify_precomputed_hash_shani_rsa_adx [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_RSA_ADX_FEATURES]
        ],
    },
    ShaNiAvx2 => {
        sign: [
            vg_rsa_pss_sign_hash_shani_avx2 [VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_FEATURES],
            vg_rsa_pss_sign_hash_shani_avx2_crt_adx [VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_CRT_ADX_FEATURES],
            vg_rsa_pss_sign_hash_shani_avx2_crt_ifma [VG_RSA_PSS_SIGN_HASH_SHANI_AVX2_CRT_IFMA_FEATURES]
        ],
        verify: [
            vg_rsa_pss_verify_precomputed_hash_shani_avx2 [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_AVX2_FEATURES],
            vg_rsa_pss_verify_precomputed_hash_shani_avx2_rsa_adx [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_AVX2_RSA_ADX_FEATURES]
        ],
    },
    ShaNiSha512 => {
        sign: [
            vg_rsa_pss_sign_hash_shani_sha512 [VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_FEATURES],
            vg_rsa_pss_sign_hash_shani_sha512_crt_adx [VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_CRT_ADX_FEATURES],
            vg_rsa_pss_sign_hash_shani_sha512_crt_ifma [VG_RSA_PSS_SIGN_HASH_SHANI_SHA512_CRT_IFMA_FEATURES]
        ],
        verify: [
            vg_rsa_pss_verify_precomputed_hash_shani_sha512 [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_SHA512_FEATURES],
            vg_rsa_pss_verify_precomputed_hash_shani_sha512_rsa_adx [VG_RSA_PSS_VERIFY_PRECOMPUTED_HASH_SHANI_SHA512_RSA_ADX_FEATURES]
        ],
    },
}

/// `vg_rsa_pss_sign` for this CPU, on the key, the hash value of `hash`
/// (as long as its values), the salt, `mgf1_hash`, the modulus-long `out`
/// and the working space.
pub(super) fn sign(
    out: &mut [u8],
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt: &[u8],
    scratch: &mut [u64],
) -> u32 {
    assert!(
        digest.len() == hash.digest_len()
            && out.len() == key.n.len()
            && scratch.len() == scratch_words(key.n.len())
    );
    let ((f, _), _) = functions(crate::cpu::detected());
    // SAFETY: each pointer is valid for its length (`out` for writes,
    // `scratch` too), and none overlaps another or wraps around, as they
    // are distinct Rust allocations; `PrivateKey::from_crt` gives
    // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len` and `dq_len = q_len`;
    // `out_len = n_len`, `scratch_len = 16 n_len + 1056`, `hash` and
    // `mgf1_hash` are the numbers of hash functions of `hashIds` and
    // `digest_len` is `hash`'s length; and the CPU has the features of the
    // function `functions` chose.
    unsafe {
        f(
            out.as_mut_ptr(),
            out.len(),
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            key.p.as_ptr(),
            key.p.len(),
            key.q.as_ptr(),
            key.q.len(),
            key.dp.as_ptr(),
            key.dp.len(),
            key.dq.as_ptr(),
            key.dq.len(),
            key.qinv.as_ptr(),
            key.qinv.len(),
            digest.as_ptr(),
            digest.len(),
            salt.as_ptr(),
            salt.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            hash.id(),
            mgf1_hash.id(),
        )
    }
}

/// `vg_rsa_pss_verify_precomputed` for this CPU, on the key, the
/// modulus-long signature, the hash value of `hash` (as long as its values),
/// `mgf1_hash`, the salt length and whether any is allowed, and the working
/// space.
#[allow(clippy::too_many_arguments)]
pub(super) fn verify(
    key: &PublicKey,
    signature: &[u8],
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_len: usize,
    any: u32,
    scratch: &mut [u64],
) -> u32 {
    assert!(
        digest.len() == hash.digest_len()
            && signature.len() == key.n.len()
            && scratch.len() == public_scratch_words(key.n.len())
    );
    let pre = key.pre(scratch);
    let (_, (f, _)) = functions(crate::cpu::detected());
    // SAFETY: each pointer is valid for its length (`scratch` for writes),
    // and none overlaps another or wraps around, as they are distinct Rust
    // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024` and
    // `1 ≤ e_len ≤ 5 ≤ n_len`; `sig_len = n_len`, `scratch_len =
    // 8 ⌈n_len / 8⌉ + 1072`, `hash` and `mgf1_hash` are the numbers of hash
    // functions of `hashIds` and `digest_len` is `hash`'s length; and the CPU
    // has the features of the function `functions` chose. `pre` holds the
    // verified precomputed values for `key.n`, with their required length.
    unsafe {
        f(
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            digest.as_ptr(),
            digest.len(),
            signature.as_ptr(),
            signature.len(),
            any,
            salt_len,
            scratch.as_mut_ptr(),
            scratch.len(),
            pre.as_ptr(),
            pre.len(),
            hash.id(),
            mgf1_hash.id(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::functions;
    use crate::cpu::Features;

    /// Each function needs no CPU feature that the implementations it calls
    /// are not selected for: on every set of features.
    #[test]
    fn backend_features() {
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            let ((_, s), (_, v)) = functions(f);
            assert!(f.contains(s) && f.contains(v));
        }
    }
}
