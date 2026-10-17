//! The choice, on x86-64, among each curve's `vg_ecdsa_<curve>_rfc6979_sign`
//! functions ([`rfc6979`](super::rfc6979)): of the tier of implementations of
//! the hash functions this CPU runs ([`Tier`]) and, for P-256, P-384 and
//! P-521, of its multiplications (`_adx`).

#![cfg(target_arch = "x86_64")]

use super::rfc6979::SignFn;
use crate::cpu::Features;
use crate::hashes::tier::Tier;

/// A function and the CPU features it needs, for each tier: `base` the
/// baseline's, then those of AVX2, the SHA extensions, the SHA extensions
/// and AVX2, and the SHA extensions and SHA512.
type Tiers<const Q: usize, const S: usize> = [(SignFn<Q, S>, Features); 5];

/// The function of `tiers` for the tier of a CPU with the features `f`.
fn choose<const Q: usize, const S: usize>(
    f: Features,
    tiers: Tiers<Q, S>,
) -> (SignFn<Q, S>, Features) {
    tiers[match Tier::select(f) {
        Tier::Base => 0,
        Tier::Avx2 => 1,
        Tier::ShaNi => 2,
        Tier::ShaNiAvx2 => 3,
        Tier::ShaNiSha512 => 4,
    }]
}

/// `vg_ecdsa_p192_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn p192_chosen(f: Features) -> (SignFn<24, 48>, Features) {
    use crate::arch::ecdsa_p192_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_p192_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_p192_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_P192_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_p192_rfc6979_sign_hash_shani,
                a::VG_ECDSA_P192_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_p192_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_P192_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_p192_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_P192_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_p192_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn p192(f: Features) -> SignFn<24, 48> {
    p192_chosen(f).0
}

/// `vg_ecdsa_p224_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn p224_chosen(f: Features) -> (SignFn<28, 56>, Features) {
    use crate::arch::ecdsa_p224_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_p224_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_p224_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_P224_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_p224_rfc6979_sign_hash_shani,
                a::VG_ECDSA_P224_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_p224_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_P224_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_p224_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_P224_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_p224_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn p224(f: Features) -> SignFn<28, 56> {
    p224_chosen(f).0
}

/// `vg_ecdsa_p256_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn p256_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    use crate::arch::ecdsa_p256_rfc6979 as a;

    match crate::ec::p256::Mul::select(f) {
        crate::ec::p256::Mul::Baseline => choose(
            f,
            [
                (a::vg_ecdsa_p256_rfc6979_sign, Features(0)),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_avx2,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani_avx2,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani_sha512,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
                ),
            ],
        ),
        crate::ec::p256::Mul::Adx => choose(
            f,
            [
                (
                    a::vg_ecdsa_p256_rfc6979_sign_adx,
                    a::VG_ECDSA_P256_RFC6979_SIGN_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_avx2_adx,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani_adx,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani_avx2_adx,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p256_rfc6979_sign_hash_shani_sha512_adx,
                    a::VG_ECDSA_P256_RFC6979_SIGN_HASH_SHANI_SHA512_ADX_FEATURES,
                ),
            ],
        ),
    }
}

/// `vg_ecdsa_p256_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn p256(f: Features) -> SignFn<32, 64> {
    p256_chosen(f).0
}

/// `vg_ecdsa_p384_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn p384_chosen(f: Features) -> (SignFn<48, 96>, Features) {
    use crate::arch::ecdsa_p384_rfc6979 as a;

    match crate::ec::p384::Mul::select(f) {
        crate::ec::p384::Mul::Baseline => choose(
            f,
            [
                (a::vg_ecdsa_p384_rfc6979_sign, Features(0)),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_avx2,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
                ),
            ],
        ),
        crate::ec::p384::Mul::Adx => choose(
            f,
            [
                (
                    a::vg_ecdsa_p384_rfc6979_sign_adx,
                    a::VG_ECDSA_P384_RFC6979_SIGN_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_avx2_adx,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani_adx,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2_adx,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512_adx,
                    a::VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_ADX_FEATURES,
                ),
            ],
        ),
    }
}

/// `vg_ecdsa_p384_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn p384(f: Features) -> SignFn<48, 96> {
    p384_chosen(f).0
}

/// `vg_ecdsa_p521_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn p521_chosen(f: Features) -> (SignFn<66, 132>, Features) {
    use crate::arch::ecdsa_p521_rfc6979 as a;

    match crate::ec::p521::Mul::select(f) {
        crate::ec::p521::Mul::Baseline => choose(
            f,
            [
                (a::vg_ecdsa_p521_rfc6979_sign, Features(0)),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_avx2,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani_avx2,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani_sha512,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
                ),
            ],
        ),
        crate::ec::p521::Mul::Adx => choose(
            f,
            [
                (
                    a::vg_ecdsa_p521_rfc6979_sign_adx,
                    a::VG_ECDSA_P521_RFC6979_SIGN_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_avx2_adx,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani_adx,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani_avx2_adx,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_AVX2_ADX_FEATURES,
                ),
                (
                    a::vg_ecdsa_p521_rfc6979_sign_hash_shani_sha512_adx,
                    a::VG_ECDSA_P521_RFC6979_SIGN_HASH_SHANI_SHA512_ADX_FEATURES,
                ),
            ],
        ),
    }
}

/// `vg_ecdsa_p521_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn p521(f: Features) -> SignFn<66, 132> {
    p521_chosen(f).0
}

/// `vg_ecdsa_secp256k1_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn secp256k1_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    use crate::arch::ecdsa_secp256k1_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_secp256k1_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_secp256k1_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_secp256k1_rfc6979_sign_hash_shani,
                a::VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_secp256k1_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_secp256k1_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_secp256k1_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn secp256k1(f: Features) -> SignFn<32, 64> {
    secp256k1_chosen(f).0
}

/// `vg_ecdsa_brainpoolp256r1_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn brainpoolp256r1_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    use crate::arch::ecdsa_brainpoolp256r1_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_brainpoolp256r1_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_shani,
                a::VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_brainpoolp256r1_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn brainpoolp256r1(f: Features) -> SignFn<32, 64> {
    brainpoolp256r1_chosen(f).0
}

/// `vg_ecdsa_brainpoolp384r1_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn brainpoolp384r1_chosen(f: Features) -> (SignFn<48, 96>, Features) {
    use crate::arch::ecdsa_brainpoolp384r1_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_brainpoolp384r1_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_shani,
                a::VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_brainpoolp384r1_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn brainpoolp384r1(f: Features) -> SignFn<48, 96> {
    brainpoolp384r1_chosen(f).0
}

/// `vg_ecdsa_brainpoolp512r1_rfc6979_sign` for a CPU with the features `f`, and the
/// features it needs.
fn brainpoolp512r1_chosen(f: Features) -> (SignFn<64, 128>, Features) {
    use crate::arch::ecdsa_brainpoolp512r1_rfc6979 as a;

    choose(
        f,
        [
            (a::vg_ecdsa_brainpoolp512r1_rfc6979_sign, Features(0)),
            (
                a::vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_avx2,
                a::VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani,
                a::VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_avx2,
                a::VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            ),
            (
                a::vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_sha512,
                a::VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
            ),
        ],
    )
}

/// `vg_ecdsa_brainpoolp512r1_rfc6979_sign` for a CPU with the features `f`.
pub(super) fn brainpoolp512r1(f: Features) -> SignFn<64, 128> {
    brainpoolp512r1_chosen(f).0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cpu::NAMES;

    /// Each function chosen needs no CPU feature that the CPU it is chosen
    /// for lacks: on every set of features.
    #[test]
    fn features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            assert!(f.contains(p192_chosen(f).1), "p192 {bits:#b}");
            assert!(f.contains(p224_chosen(f).1), "p224 {bits:#b}");
            assert!(f.contains(p256_chosen(f).1), "p256 {bits:#b}");
            assert!(f.contains(p384_chosen(f).1), "p384 {bits:#b}");
            assert!(f.contains(p521_chosen(f).1), "p521 {bits:#b}");
            assert!(f.contains(secp256k1_chosen(f).1), "secp256k1 {bits:#b}");
            assert!(f.contains(brainpoolp256r1_chosen(f).1), "bp256 {bits:#b}");
            assert!(f.contains(brainpoolp384r1_chosen(f).1), "bp384 {bits:#b}");
            assert!(f.contains(brainpoolp512r1_chosen(f).1), "bp512 {bits:#b}");
        }
    }
}
