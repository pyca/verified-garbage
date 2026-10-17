//! The verified `vg_ecdsa_<curve>_rfc6979_sign` of AArch64, for each tier of
//! the hash functions ([`Tier`]): the baseline's, `_hash_sha2` and
//! `_hash_sha2_sha3`.

#![cfg(target_arch = "aarch64")]

use super::rfc6979::SignFn;
use crate::arch::ecdsa_brainpoolp256r1_rfc6979::{
    VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_brainpoolp256r1_rfc6979_sign, vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_sha2, vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_brainpoolp384r1_rfc6979::{
    VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_brainpoolp384r1_rfc6979_sign, vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_sha2, vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_brainpoolp512r1_rfc6979::{
    VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_brainpoolp512r1_rfc6979_sign, vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_sha2, vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_p192_rfc6979::{
    VG_ECDSA_P192_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_P192_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_p192_rfc6979_sign, vg_ecdsa_p192_rfc6979_sign_hash_sha2, vg_ecdsa_p192_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_p224_rfc6979::{
    VG_ECDSA_P224_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_P224_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_p224_rfc6979_sign, vg_ecdsa_p224_rfc6979_sign_hash_sha2, vg_ecdsa_p224_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_p256_rfc6979::{
    VG_ECDSA_P256_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_P256_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_p256_rfc6979_sign, vg_ecdsa_p256_rfc6979_sign_hash_sha2, vg_ecdsa_p256_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_p384_rfc6979::{
    VG_ECDSA_P384_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_P384_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_p384_rfc6979_sign, vg_ecdsa_p384_rfc6979_sign_hash_sha2, vg_ecdsa_p384_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_p521_rfc6979::{
    VG_ECDSA_P521_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_P521_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_p521_rfc6979_sign, vg_ecdsa_p521_rfc6979_sign_hash_sha2, vg_ecdsa_p521_rfc6979_sign_hash_sha2_sha3,
};
use crate::arch::ecdsa_secp256k1_rfc6979::{
    VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHA2_FEATURES, VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
    vg_ecdsa_secp256k1_rfc6979_sign, vg_ecdsa_secp256k1_rfc6979_sign_hash_sha2, vg_ecdsa_secp256k1_rfc6979_sign_hash_sha2_sha3,
};
use crate::cpu::Features;
use crate::hashes::tier::Tier;

/// The function of the tier of a CPU with the features `f`, with the CPU
/// features it needs: `base` (none), `sha2` or `sha2_sha3`.
fn choose<const Q: usize, const S: usize>(
    f: Features,
    base: SignFn<Q, S>,
    sha2: (SignFn<Q, S>, Features),
    sha2_sha3: (SignFn<Q, S>, Features),
) -> (SignFn<Q, S>, Features) {
    match Tier::select(f) {
        Tier::Base => (base, Features::all(&[])),
        Tier::Sha2 => sha2,
        Tier::Sha2Sha3 => sha2_sha3,
    }
}

/// `vg_ecdsa_p192_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn p192(f: Features) -> SignFn<24, 48> {
    p192_chosen(f).0
}

fn p192_chosen(f: Features) -> (SignFn<24, 48>, Features) {
    choose(
        f,
        vg_ecdsa_p192_rfc6979_sign,
        (
            vg_ecdsa_p192_rfc6979_sign_hash_sha2,
            VG_ECDSA_P192_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_p192_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_P192_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_p224_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn p224(f: Features) -> SignFn<28, 56> {
    p224_chosen(f).0
}

fn p224_chosen(f: Features) -> (SignFn<28, 56>, Features) {
    choose(
        f,
        vg_ecdsa_p224_rfc6979_sign,
        (
            vg_ecdsa_p224_rfc6979_sign_hash_sha2,
            VG_ECDSA_P224_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_p224_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_P224_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_p256_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn p256(f: Features) -> SignFn<32, 64> {
    p256_chosen(f).0
}

fn p256_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    choose(
        f,
        vg_ecdsa_p256_rfc6979_sign,
        (
            vg_ecdsa_p256_rfc6979_sign_hash_sha2,
            VG_ECDSA_P256_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_p256_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_P256_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_p384_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn p384(f: Features) -> SignFn<48, 96> {
    p384_chosen(f).0
}

fn p384_chosen(f: Features) -> (SignFn<48, 96>, Features) {
    choose(
        f,
        vg_ecdsa_p384_rfc6979_sign,
        (
            vg_ecdsa_p384_rfc6979_sign_hash_sha2,
            VG_ECDSA_P384_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_p384_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_P384_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_p521_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn p521(f: Features) -> SignFn<66, 132> {
    p521_chosen(f).0
}

fn p521_chosen(f: Features) -> (SignFn<66, 132>, Features) {
    choose(
        f,
        vg_ecdsa_p521_rfc6979_sign,
        (
            vg_ecdsa_p521_rfc6979_sign_hash_sha2,
            VG_ECDSA_P521_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_p521_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_P521_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_brainpoolp256r1_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn brainpoolp256r1(f: Features) -> SignFn<32, 64> {
    brainpoolp256r1_chosen(f).0
}

fn brainpoolp256r1_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    choose(
        f,
        vg_ecdsa_brainpoolp256r1_rfc6979_sign,
        (
            vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_sha2,
            VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_brainpoolp256r1_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_BRAINPOOLP256R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_brainpoolp384r1_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn brainpoolp384r1(f: Features) -> SignFn<48, 96> {
    brainpoolp384r1_chosen(f).0
}

fn brainpoolp384r1_chosen(f: Features) -> (SignFn<48, 96>, Features) {
    choose(
        f,
        vg_ecdsa_brainpoolp384r1_rfc6979_sign,
        (
            vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_sha2,
            VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_brainpoolp384r1_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_BRAINPOOLP384R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_brainpoolp512r1_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn brainpoolp512r1(f: Features) -> SignFn<64, 128> {
    brainpoolp512r1_chosen(f).0
}

fn brainpoolp512r1_chosen(f: Features) -> (SignFn<64, 128>, Features) {
    choose(
        f,
        vg_ecdsa_brainpoolp512r1_rfc6979_sign,
        (
            vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_sha2,
            VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

/// `vg_ecdsa_secp256k1_rfc6979_sign` of a CPU with the features `f`.
pub(super) fn secp256k1(f: Features) -> SignFn<32, 64> {
    secp256k1_chosen(f).0
}

fn secp256k1_chosen(f: Features) -> (SignFn<32, 64>, Features) {
    choose(
        f,
        vg_ecdsa_secp256k1_rfc6979_sign,
        (
            vg_ecdsa_secp256k1_rfc6979_sign_hash_sha2,
            VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHA2_FEATURES,
        ),
        (
            vg_ecdsa_secp256k1_rfc6979_sign_hash_sha2_sha3,
            VG_ECDSA_SECP256K1_RFC6979_SIGN_HASH_SHA2_SHA3_FEATURES,
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each function chosen needs no CPU feature that the features it was
    /// chosen for lack: on every set of features.
    #[test]
    fn features() {
        for bits in 0..1u32 << crate::cpu::NAMES.len() {
            let f = Features(bits);
            assert!(f.contains(p192_chosen(f).1), "{bits:#b}");
            assert!(f.contains(p224_chosen(f).1), "{bits:#b}");
            assert!(f.contains(p256_chosen(f).1), "{bits:#b}");
            assert!(f.contains(p384_chosen(f).1), "{bits:#b}");
            assert!(f.contains(p521_chosen(f).1), "{bits:#b}");
            assert!(f.contains(brainpoolp256r1_chosen(f).1), "{bits:#b}");
            assert!(f.contains(brainpoolp384r1_chosen(f).1), "{bits:#b}");
            assert!(f.contains(brainpoolp512r1_chosen(f).1), "{bits:#b}");
            assert!(f.contains(secp256k1_chosen(f).1), "{bits:#b}");
        }
    }
}
