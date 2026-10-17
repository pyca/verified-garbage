//! ECDSA over P-384: deterministic signatures with HMAC with any of SHA-1
//! and the SHA-2 functions on x86-64 (`vg_ecdsa_p384_rfc6979_sign`), and
//! with HMAC-SHA-384 elsewhere (`vg_ecdsa_p384_sha384_sign`), each of which
//! calls `vg_ecdsa_p384_sign`; public keys (`vg_ec_p384_public_key`), and
//! verification (`vg_ecdsa_p384_verify`), each with BMI2 and ADX where the
//! CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P384, SigningKey};
#[cfg(not(target_arch = "x86_64"))]
use super::{SignatureHash, sealed};
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify_adx;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384_rfc6979::{
    vg_ecdsa_p384_rfc6979_sign, vg_ecdsa_p384_rfc6979_sign_adx,
    vg_ecdsa_p384_rfc6979_sign_hash_avx2, vg_ecdsa_p384_rfc6979_sign_hash_avx2_adx,
    vg_ecdsa_p384_rfc6979_sign_hash_shani, vg_ecdsa_p384_rfc6979_sign_hash_shani_adx,
    vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2, vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2_adx,
    vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512, vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512_adx,
};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p384_sha384::vg_ecdsa_p384_sha384_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::cpu::Features;
use crate::cpu::detected;
use crate::ec::p384::{Mul, public_key};
#[cfg(not(target_arch = "x86_64"))]
use crate::hashes::sha384::{Sha384, Sha384Backend};
#[cfg(target_arch = "x86_64")]
use crate::hashes::tier::Tier;
#[cfg(not(target_arch = "x86_64"))]
use crate::zeroize::zeroize;

impl SigningKey<P384> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 48 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 97], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 48
/// bytes are `e`.
fn verify_with(q: &[u8; 97], e: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 97 bytes, `e` of 48, `signature`
        // of 96 and `scratch` for reads and writes of 8192; `scratch` is a
        // distinct object from the others, so it overlaps neither them nor
        // the call's stack frame, and, as Rust objects, none wraps around
        // the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p384_verify(q, e, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p384_verify_adx(q, e, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl sealed::Functions<P384> for Sha384 {
    fn sign(d: &[u8; 48], digest: &[u8; 48]) -> Result<[u8; 96], Error> {
        let f = detected();
        let sign = match (Sha384Backend::select(f), Mul::select(f)) {
            (Sha384Backend::Scalar, Mul::Baseline) => vg_ecdsa_p384_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            (Sha384Backend::Sha3, Mul::Baseline) => vg_ecdsa_p384_sha384_sign_sha3,
        };
        let mut out = [0; 96];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 96 bytes, `d` and
        // `digest` for reads of 48 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-384 and the
        // multiplications selected for this CPU do not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 97], digest: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl SignatureHash<P384> for Sha384 {}

/// The signing function for a CPU with the features `f`: of its tier of
/// hash functions and its multiplications.
#[cfg(target_arch = "x86_64")]
fn sign_fn(f: Features) -> super::any::SignFn<48, 96> {
    match (Tier::select(f), Mul::select(f)) {
        (Tier::Base, Mul::Baseline) => vg_ecdsa_p384_rfc6979_sign,
        (Tier::Avx2, Mul::Baseline) => vg_ecdsa_p384_rfc6979_sign_hash_avx2,
        (Tier::ShaNi, Mul::Baseline) => vg_ecdsa_p384_rfc6979_sign_hash_shani,
        (Tier::ShaNiAvx2, Mul::Baseline) => vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2,
        (Tier::ShaNiSha512, Mul::Baseline) => vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512,
        (Tier::Base, Mul::Adx) => vg_ecdsa_p384_rfc6979_sign_adx,
        (Tier::Avx2, Mul::Adx) => vg_ecdsa_p384_rfc6979_sign_hash_avx2_adx,
        (Tier::ShaNi, Mul::Adx) => vg_ecdsa_p384_rfc6979_sign_hash_shani_adx,
        (Tier::ShaNiAvx2, Mul::Adx) => vg_ecdsa_p384_rfc6979_sign_hash_shani_avx2_adx,
        (Tier::ShaNiSha512, Mul::Adx) => vg_ecdsa_p384_rfc6979_sign_hash_shani_sha512_adx,
    }
}

#[cfg(target_arch = "x86_64")]
super::any::any_hash!(P384, sign_fn, verify_with, 0);

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::arch::ecdsa_p384_rfc6979::{
        VG_ECDSA_P384_RFC6979_SIGN_ADX_FEATURES, VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_ADX_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_ADX_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_ADX_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_ADX_FEATURES,
        VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
    };
    use crate::cpu::NAMES;

    /// The CPU features of the signature with the tier `t` and the
    /// multiplications `m`.
    fn required(t: Tier, m: Mul) -> Features {
        match (t, m) {
            (Tier::Base, Mul::Baseline) => Features(0),
            (Tier::Avx2, Mul::Baseline) => VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_FEATURES,
            (Tier::ShaNi, Mul::Baseline) => VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_FEATURES,
            (Tier::ShaNiAvx2, Mul::Baseline) => VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            (Tier::ShaNiSha512, Mul::Baseline) => {
                VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES
            }
            (Tier::Base, Mul::Adx) => VG_ECDSA_P384_RFC6979_SIGN_ADX_FEATURES,
            (Tier::Avx2, Mul::Adx) => VG_ECDSA_P384_RFC6979_SIGN_HASH_AVX2_ADX_FEATURES,
            (Tier::ShaNi, Mul::Adx) => VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_ADX_FEATURES,
            (Tier::ShaNiAvx2, Mul::Adx) => VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_AVX2_ADX_FEATURES,
            (Tier::ShaNiSha512, Mul::Adx) => {
                VG_ECDSA_P384_RFC6979_SIGN_HASH_SHANI_SHA512_ADX_FEATURES
            }
        }
    }

    /// Each signature needs no CPU feature that the tier and the
    /// multiplications are not selected for: on every set of features that
    /// selects them.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            let r = required(Tier::select(f), Mul::select(f));
            assert!(f.contains(r), "{bits:#b}");
        }
    }
}
