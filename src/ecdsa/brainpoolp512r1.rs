//! ECDSA over brainpoolP512r1: deterministic signatures with HMAC with any of
//! SHA-1 and the SHA-2 functions on x86-64
//! (`vg_ecdsa_brainpoolp512r1_rfc6979_sign`), and with HMAC-SHA-512 elsewhere
//! (`vg_ecdsa_brainpoolp512r1_sha512_sign`), each of which calls
//! `vg_ecdsa_brainpoolp512r1_sign`; public keys
//! (`vg_ec_brainpoolp512r1_public_key`), and verification
//! (`vg_ecdsa_brainpoolp512r1_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{BrainpoolP512r1, Error, SigningKey};
#[cfg(not(target_arch = "x86_64"))]
use super::{SignatureHash, sealed};
use crate::arch::ec_brainpoolp512r1::vg_ec_brainpoolp512r1_public_key;
use crate::arch::ecdsa_brainpoolp512r1::vg_ecdsa_brainpoolp512r1_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_brainpoolp512r1_rfc6979::{
    vg_ecdsa_brainpoolp512r1_rfc6979_sign, vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_avx2,
    vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani,
    vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_avx2,
    vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_sha512,
};
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp512r1_sha512::vg_ecdsa_brainpoolp512r1_sha512_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::cpu::Features;
#[cfg(not(target_arch = "x86_64"))]
use crate::hashes::sha512::{Sha512, Sha512Backend};
#[cfg(target_arch = "x86_64")]
use crate::hashes::tier::Tier;
use crate::zeroize::zeroize;

impl SigningKey<BrainpoolP512r1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 64 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 129], Error> {
        let mut out = [0; 129];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 129 bytes, `self.d`
        // for reads of 64 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_brainpoolp512r1_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 64
/// bytes are `e`.
fn verify_with(q: &[u8; 129], e: &[u8; 64], signature: &[u8; 128]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 129 bytes, `e` of 64, `signature` of
    // 128 and `scratch` for reads and writes of 8192; `scratch` is a distinct
    // object from the others, so it overlaps neither them nor the call's
    // stack frame, and, as Rust objects, none wraps around the address space.
    let ok = unsafe { vg_ecdsa_brainpoolp512r1_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl sealed::Functions<BrainpoolP512r1> for Sha512 {
    fn sign(d: &[u8; 64], digest: &[u8; 64]) -> Result<[u8; 128], Error> {
        let sign = match Sha512Backend::select(crate::cpu::detected()) {
            Sha512Backend::Scalar => vg_ecdsa_brainpoolp512r1_sha512_sign,
            #[cfg(target_arch = "aarch64")]
            Sha512Backend::Sha3 => vg_ecdsa_brainpoolp512r1_sha512_sign_sha3,
        };
        let mut out = [0; 128];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 128 bytes, `d` and
        // `digest` for reads of 64 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-512 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 129], digest: &[u8; 64], signature: &[u8; 128]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl SignatureHash<BrainpoolP512r1> for Sha512 {}

/// The signing function for a CPU with the features `f`: of its tier of
/// hash functions.
#[cfg(target_arch = "x86_64")]
fn sign_fn(f: Features) -> super::any::SignFn<64, 128> {
    match Tier::select(f) {
        Tier::Base => vg_ecdsa_brainpoolp512r1_rfc6979_sign,
        Tier::Avx2 => vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_avx2,
        Tier::ShaNi => vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani,
        Tier::ShaNiAvx2 => vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_avx2,
        Tier::ShaNiSha512 => vg_ecdsa_brainpoolp512r1_rfc6979_sign_hash_shani_sha512,
    }
}

#[cfg(target_arch = "x86_64")]
super::any::any_hash!(BrainpoolP512r1, sign_fn, verify_with, 0);

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::arch::ecdsa_brainpoolp512r1_rfc6979::{
        VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_AVX2_FEATURES,
        VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
        VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_FEATURES,
        VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
    };
    use crate::cpu::NAMES;

    /// The CPU features of the signature with the tier `t`.
    fn required(t: Tier) -> Features {
        match t {
            Tier::Base => Features(0),
            Tier::Avx2 => VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_AVX2_FEATURES,
            Tier::ShaNi => VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_FEATURES,
            Tier::ShaNiAvx2 => VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_AVX2_FEATURES,
            Tier::ShaNiSha512 => VG_ECDSA_BRAINPOOLP512R1_RFC6979_SIGN_HASH_SHANI_SHA512_FEATURES,
        }
    }

    /// Each signature needs no CPU feature that the tier is not selected
    /// for: on every set of features that selects it.
    #[test]
    fn whole_algorithm_features() {
        for bits in 0..1u32 << NAMES.len() {
            let f = Features(bits);
            assert!(f.contains(required(Tier::select(f))), "{bits:#b}");
        }
    }
}
