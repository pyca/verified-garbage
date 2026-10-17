//! ECDSA over brainpoolP384r1: deterministic signatures with HMAC with any of
//! SHA-1 and the SHA-2 functions on x86-64
//! (`vg_ecdsa_brainpoolp384r1_rfc6979_sign`), and with HMAC-SHA-384 elsewhere
//! (`vg_ecdsa_brainpoolp384r1_sha384_sign`), each of which calls
//! `vg_ecdsa_brainpoolp384r1_sign`; public keys
//! (`vg_ec_brainpoolp384r1_public_key`), and verification
//! (`vg_ecdsa_brainpoolp384r1_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{BrainpoolP384r1, Error, SigningKey};
#[cfg(not(target_arch = "x86_64"))]
use super::{SignatureHash, sealed};
use crate::arch::ec_brainpoolp384r1::vg_ec_brainpoolp384r1_public_key;
use crate::arch::ecdsa_brainpoolp384r1::vg_ecdsa_brainpoolp384r1_verify;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::ecdsa_brainpoolp384r1_sha384::vg_ecdsa_brainpoolp384r1_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_brainpoolp384r1_sha384::vg_ecdsa_brainpoolp384r1_sha384_sign_sha3;
#[cfg(not(target_arch = "x86_64"))]
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl SigningKey<BrainpoolP384r1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 48 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 97], Error> {
        let mut out = [0; 97];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 97 bytes, `self.d`
        // for reads of 48 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_brainpoolp384r1_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 48
/// bytes are `e`.
fn verify_with(q: &[u8; 97], e: &[u8; 48], signature: &[u8; 96]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 97 bytes, `e` of 48, `signature` of
    // 96 and `scratch` for reads and writes of 8192; `scratch` is a distinct
    // object from the others, so it overlaps neither them nor the call's
    // stack frame, and, as Rust objects, none wraps around the address space.
    let ok = unsafe { vg_ecdsa_brainpoolp384r1_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl sealed::Functions<BrainpoolP384r1> for Sha384 {
    fn sign(d: &[u8; 48], digest: &[u8; 48]) -> Result<[u8; 96], Error> {
        let sign = match Sha384Backend::select(crate::cpu::detected()) {
            Sha384Backend::Scalar => vg_ecdsa_brainpoolp384r1_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            Sha384Backend::Sha3 => vg_ecdsa_brainpoolp384r1_sha384_sign_sha3,
        };
        let mut out = [0; 96];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 96 bytes, `d` and
        // `digest` for reads of 48 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-384 selected
        // for this CPU does not.
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
impl SignatureHash<BrainpoolP384r1> for Sha384 {}

#[cfg(target_arch = "x86_64")]
super::rfc6979::any_hash!(
    BrainpoolP384r1,
    super::rfc6979_x86_64::brainpoolp384r1,
    verify_with,
    0
);
