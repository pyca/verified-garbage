//! ECDSA over P-192: deterministic signatures with HMAC with any of SHA-1 and
//! the SHA-2 functions on x86-64 (`vg_ecdsa_p192_rfc6979_sign`), and with
//! HMAC-SHA-256 elsewhere (`vg_ecdsa_p192_sha256_sign`), each of which calls
//! `vg_ecdsa_p192_sign`; public keys (`vg_ec_p192_public_key`), and
//! verification (`vg_ecdsa_p192_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P192, SigningKey};
#[cfg(not(target_arch = "x86_64"))]
use super::{SignatureHash, sealed};
use crate::arch::ec_p192::vg_ec_p192_public_key;
use crate::arch::ecdsa_p192::vg_ecdsa_p192_verify;
#[cfg(not(target_arch = "x86_64"))]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_sha2;
#[cfg(target_arch = "x86")]
use crate::arch::ecdsa_p192_sha256::vg_ecdsa_p192_sha256_sign_shani;
#[cfg(not(target_arch = "x86_64"))]
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::zeroize::zeroize;

impl SigningKey<P192> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 24 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 49], Error> {
        let mut out = [0; 49];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 49 bytes, `self.d`
        // for reads of 24 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p192_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 24
/// bytes are `e`.
fn verify_with(q: &[u8; 49], e: &[u8; 24], signature: &[u8; 48]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 49 bytes, `e` of 24, `signature` of
    // 48 and `scratch` for reads and writes of 8192; `scratch` is a distinct
    // object from the others, so it overlaps neither them nor the call's
    // stack frame, and, as Rust objects, none wraps around the address space.
    let ok = unsafe { vg_ecdsa_p192_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl sealed::Functions<P192> for Sha256 {
    fn sign(d: &[u8; 24], digest: &[u8; 32]) -> Result<[u8; 48], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_p192_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            Sha256Backend::Sha2 => vg_ecdsa_p192_sha256_sign_sha2,
            #[cfg(target_arch = "x86")]
            Sha256Backend::ShaNi => vg_ecdsa_p192_sha256_sign_shani,
        };
        let mut out = [0; 48];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 48 bytes, `d` for
        // reads of 24, `digest` of 32 and `scratch` for reads and writes of
        // 8192; `out` and `scratch` are distinct objects from each other and
        // the others, so none overlaps another or the call's stack frame,
        // and, as Rust objects, none wraps around the address space. `sign`
        // needs no CPU feature that the implementation of SHA-256 selected
        // for this CPU does not.
        let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    fn verify(q: &[u8; 49], digest: &[u8; 32], signature: &[u8; 48]) -> Result<(), Error> {
        verify_with(q, digest[..24].try_into().unwrap(), signature)
    }
}

#[cfg(not(target_arch = "x86_64"))]
impl SignatureHash<P192> for Sha256 {}

#[cfg(target_arch = "x86_64")]
super::rfc6979::any_hash!(P192, super::rfc6979_x86_64::p192, verify_with, 0);
