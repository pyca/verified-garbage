//! ECDSA over P-256: deterministic signatures with HMAC-SHA-256 or
//! HMAC-SHA-384 (`vg_ecdsa_p256_<hash>_sign`, which calls
//! `vg_ecdsa_p256_sign`), public keys (`vg_ec_p256_public_key`), and
//! verification (`vg_ecdsa_p256_verify`).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use super::{Error, P256, SignatureHash, SigningKey, sealed};
use crate::arch::ec_p256::vg_ec_p256_public_key;
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify;
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha256::vg_ecdsa_p256_sha256_sign_sha2;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256_sha256::{
    vg_ecdsa_p256_sha256_sign_avx2, vg_ecdsa_p256_sha256_sign_shani,
};
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign;
#[cfg(target_arch = "aarch64")]
use crate::arch::ecdsa_p256_sha384::vg_ecdsa_p256_sha384_sign_sha3;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256_sha384::{
    vg_ecdsa_p256_sha384_sign_avx2, vg_ecdsa_p256_sha384_sign_shani,
};
use crate::hashes::sha256::{Sha256, Sha256Backend};
use crate::hashes::sha384::{Sha384, Sha384Backend};
use crate::zeroize::zeroize;

impl SigningKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        let mut out = [0; 65];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 65 bytes, `self.d`
        // for reads of 32 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p256_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// A verified `vg_ecdsa_p256_<hash>_sign`, for a hash of `N` bytes.
#[cfg(target_arch = "x86_64")]
type SignFn<const N: usize> = unsafe extern "sysv64" fn(
    *mut [u8; 64],
    *const [u8; 32],
    *const [u8; N],
    *mut [u64; 1024],
) -> u32;
/// A verified `vg_ecdsa_p256_<hash>_sign`, for a hash of `N` bytes.
#[cfg(target_arch = "aarch64")]
type SignFn<const N: usize> =
    unsafe extern "C" fn(*mut [u8; 64], *const [u8; 32], *const [u8; N], *mut [u64; 1024]) -> u32;

/// The signature `r ‖ s` of `digest` with the key `d`, by `sign`.
///
/// # Safety
///
/// `sign` needs no CPU feature that this CPU lacks.
unsafe fn sign_with<const N: usize>(
    sign: SignFn<N>,
    d: &[u8; 32],
    digest: &[u8; N],
) -> Result<[u8; 64], Error> {
    let mut out = [0; 64];
    let mut scratch = [0u64; 1024];
    // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` for reads
    // of 32, `digest` for reads of `N` and `scratch` for reads and writes of
    // 8192; `out` and `scratch` are distinct objects from each other and the
    // others, so none overlaps another or the call's stack frame, and, as
    // Rust objects, none wraps around the address space. The caller
    // guarantees the CPU features `sign` needs.
    let ok = unsafe { sign(&mut out, d, digest, &mut scratch) };
    zeroize(&mut scratch);
    if ok == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidKey)
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 32
/// bytes are `e`.
fn verify_with(q: &[u8; 65], e: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32, `signature` of
    // 64 and `scratch` for reads and writes of 8192; `scratch` is a distinct
    // object from the others, so it overlaps neither them nor the call's
    // stack frame, and, as Rust objects, none wraps around the address
    // space.
    let ok = unsafe { vg_ecdsa_p256_verify(q, e, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

impl sealed::Functions<P256> for Sha256 {
    fn sign(d: &[u8; 32], digest: &[u8; 32]) -> Result<[u8; 64], Error> {
        let sign = match Sha256Backend::select(crate::cpu::detected()) {
            Sha256Backend::Scalar => vg_ecdsa_p256_sha256_sign,
            #[cfg(target_arch = "aarch64")]
            Sha256Backend::Sha2 => vg_ecdsa_p256_sha256_sign_sha2,
            #[cfg(target_arch = "x86_64")]
            Sha256Backend::ShaNi => vg_ecdsa_p256_sha256_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha256Backend::Avx2 => vg_ecdsa_p256_sha256_sign_avx2,
        };
        // SAFETY: `sign` needs no CPU feature that the implementation of
        // SHA-256 selected for this CPU does not.
        unsafe { sign_with(sign, d, digest) }
    }

    fn verify(q: &[u8; 65], digest: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
        verify_with(q, digest, signature)
    }
}

impl SignatureHash<P256> for Sha256 {}

impl sealed::Functions<P256> for Sha384 {
    fn sign(d: &[u8; 32], digest: &[u8; 48]) -> Result<[u8; 64], Error> {
        let sign = match Sha384Backend::select(crate::cpu::detected()) {
            Sha384Backend::Scalar => vg_ecdsa_p256_sha384_sign,
            #[cfg(target_arch = "aarch64")]
            Sha384Backend::Sha3 => vg_ecdsa_p256_sha384_sign_sha3,
            #[cfg(target_arch = "x86_64")]
            Sha384Backend::ShaNi => vg_ecdsa_p256_sha384_sign_shani,
            #[cfg(target_arch = "x86_64")]
            Sha384Backend::Avx2 => vg_ecdsa_p256_sha384_sign_avx2,
        };
        // SAFETY: `sign` needs no CPU feature that the implementation of
        // SHA-384 selected for this CPU does not.
        unsafe { sign_with(sign, d, digest) }
    }

    /// `e` is the leftmost 256 bits of the hash (FIPS 186-5 §6.4.2), its
    /// first 32 bytes.
    fn verify(q: &[u8; 65], digest: &[u8; 48], signature: &[u8; 64]) -> Result<(), Error> {
        let (e, _) = digest.split_first_chunk::<32>().unwrap();
        verify_with(q, e, signature)
    }
}

impl SignatureHash<P256> for Sha384 {}
