//! ECDSA over P-256: deterministic signatures with HMAC-SHA-256 or
//! HMAC-SHA-384 (`vg_ecdsa_p256_<hash>_sign`, which calls
//! `vg_ecdsa_p256_sign`), public keys (`vg_ec_p256_public_key`), and
//! verification (`vg_ecdsa_p256_verify`), each with BMI2 and ADX (and the
//! comb's selection by AVX2) where the CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P256, SigningKey};
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p256::vg_ecdsa_p256_verify_adx;
use crate::cpu::detected;
use crate::ec::p256::{Mul, public_key};

impl SigningKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost 32
/// bytes are `e`.
pub(super) fn verify_with(q: &[u8; 65], e: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    // Align the public point table to avoid split cache-line loads on x86-64.
    #[cfg_attr(target_arch = "x86_64", repr(align(64)))]
    struct Scratch([u64; 1024]);
    let mut scratch = Scratch([0u64; 1024]);
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 65 bytes, `e` of 32, `signature`
        // of 64 and `scratch` for reads and writes of 8192; `scratch` is a
        // distinct object from the others, so it overlaps neither them nor
        // the call's stack frame, and, as Rust objects, none wraps around
        // the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p256_verify(q, e, signature, &mut scratch.0) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p256_verify_adx(q, e, signature, &mut scratch.0) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
