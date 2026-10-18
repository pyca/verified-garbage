//! ECDSA over P-384: deterministic signatures with HMAC-SHA-384
//! (`vg_ecdsa_p384_sha384_sign`, which calls `vg_ecdsa_p384_sign`), public
//! keys (`vg_ec_p384_public_key`), and verification (`vg_ecdsa_p384_verify`),
//! each with BMI2 and ADX where the CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P384, SigningKey};
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p384::vg_ecdsa_p384_verify_adx;
use crate::cpu::detected;
use crate::ec::p384::{Mul, public_key};

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

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_p384_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 97],
    digest: &[u8; 48],
    signature: &[u8; 96],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 97 bytes, `digest` of 48,
        // `signature` of 96 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p384_verify(q, digest, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p384_verify_adx(q, digest, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
