//! ECDSA over P-521: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_p521_sha512_sign`, which calls `vg_ecdsa_p521_sign`), public
//! keys (`vg_ec_p521_public_key`), and verification (`vg_ecdsa_p521_verify`),
//! each with BMI2 and ADX (and the comb's selection by AVX2) where the CPU
//! has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64"
))]

use super::{Error, P521, SigningKey};
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdsa_p521::vg_ecdsa_p521_verify_adx;
use crate::cpu::detected;
use crate::ec::p521::{Mul, public_key};

impl SigningKey<P521> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 66 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 133], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }
}

/// The 66 bytes `vg_ecdsa_p521_verify` takes for a hash shorter than them
/// (every hash function's here): the hash's integer shifted left by 7 bits,
/// so that its leftmost 521 bits are the hash's integer (FIPS 186-5
/// §6.4.1).
pub(super) fn widen(digest: &[u8]) -> [u8; 66] {
    let o = 65 - digest.len();
    let mut out = [0; 66];
    for (i, b) in digest.iter().enumerate() {
        out[o + i] |= b >> 1;
        out[o + i + 1] |= b << 7;
    }
    out
}

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_p521_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 133],
    digest: &[u8; 66],
    signature: &[u8; 132],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    let ok = match Mul::select(detected()) {
        // SAFETY: `q` is valid for reads of 133 bytes, `digest` of 66,
        // `signature` of 132 and `scratch` for reads and writes of 8192;
        // `scratch` is a distinct object from the others, so it overlaps
        // neither them nor the call's stack frame, and, as Rust objects,
        // none wraps around the address space.
        Mul::Baseline => unsafe { vg_ecdsa_p521_verify(q, digest, signature, &mut scratch) },
        // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
        // (`Mul::select`).
        #[cfg(target_arch = "x86_64")]
        Mul::Adx => unsafe { vg_ecdsa_p521_verify_adx(q, digest, signature, &mut scratch) },
    };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
