//! ECDSA over brainpoolP384r1: deterministic signatures with HMAC-SHA-384
//! (`vg_ecdsa_brainpoolp384r1_sha384_sign`, which calls `vg_ecdsa_brainpoolp384r1_sign`), public
//! keys (`vg_ec_brainpoolp384r1_public_key`), and verification (`vg_ecdsa_brainpoolp384r1_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{BrainpoolP384r1, Error, SigningKey};
use crate::arch::ec_brainpoolp384r1::vg_ec_brainpoolp384r1_public_key;
use crate::arch::ecdsa_brainpoolp384r1::vg_ecdsa_brainpoolp384r1_verify;
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

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_brainpoolp384r1_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 97],
    digest: &[u8; 48],
    signature: &[u8; 96],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 97 bytes, `digest` of 48,
    // `signature` of 96 and `scratch` for reads and writes of 8192;
    // `scratch` is a distinct object from the others, so it overlaps
    // neither them nor the call's stack frame, and, as Rust objects,
    // none wraps around the address space.
    let ok = unsafe { vg_ecdsa_brainpoolp384r1_verify(q, digest, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
