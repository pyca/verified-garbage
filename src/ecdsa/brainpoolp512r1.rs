//! ECDSA over brainpoolP512r1: deterministic signatures with HMAC-SHA-512
//! (`vg_ecdsa_brainpoolp512r1_sha512_sign`, which calls `vg_ecdsa_brainpoolp512r1_sign`), public
//! keys (`vg_ec_brainpoolp512r1_public_key`), and verification (`vg_ecdsa_brainpoolp512r1_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{BrainpoolP512r1, Error, SigningKey};
use crate::arch::ec_brainpoolp512r1::vg_ec_brainpoolp512r1_public_key;
use crate::arch::ecdsa_brainpoolp512r1::vg_ecdsa_brainpoolp512r1_verify;
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

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_brainpoolp512r1_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 129],
    digest: &[u8; 64],
    signature: &[u8; 128],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 129 bytes, `digest` of 64,
    // `signature` of 128 and `scratch` for reads and writes of 8192;
    // `scratch` is a distinct object from the others, so it overlaps
    // neither them nor the call's stack frame, and, as Rust objects,
    // none wraps around the address space.
    let ok = unsafe { vg_ecdsa_brainpoolp512r1_verify(q, digest, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
