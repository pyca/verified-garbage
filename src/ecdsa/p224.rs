//! ECDSA over P-224: deterministic signatures with HMAC-SHA-224
//! (`vg_ecdsa_p224_sha224_sign`, which calls `vg_ecdsa_p224_sign`), public
//! keys (`vg_ec_p224_public_key`), and verification (`vg_ecdsa_p224_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P224, SigningKey};
use crate::arch::ec_p224::vg_ec_p224_public_key;
use crate::arch::ecdsa_p224::vg_ecdsa_p224_verify;
use crate::zeroize::zeroize;

impl SigningKey<P224> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 28 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 57], Error> {
        let mut out = [0; 57];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 57 bytes, `self.d`
        // for reads of 28 and `scratch` for reads and writes of 8192; `out`
        // and `scratch` are distinct objects from each other and `self.d`,
        // so none overlaps another or the call's stack frame, and, as Rust
        // objects, none wraps around the address space.
        let ok = unsafe { vg_ec_p224_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_p224_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 57],
    digest: &[u8; 28],
    signature: &[u8; 56],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 57 bytes, `digest` of 28,
    // `signature` of 56 and `scratch` for reads and writes of 8192;
    // `scratch` is a distinct object from the others, so it overlaps
    // neither them nor the call's stack frame, and, as Rust objects,
    // none wraps around the address space.
    let ok = unsafe { vg_ecdsa_p224_verify(q, digest, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
