//! ECDSA over p192: deterministic signatures with HMAC-SHA-256
//! (`vg_ecdsa_p192_sha256_sign`, which calls `vg_ecdsa_p192_sign`), public
//! keys (`vg_ec_p192_public_key`), and verification (`vg_ecdsa_p192_verify`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P192, SigningKey};
use crate::arch::ec_p192::vg_ec_p192_public_key;
use crate::arch::ecdsa_p192::vg_ecdsa_p192_verify;
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

/// Whether `signature` verifies with `q` for the hash whose leftmost bits
/// are `digest`, as `vg_ecdsa_p192_verify` takes them (FIPS 186-5 §6.4.2).
pub(super) fn verify_with(
    q: &[u8; 49],
    digest: &[u8; 24],
    signature: &[u8; 48],
) -> Result<(), Error> {
    let mut scratch = [0u64; 1024];
    // SAFETY: `q` is valid for reads of 49 bytes, the digest prefix of 24,
    // `signature` of 48 and `scratch` for reads and writes of 8192;
    // `scratch` is a distinct object from the others, so it overlaps
    // neither them nor the call's stack frame, and, as Rust objects,
    // none wraps around the address space.
    let ok = unsafe { vg_ecdsa_p192_verify(q, digest, signature, &mut scratch) };
    if ok == 1 {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
