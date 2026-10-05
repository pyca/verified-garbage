//! ECDH over P-384 (`vg_ecdh_p384`), and public keys
//! (`vg_ec_p384_public_key`).

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use super::{Error, P384, PrivateKey};
use crate::arch::ec_p384::vg_ec_p384_public_key;
use crate::arch::ecdh_p384::vg_ecdh_p384;
use crate::zeroize::zeroize;

impl PrivateKey<P384> {
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
        let ok = unsafe { vg_ec_p384_public_key(&mut out, &self.d, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }

    /// The shared secret with the peer whose public key is `peer`
    /// (uncompressed, `04 ‖ x ‖ y`): the x-coordinate of `dQ`, 48 bytes,
    /// most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`, or `peer`
    /// is not a valid public key (SP 800-56A §5.6.2.3.3).
    pub fn diffie_hellman(&self, peer: &[u8; 97]) -> Result<[u8; 48], Error> {
        let mut out = [0; 48];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 48 bytes, `self.d`
        // for reads of 48, `peer` for reads of 97 and `scratch` for reads
        // and writes of 8192; `out` and `scratch` are distinct objects from
        // each other and the others, so none overlaps another or the call's
        // stack frame, and, as Rust objects, none wraps around the address
        // space.
        let ok = unsafe { vg_ecdh_p384(&mut out, &self.d, peer, &mut scratch) };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}
