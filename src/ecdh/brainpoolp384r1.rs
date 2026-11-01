//! ECDH over brainpoolP384r1 (`vg_ecdh_brainpoolp384r1`), and public keys
//! (`vg_ec_brainpoolp384r1_public_key`), and their `_umaal` variants on ARMv7
//! CPUs with the features their `_FEATURES` constants name.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use super::{BrainpoolP384r1, Error, PrivateKey};
use crate::arch::ecdh_brainpoolp384r1::vg_ecdh_brainpoolp384r1;
#[cfg(target_arch = "arm")]
use crate::arch::ecdh_brainpoolp384r1::vg_ecdh_brainpoolp384r1_umaal;
use crate::cpu::detected;
use crate::ec::brainpoolp384r1::{Mul, public_key};
use crate::zeroize::zeroize;

impl PrivateKey<BrainpoolP384r1> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 48 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 97], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
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
        let ok = match Mul::select(detected()) {
            // SAFETY: `out` is valid for reads and writes of 48 bytes,
            // `self.d` for reads of 48, `peer` for reads of 97 and
            // `scratch` for reads and writes of 8192; `out` and `scratch`
            // are distinct objects from each other and the others, so none
            // overlaps another or the call's stack frame, and, as Rust
            // objects, none wraps around the address space.
            Mul::Baseline => unsafe {
                vg_ecdh_brainpoolp384r1(&mut out, &self.d, peer, &mut scratch)
            },
            // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
            // (`Mul::select`).
            #[cfg(target_arch = "arm")]
            Mul::Umaal => unsafe {
                vg_ecdh_brainpoolp384r1_umaal(&mut out, &self.d, peer, &mut scratch)
            },
        };
        zeroize(&mut scratch);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}
