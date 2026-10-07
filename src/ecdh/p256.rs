//! ECDH over P-256 (`vg_ecdh_p256`), and public keys
//! (`vg_ec_p256_public_key`), with BMI2, ADX and AVX2 table selection
//! where the CPU has them (`_adx`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

use super::{Error, P256, PrivateKey};
use crate::arch::ecdh_p256::vg_ecdh_p256;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdh_p256::vg_ecdh_p256_adx;
use crate::cpu::detected;
use crate::ec::p256::{Mul, public_key};
use crate::zeroize::zeroize;

impl PrivateKey<P256> {
    /// The public key `Q = dG`, in the uncompressed form of SEC 1 §2.3.3:
    /// `04 ‖ x ‖ y`, each coordinate 32 bytes, most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<[u8; 65], Error> {
        public_key(&self.d).ok_or(Error::InvalidKey)
    }

    /// The shared secret with the peer whose public key is `peer`
    /// (uncompressed, `04 ‖ x ‖ y`): the x-coordinate of `dQ`, 32 bytes,
    /// most significant first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`, or `peer`
    /// is not a valid public key (SP 800-56A §5.6.2.3.3).
    pub fn diffie_hellman(&self, peer: &[u8; 65]) -> Result<[u8; 32], Error> {
        let mut out = [0; 32];
        #[cfg_attr(target_arch = "x86_64", repr(align(64)))]
        struct Scratch([u64; 1024]);
        let mut scratch = Scratch([0u64; 1024]);
        let ok = match Mul::select(detected()) {
            // SAFETY: `out` is valid for reads and writes of 32 bytes,
            // `self.d` for reads of 32, `peer` for reads of 65 and `scratch`
            // for reads and writes of 8192; `out` and `scratch` are distinct
            // objects from each other and the others, so none overlaps
            // another or the call's stack frame, and, as Rust objects, none
            // wraps around the address space.
            Mul::Baseline => unsafe { vg_ecdh_p256(&mut out, &self.d, peer, &mut scratch.0) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2, ADX and AVX2
            // (`Mul::select`).
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => unsafe { vg_ecdh_p256_adx(&mut out, &self.d, peer, &mut scratch.0) },
        };
        zeroize(&mut scratch.0);
        if ok == 1 {
            Ok(out)
        } else {
            Err(Error::InvalidKey)
        }
    }
}
