//! Elliptic-curve Diffie-Hellman: the ECC CDH primitive of NIST SP 800-56A Rev.
//! 3 §5.7.1.2, over the curves of [`ec`](crate::ec).
//!
//! An exchange validates the peer's [`PublicKey<C>`] as SP 800-56A §5.6.2.3.3
//! requires (the uncompressed form of SEC 1 §2.3.3, both coordinates below `p`,
//! on the curve) and returns the x-coordinate of the shared point, which is not
//! passed through a KDF.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod brainpoolp256r1;
mod brainpoolp384r1;
mod brainpoolp512r1;
mod p192;
mod p224;
mod p256;
mod p384;
mod p521;
mod secp256k1;

use crate::ec::{Curve, PublicKey};
use crate::zeroize::zeroize;

/// Why an operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`, or (for an exchange) the
    /// peer's public key is not a valid uncompressed public key on the
    /// curve. The verified code does not say which.
    InvalidKey,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidKey => "invalid ECDH key",
        })
    }
}

impl core::error::Error for Error {}

/// An ECDH private key on the curve `C`.
///
/// The key is cleared when it is dropped. Debug output omits it.
pub struct PrivateKey<C: Curve> {
    d: C::PrivateKey,
}

impl<C: Curve> PrivateKey<C> {
    /// Imports a private key `d`, most significant byte first. Each
    /// operation checks that it is in `[1, n − 1]`.
    pub fn from_bytes(d: &C::PrivateKey) -> Self {
        Self { d: d.clone() }
    }

    /// The public key `Q = dG`.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<PublicKey<C>, Error> {
        PublicKey::derive(&self.d).ok_or(Error::InvalidKey)
    }

    /// The shared secret with the peer whose public key is `peer`: the
    /// x-coordinate of `dQ`, most significant byte first.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`, or `peer`
    /// is not a valid public key (SP 800-56A §5.6.2.3.3).
    pub fn exchange(&self, peer: &PublicKey<C>) -> Result<C::SharedSecret, Error> {
        C::exchange(&self.d, &peer.q).ok_or(Error::InvalidKey)
    }
}

impl<C: Curve> Clone for PrivateKey<C> {
    fn clone(&self) -> Self {
        Self { d: self.d.clone() }
    }
}

impl<C: Curve> core::fmt::Debug for PrivateKey<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl<C: Curve> Drop for PrivateKey<C> {
    fn drop(&mut self) {
        zeroize(self.d.as_mut());
    }
}
