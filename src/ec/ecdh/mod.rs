//! Elliptic-curve Diffie-Hellman (the ECC CDH primitive of NIST SP 800-56A Rev.
//! 3 §5.7.1.2): the exchange of `ec`'s private key, and each curve's verified
//! function, in its file here.

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

use crate::ec::{Curve, PrivateKey, PublicKey};
use crate::error::InvalidKey;

/// Exchanging keys with ECDH.
impl<C: Curve> PrivateKey<C> {
    /// The shared secret with the peer whose public key is `peer` (SP
    /// 800-56A §5.7.1.2): the x-coordinate of `dQ`, most significant byte
    /// first, which is not passed through a KDF. `peer` is validated as SP
    /// 800-56A §5.6.2.3.3 requires: the uncompressed form of SEC 1 §2.3.3,
    /// both coordinates below `p`, on the curve.
    ///
    /// # Errors
    ///
    /// [`InvalidKey`] if the key is not in `[1, n − 1]`, or `peer`
    /// is not a valid public key (the verified code does not say which).
    pub fn exchange(&self, peer: &PublicKey<C>) -> Result<C::SharedSecret, InvalidKey> {
        C::exchange(&self.d, &peer.q).ok_or(InvalidKey)
    }
}
