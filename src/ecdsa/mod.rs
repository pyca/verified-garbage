//! ECDSA (FIPS 186-5 §6.4) with deterministic signatures (RFC 6979 §3.2), over
//! the curves of [`ec`](crate::ec), with MD5, SHA-1 or a SHA-2 hash function
//! ([`SignatureHash<C>`]).
//!
//! Signing's timing may depend on how many candidates for the per-message
//! secret `k` it tries (almost always one), but not otherwise on the key or the
//! message. Verification with a [`PublicKey<C>`] uses as many of the hash's
//! leftmost bits as the curve's order has (FIPS 186-5 §6.4.2), and validates
//! the key (SP 800-56A §5.6.2.3.3).

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
mod table;

use crate::ec::{Curve, PublicKey};
use crate::zeroize::zeroize;

mod sealed {
    /// The verified functions of the curve `C` with a hash function: signing
    /// its hash `digest` with the private key `d`, and verifying a signature
    /// of it with the public key `q`.
    pub trait Functions<C: super::Curve>: crate::hashes::HashFunction {
        fn sign(d: &C::PrivateKey, digest: &Self::Output) -> Result<C::Signature, super::Error>;
        fn verify(
            q: &C::PublicKey,
            digest: &Self::Output,
            signature: &C::Signature,
        ) -> Result<(), super::Error>;
    }
}

/// A hash function that ECDSA signs with, and verifies signatures of, over
/// the curve `C`: for P-224, [`Sha224`](crate::hashes::sha224::Sha224); for
/// P-256, [`Sha256`](crate::hashes::sha256::Sha256) and
/// [`Sha384`](crate::hashes::sha384::Sha384); for P-384, `Sha384`; for
/// P-521, [`Sha512`](crate::hashes::sha512::Sha512); for secp256k1 and
/// brainpoolP256r1, `Sha256`; for brainpoolP384r1, `Sha384`; for
/// brainpoolP512r1, `Sha512`.
pub trait SignatureHash<C: Curve>: sealed::Functions<C> {}

/// Why signing, deriving the public key, or verifying a signature failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`. For a valid key, signing
    /// fails only if none of the candidates for `k` it tries is suitable:
    /// for P-224, with probability under 2⁻⁸⁸⁸, for P-256 under 2⁻²⁴⁸, for
    /// P-384 under 2⁻¹⁵⁴⁴,
    /// and for P-521 under 2⁻²⁰⁸⁸; deriving the public key
    /// never fails.
    InvalidKey,
    /// The signature is not valid for the public key, or the public key is
    /// not valid.
    InvalidSignature,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Error::InvalidKey => "invalid ECDSA private key",
            Error::InvalidSignature => "invalid ECDSA signature",
        })
    }
}

impl core::error::Error for Error {}

/// An ECDSA private key on the curve `C`.
///
/// The key is cleared when it is dropped. Debug output omits it.
pub struct SigningKey<C: Curve> {
    d: C::PrivateKey,
}

impl<C: Curve> SigningKey<C> {
    /// Imports a private key `d`, most significant byte first. Signing and
    /// deriving the public key check that it is in `[1, n − 1]`.
    pub fn from_bytes(d: &C::PrivateKey) -> Self {
        Self { d: d.clone() }
    }

    /// The public key `Q = dG`, which verifies the key's signatures.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn public_key(&self) -> Result<PublicKey<C>, Error> {
        PublicKey::derive(&self.d).ok_or(Error::InvalidKey)
    }

    /// Signs the hash of `message` with the hash function `H`, deriving `k`
    /// with HMAC with `H` (RFC 6979 §3.2): the signature `r ‖ s`.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn sign<H: SignatureHash<C>>(&self, message: &[u8]) -> Result<C::Signature, Error> {
        self.sign_prehashed::<H>(&H::digest(message))
    }

    /// Signs `digest`, the hash of a message with `H`, as
    /// [`sign`](Self::sign) signs the message.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidKey`] if the key is not in `[1, n − 1]`.
    pub fn sign_prehashed<H: SignatureHash<C>>(
        &self,
        digest: &H::Output,
    ) -> Result<C::Signature, Error> {
        H::sign(&self.d, digest)
    }
}

impl<C: Curve> Clone for SigningKey<C> {
    fn clone(&self) -> Self {
        Self { d: self.d.clone() }
    }
}

impl<C: Curve> core::fmt::Debug for SigningKey<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl<C: Curve> Drop for SigningKey<C> {
    fn drop(&mut self) {
        zeroize(self.d.as_mut());
    }
}

/// Verifying ECDSA signatures.
impl<C: Curve> PublicKey<C> {
    /// Verifies the signature `r ‖ s` of the hash of `message` with the hash
    /// function `H` (FIPS 186-5 §6.4.2).
    ///
    /// # Errors
    ///
    /// [`Error::InvalidSignature`] if the signature does not verify with
    /// this key, or the key is not a valid public key.
    pub fn verify<H: SignatureHash<C>>(
        &self,
        message: &[u8],
        signature: &C::Signature,
    ) -> Result<(), Error> {
        self.verify_prehashed::<H>(&H::digest(message), signature)
    }

    /// Verifies a signature of `digest`, the hash of a message with `H`, as
    /// [`verify`](Self::verify) verifies one of the message.
    ///
    /// # Errors
    ///
    /// [`Error::InvalidSignature`] if the signature does not verify with
    /// this key, or the key is not a valid public key.
    pub fn verify_prehashed<H: SignatureHash<C>>(
        &self,
        digest: &H::Output,
        signature: &C::Signature,
    ) -> Result<(), Error> {
        H::verify(&self.q, digest, signature)
    }
}
