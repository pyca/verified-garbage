//! ECDSA (FIPS 186-5 §6.4) with deterministic signatures (RFC 6979 §3.2).
//!
//! A [`SigningKey<C>`] holds a private key on the curve `C` (so far
//! [`P256`], [`P384`] and, on x86-64, `P521`), and signs with a hash
//! function `H` that the curve has signatures with ([`SignatureHash<C>`]: for
//! P-256, SHA-256 and SHA-384; for P-384, SHA-384; for P-521, SHA-512), as in
//! `key.sign::<Sha256>(message)`. Each signature is one call of
//! verified code, for the curve and the hash function
//! (`vg_ecdsa_<curve>_<hash>_sign`, contract
//! `VG.Spec.Ecdsa.Rfc6979.Instance.signContract`). That code
//! derives the per-message secret number `k` from the key and the hash with
//! HMAC, as RFC 6979 does, and signs with the verified ECDSA of a given `k`
//! (`vg_ecdsa_<curve>_sign`). It checks the key, and tries further
//! candidates for `k` when one is unsuitable. It follows the implementation
//! of the hash function that this CPU runs (e.g. on x86-64,
//! `vg_ecdsa_p256_sha256_sign_shani` with the SHA extensions, or on
//! AArch64 `vg_ecdsa_p256_sha256_sign_sha2` with the SHA-256 instructions).
//!
//! Signing is constant time except for the number of candidates for `k`
//! that it tries, almost always one.
//!
//! `public_key` derives a key's public key `Q = dG`, by one call of
//! verified code (`vg_ec_<curve>_public_key`, contract
//! `VG.Spec.EcKey.Instance.publicKeyContract`), in constant time.
//!
//! A [`VerifyingKey<C>`] holds a public key, and checks a signature with a
//! hash function `H` (`key.verify::<Sha256>(message, signature)`) by one
//! call of verified code (`vg_ecdsa_<curve>_verify`, contract
//! `VG.Spec.Ecdsa.Instance.verifyContract`) with the hash's leftmost bits,
//! as many as the curve's order has (FIPS 186-5 §6.4.2), which also checks
//! that the key is valid (SP 800-56A §5.6.2.3.3). It runs in constant time,
//! although nothing it handles is secret.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

mod p256;
mod p384;
mod p521;

#[cfg(target_arch = "x86_64")]
pub use crate::ec::P521;
pub use crate::ec::{Curve, P256, P384};

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
/// the curve `C`: for P-256, [`Sha256`](crate::hashes::sha256::Sha256) and
/// [`Sha384`](crate::hashes::sha384::Sha384); for P-384, `Sha384`; for
/// P-521, [`Sha512`](crate::hashes::sha512::Sha512).
pub trait SignatureHash<C: Curve>: sealed::Functions<C> {}

/// Why signing, deriving the public key, or verifying a signature failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The private key is not in `[1, n − 1]`. For a valid key, signing
    /// fails only if none of the candidates for `k` it tries is suitable:
    /// for P-256, with probability under 2⁻²⁴⁸, for P-384 under 2⁻¹⁵⁴⁴,
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

/// An ECDSA public key on the curve `C`, for verifying signatures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey<C: Curve> {
    q: C::PublicKey,
}

impl<C: Curve> VerifyingKey<C> {
    /// Imports a public key, in the uncompressed form of SEC 1 §2.3.3.
    /// Verifying checks that it is valid: a key that is not is never
    /// accepted.
    pub fn from_bytes(q: &C::PublicKey) -> Self {
        Self { q: q.clone() }
    }

    /// The public key, as [`from_bytes`](Self::from_bytes) takes it.
    pub fn to_bytes(&self) -> C::PublicKey {
        self.q.clone()
    }

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
