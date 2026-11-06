//! ECDSA (FIPS 186-5 §6.4) with deterministic signatures (RFC 6979 §3.2): the
//! signing and verification methods of `ec`'s keys, and each curve's verified
//! functions with each hash function, in its file here.

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

use crate::ec::{Curve, PrivateKey, PublicKey};
use crate::error::{InvalidKey, InvalidSignature};

mod sealed {
    /// The verified functions of the curve `C` with a hash function: signing
    /// its hash `digest` with the private key `d`, and verifying a signature
    /// of it with the public key `q`.
    pub trait Functions<C: super::Curve>: crate::hashes::HashFunction {
        fn sign(
            d: &C::PrivateKey,
            digest: &Self::Output,
        ) -> Result<C::Signature, super::InvalidKey>;
        fn verify(
            q: &C::PublicKey,
            digest: &Self::Output,
            signature: &C::Signature,
        ) -> Result<(), super::InvalidSignature>;
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

/// Signing with ECDSA.
impl<C: Curve> PrivateKey<C> {
    /// Signs the hash of `message` with the hash function `H` (FIPS 186-5
    /// §6.4.1), deriving `k` with HMAC with `H` (RFC 6979 §3.2): the
    /// signature `r ‖ s`.
    ///
    /// The timing may depend on how many candidates for the per-message
    /// secret `k` it tries (almost always one), but not otherwise on the key
    /// or the message.
    ///
    /// # Errors
    ///
    /// [`InvalidKey`] if the key is not in `[1, n − 1]`. For a valid key,
    /// signing fails only if none of the candidates for `k` it tries is
    /// suitable: for P-224, with probability under 2⁻⁸⁸⁸, for P-256 under
    /// 2⁻²⁴⁸, for P-384 under 2⁻¹⁵⁴⁴, and for P-521 under 2⁻²⁰⁸⁸.
    pub fn sign<H: SignatureHash<C>>(&self, message: &[u8]) -> Result<C::Signature, InvalidKey> {
        self.sign_prehashed::<H>(&H::digest(message))
    }

    /// Signs `digest`, the hash of a message with `H`, as
    /// [`sign`](Self::sign) signs the message.
    ///
    /// # Errors
    ///
    /// [`InvalidKey`], as [`sign`](Self::sign) returns it.
    pub fn sign_prehashed<H: SignatureHash<C>>(
        &self,
        digest: &H::Output,
    ) -> Result<C::Signature, InvalidKey> {
        H::sign(&self.d, digest)
    }
}

/// Verifying ECDSA signatures.
impl<C: Curve> PublicKey<C> {
    /// Verifies the signature `r ‖ s` of the hash of `message` with the hash
    /// function `H` (FIPS 186-5 §6.4.2), using as many of the hash's leftmost
    /// bits as the curve's order has, and validating the key (SP 800-56A
    /// §5.6.2.3.3).
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if the signature does not verify with
    /// this key, or the key is not a valid public key.
    pub fn verify<H: SignatureHash<C>>(
        &self,
        message: &[u8],
        signature: &C::Signature,
    ) -> Result<(), InvalidSignature> {
        self.verify_prehashed::<H>(&H::digest(message), signature)
    }

    /// Verifies a signature of `digest`, the hash of a message with `H`, as
    /// [`verify`](Self::verify) verifies one of the message.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if the signature does not verify with
    /// this key, or the key is not a valid public key.
    pub fn verify_prehashed<H: SignatureHash<C>>(
        &self,
        digest: &H::Output,
        signature: &C::Signature,
    ) -> Result<(), InvalidSignature> {
        H::verify(&self.q, digest, signature)
    }
}
