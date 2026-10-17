//! RSASSA-PSS (RFC 8017 §8.1) of a hash value, with the keys of
//! [`crate::rsa`].
//!
//! [`sign`] is the verified `vg_rsa_pss_sign` (contract
//! `VG.Spec.RsaPss.signAnyContract`), which takes the hash functions as
//! arguments: EMSA-PSS's encoding of the hash value
//! with a salt of random bytes (RFC 8017 §9.1.1), then the private-key
//! operation of `vg_rsa_private_checked`, which releases the signature only if
//! it passes the check against the public exponent, as BoringSSL's
//! `RSA_sign_pss_mgf1` does. Its timing may depend on the public key, the hash
//! function and the lengths, but not on the hash value, the salt or the
//! private key.
//!
//! [`verify`] is the verified `vg_rsa_pss_verify_precomputed` (contract
//! `VG.Spec.RsaPss.verifyAnyContract`): RSAVP1, then EMSA-PSS-VERIFY (RFC 8017
//! §9.1.2), expecting a salt of a given length or of any length
//! ([`SaltLength::Any`], BoringSSL's `RSA_PSS_SALTLEN_AUTO`), as BoringSSL's
//! `RSA_verify_pss_mgf1` does. Its timing may depend on the public key, the
//! hash function, the lengths and the expected salt length, but not on the
//! signature, the hash value or anything computed from them but the result.
//! Verification reuses the public-key values cached by [`PublicKey::new`].
//!
//! Each function runs the implementations of the hash functions'
//! compression functions that the CPU is best at (as [`crate::hashes`] does:
//! their tier, `crate::hashes::tier`), and for both operations,
//! the RSA backend's (see [`crate::rsa`]): the verified functions are
//! emitted for each pair, all with the same contracts.
//!
//! MGF1 may be over another hash function than the hash value's. This
//! module only checks the lengths, draws the salt and allocates the memory
//! the functions work in.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod any_hash;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::rsa::{PrivateKey, PublicKey};
use crate::zeroize::zeroize;

/// A hash function RSASSA-PSS can use (`VG.Spec.Mgf1.Hash`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hash {
    /// MD5.
    Md5,
    /// SHA-1.
    Sha1,
    /// SHA-224.
    Sha224,
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
    /// SHA-512/224.
    Sha512_224,
    /// SHA-512/256.
    Sha512_256,
}

impl Hash {
    /// The length of the hash function's values, in bytes
    /// (`VG.Spec.Mgf1.Hash.len`).
    pub fn digest_len(self) -> usize {
        match self {
            Hash::Md5 => 16,
            Hash::Sha1 => 20,
            Hash::Sha224 | Hash::Sha512_224 => 28,
            Hash::Sha256 | Hash::Sha512_256 => 32,
            Hash::Sha384 => 48,
            Hash::Sha512 => 64,
        }
    }

    /// The number that names the hash function to the verified functions
    /// that take it as an argument (`VG.Spec.HashId.mgf1`).
    pub(crate) fn id(self) -> usize {
        match self {
            Hash::Md5 => 0,
            Hash::Sha1 => 1,
            Hash::Sha224 => 2,
            Hash::Sha256 => 3,
            Hash::Sha384 => 4,
            Hash::Sha512 => 5,
            Hash::Sha512_224 => 6,
            Hash::Sha512_256 => 7,
        }
    }
}

/// The salt length a signature must have to verify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaltLength {
    /// Exactly this many bytes.
    Len(usize),
    /// Any length the encoding's padding gives (BoringSSL's
    /// `RSA_PSS_SALTLEN_AUTO`).
    Any,
}

/// Why a signature was not made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The hash value is not as long as the hash function's values.
    InvalidDigestLength,
    /// The encoding does not fit the modulus: the hash value, the salt and
    /// two bytes are longer than `⌈(bits of n - 1) / 8⌉`.
    SaltTooLong,
    /// The signature failed the private-key operation's check against the
    /// public exponent (see [`crate::rsa::Error::Fault`]) and is not
    /// released.
    Fault,
    /// The random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidDigestLength => "hash value length is not the hash function's",
            Error::SaltTooLong => "RSA modulus is too short for the hash value and the salt",
            Error::Fault => "RSA signature failed its check against the public exponent",
            Error::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// The words of working space the functions need for an `n_len`-byte
/// modulus (`VG.Spec.RsaPss.scratchWords`).
pub(crate) fn scratch_words(n_len: usize) -> usize {
    crate::rsa::scratch_words(n_len) + 1024
}

/// The words of working space verification needs for an `n_len`-byte
/// modulus (`VG.Spec.RsaPss.publicScratchWords`).
pub(crate) fn public_scratch_words(n_len: usize) -> usize {
    crate::rsa::public_scratch_words(n_len) + 1024
}

/// RSASSA-PSS-SIGN (RFC 8017 §8.1.1) of the hash value `digest` of the hash
/// function `hash`, with MGF1 over `mgf1_hash` and a salt of `salt_len` random bytes: the signature, as long as
/// the modulus.
pub fn sign(
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_len: usize,
) -> Result<Vec<u8>, Error> {
    if digest.len() != hash.digest_len() {
        return Err(Error::InvalidDigestLength);
    }
    if salt_len > key.n.len() {
        return Err(Error::SaltTooLong);
    }
    let mut salt = vec![0u8; salt_len];
    getrandom::fill(&mut salt).map_err(|_| Error::Randomness)?;
    let r = sign_with(key, digest, hash, mgf1_hash, &salt);
    zeroize(&mut salt);
    r
}

/// The signature of `digest` with the salt `salt`.
fn sign_with(
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt: &[u8],
) -> Result<Vec<u8>, Error> {
    let k = key.n.len();
    let mut out = vec![0; k];
    let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
    let r = any_hash::sign(&mut out, key, digest, hash, mgf1_hash, salt, &mut scratch);
    // `PrivateKey::from_crt` checked the key, so a refusal means the encoding
    // does not fit.
    match r {
        1 => Ok(out),
        2 => Err(Error::Fault),
        _ => Err(Error::SaltTooLong),
    }
}

/// RSASSA-PSS-VERIFY (RFC 8017 §8.1.2): whether `signature` is a valid
/// signature of the hash value `digest` of the hash function `hash`, with
/// MGF1 over `mgf1_hash` and a salt
/// of `salt_length`.
pub fn verify(
    key: &PublicKey,
    signature: &[u8],
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_length: SaltLength,
) -> bool {
    let k = key.n.len();
    if digest.len() != hash.digest_len() || signature.len() != k {
        return false;
    }
    let (salt_len, any) = match salt_length {
        SaltLength::Len(l) => (l, 0),
        SaltLength::Any => (0, 1),
    };
    let mut scratch = key.verify_scratch.take(public_scratch_words(k), false);
    let r = any_hash::verify(
        key,
        signature,
        digest,
        hash,
        mgf1_hash,
        salt_len,
        any,
        &mut scratch,
    );
    // The encoding is public: ScratchLease returns the buffer to the key unwiped.
    r == 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

    /// With `composite_key`'s 64-byte modulus (`emLen = 64`): MGF1 over another hash
    /// function (the signature fails the check), a
    /// hash value of the wrong length, salts longer than the
    /// modulus and than the encoding has room for, and a signature that
    /// fails the check.
    #[test]
    fn sign_refused() {
        let (private, _) = composite_key();
        let s = |d: &[u8], h, g, l| sign(&private, d, h, g, l);
        assert_eq!(s(&[0; 20], Hash::Sha1, Hash::Sha256, 0), Err(Error::Fault));
        assert_eq!(
            s(&[0; 19], Hash::Sha1, Hash::Sha1, 0),
            Err(Error::InvalidDigestLength)
        );
        assert_eq!(
            s(&[0; 20], Hash::Sha1, Hash::Sha1, 65),
            Err(Error::SaltTooLong)
        );
        assert_eq!(
            s(&[0; 20], Hash::Sha1, Hash::Sha1, 43),
            Err(Error::SaltTooLong)
        );
        assert_eq!(s(&[0; 20], Hash::Sha1, Hash::Sha1, 0), Err(Error::Fault));
    }

    /// Arguments `verify` refuses before calling the verified function.
    #[test]
    fn verify_refused() {
        let (_, public) = composite_key();
        let sig = [1; 64];
        let v = |s: &[u8], d: &[u8], h, g| verify(&public, s, d, h, g, SaltLength::Any);
        assert!(!v(&sig, &[0; 20], Hash::Sha1, Hash::Sha256));
        assert!(!v(&sig, &[0; 19], Hash::Sha1, Hash::Sha1));
        assert!(!v(&sig[..63], &[0; 20], Hash::Sha1, Hash::Sha1));
        assert!(!v(&sig, &[0; 20], Hash::Sha1, Hash::Sha1));
    }

    #[test]
    fn errors() {
        for e in [
            Error::InvalidDigestLength,
            Error::SaltTooLong,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
