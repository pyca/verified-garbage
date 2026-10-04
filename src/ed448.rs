//! Ed448 (RFC 8032), deterministic signatures from 57-byte private keys,
//! with an optional context of up to 255 bytes.
//!
//! Key derivation, signing, and verification each call one complete verified
//! assembly operation, including SHAKE256. Signing uses the public key derived
//! once by [`SigningKey::from_seed`]. This is Ed448 with a context (`dom4` with
//! flag 0), not Ed448ph. Secret scratch values are cleared after use.

#![cfg(any(target_arch = "x86_64", target_arch = "arm"))]

use crate::arch::ed448::{vg_ed448_public_key, vg_ed448_sign_cached, vg_ed448_verify};
use crate::zeroize::zeroize;

/// The longest context RFC 8032 allows.
pub const MAX_CONTEXT_LEN: usize = 255;

/// Why an operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The signature has the wrong length, a noncanonical encoding, or an
    /// invalid equation, or the context is longer than 255 bytes.
    InvalidSignature,
    /// The context to sign with is longer than 255 bytes.
    ContextTooLong,
}

/// An encoded Ed448 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 57],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 57]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 57] {
        &self.bytes
    }

    /// Verify an Ed448 signature with an empty context (RFC 8032 §5.2.7).
    ///
    /// See [`VerifyingKey::verify_with_context`].
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.verify_with_context(&[], message, signature)
    }

    /// Verify an Ed448 signature with the context `context` (RFC 8032 §5.2.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks the
    /// cofactored equation `[4][S]B = [4]R + [4][k]A`. No additional subgroup
    /// or small-order rejection policy is imposed. Nothing verifies with a
    /// context longer than 255 bytes. Verification timing may depend on the
    /// public key, context, message, and signature.
    pub fn verify_with_context(
        &self,
        context: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Error> {
        let signature: &[u8; 114] = signature.try_into().map_err(|_| Error::InvalidSignature)?;
        let mut scratch = [0u64; 1024];
        // SAFETY: the input references are valid for their declared lengths,
        // and scratch is a distinct writable object. No object overlaps the
        // call's stack or wraps the address space.
        let valid = unsafe {
            vg_ed448_verify(
                &self.bytes,
                context.as_ptr(),
                context.len(),
                message.as_ptr(),
                message.len(),
                signature,
                &mut scratch,
            )
        };
        zeroize(&mut scratch);
        if valid == 1 {
            Ok(())
        } else {
            Err(Error::InvalidSignature)
        }
    }
}

/// An Ed448 signing key, storing its private key and derived public key.
///
/// The private key is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 57],
    public: VerifyingKey,
}

impl core::fmt::Debug for SigningKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl Drop for SigningKey {
    fn drop(&mut self) {
        zeroize(&mut self.seed);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key (RFC 8032 §5.2.5) from a
    /// 57-byte private key.
    pub fn from_seed(seed: &[u8; 57]) -> Self {
        let mut public = [0u8; 57];
        let mut scratch = [0u64; 1024];
        // SAFETY: the output, seed, and scratch are distinct objects valid for
        // 57, 57, and 8192 bytes, respectively, so they overlap neither each
        // other nor the call's stack, and none wraps the address space.
        unsafe { vg_ed448_public_key(&mut public, seed, &mut scratch) };
        zeroize(&mut scratch);
        Self {
            seed: *seed,
            public: VerifyingKey { bytes: public },
        }
    }

    /// The original 57-byte private key.
    pub fn seed(&self) -> &[u8; 57] {
        &self.seed
    }

    /// The public key derived from this key's private key.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically with an empty context (RFC 8032 §5.2.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 114] {
        sign_message(&self.seed, &self.public.bytes, &[], message)
    }

    /// Sign `message` deterministically with the context `context` (RFC 8032
    /// §5.2.6), which may be at most 255 bytes long.
    pub fn sign_with_context(&self, context: &[u8], message: &[u8]) -> Result<[u8; 114], Error> {
        if context.len() > MAX_CONTEXT_LEN {
            return Err(Error::ContextTooLong);
        }
        Ok(sign_message(
            &self.seed,
            &self.public.bytes,
            context,
            message,
        ))
    }
}

/// `context` must be at most 255 bytes long.
fn sign_message(seed: &[u8; 57], pk: &[u8; 57], context: &[u8], message: &[u8]) -> [u8; 114] {
    let mut signature = [0u8; 114];
    let mut scratch = [0u64; 1024];
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. pk is seed's
    // public key (`SigningKey::sign` passes the one `from_seed` derived), and
    // the context is at most 255 bytes long (the callers check it).
    unsafe {
        vg_ed448_sign_cached(
            &mut signature,
            seed,
            pk,
            context.as_ptr(),
            context.len(),
            message.as_ptr(),
            message.len(),
            &mut scratch,
        )
    };
    zeroize(&mut scratch);
    signature
}
