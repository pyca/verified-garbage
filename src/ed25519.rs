//! Ed25519 (RFC 8032 §5.1), deterministic signatures from 32-byte seeds.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::ed25519::{
    vg_ed25519_key_pair_auto, vg_ed25519_sign_expanded_auto, vg_ed25519_verify_auto,
};
use crate::error::InvalidSignature;
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

/// An encoded Ed25519 public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    bytes: [u8; 32],
}

impl VerifyingKey {
    /// Import an encoded public key. Its encoding is checked during verification.
    pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        Self { bytes: *bytes }
    }

    /// The encoded public key.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.bytes
    }

    /// Verify a pure Ed25519 signature (RFC 8032 §5.1.7).
    ///
    /// Public keys and signatures must use canonical encodings, and the
    /// signature scalar must be less than the subgroup order. This checks
    /// the uncofactored equation. The SHA-512 challenge is reduced modulo the
    /// subgroup order, following RFC 8032 §6. No additional subgroup or
    /// small-order rejection policy is imposed.
    /// Verification timing may depend on the public key, message, and signature.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if the signature is not 64 bytes long, an
    /// encoding is not canonical, or the equation does not hold.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), InvalidSignature> {
        let dit = crate::dit::public(crate::dit::Why::Verify);
        let signature: &[u8; 64] = signature.try_into().map_err(|_| InvalidSignature)?;
        let valid = verify_message(dit, &self.bytes, message, signature);
        if valid == 1 {
            Ok(())
        } else {
            Err(InvalidSignature)
        }
    }
}

/// An Ed25519 signing key, storing its seed and derived public key.
///
/// The seed is cleared when the key is dropped. Debug output omits it.
#[derive(Clone)]
pub struct SigningKey {
    seed: [u8; 32],
    /// The seed's SHA-512 digest (RFC 8032 §5.1.6, step 1), which signing
    /// reads rather than hashing the seed again.
    expanded: [u8; 64],
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
        zeroize(&mut self.expanded);
    }
}

impl SigningKey {
    /// Derive a signing key and its public key from an RFC 8032 seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        crate::dit::enter!(dit);
        let mut expanded = [0u8; 64];
        let mut public = [0u8; 32];
        key_pair(dit, &mut public, &mut expanded, seed);
        Self {
            seed: *seed,
            expanded,
            public: VerifyingKey { bytes: public },
        }
    }

    /// The original 32-byte seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The public key derived from this key's seed.
    pub fn verifying_key(&self) -> &VerifyingKey {
        &self.public
    }

    /// Sign `message` deterministically using pure Ed25519 (RFC 8032 §5.1.6).
    pub fn sign(&self, message: &[u8]) -> [u8; 64] {
        crate::dit::enter!(dit);
        sign_message(dit, self, message)
    }
}

/// The seed's SHA-512 digest (RFC 8032 §5.1.5, step 1) into `expanded` and
/// its public key (§5.1.5) into `public`, with the verified
/// `vg_ed25519_key_pair`.
fn key_pair(
    dit: crate::dit::Dit<'_>,
    public: &mut [u8; 32],
    expanded: &mut [u8; 64],
    seed: &[u8; 32],
) {
    // Uninitialized: the contract holds whatever the scratch holds, so
    // filling it with zeros first would only cost time.
    let mut scratch = CacheAligned(MaybeUninit::<[u64; 1024]>::uninit());
    // SAFETY: the public key, digest, seed and scratch are distinct objects
    // valid for 32, 64, 32 and 8192 bytes, respectively, so they overlap
    // neither each other nor the call's stack, and none wraps the address
    // space. The dispatcher calls only an implementation the CPU has the
    // features of.
    unsafe { vg_ed25519_key_pair_auto(dit, public, expanded, seed, scratch.0.as_mut_ptr()) };
    zeroize(core::slice::from_mut(&mut scratch));
}

fn verify_message(
    dit: crate::dit::Dit<'_>,
    pk: &[u8; 32],
    message: &[u8],
    signature: &[u8; 64],
) -> u32 {
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = CacheAligned(MaybeUninit::<[u64; 1024]>::uninit());
    // SAFETY: input references are valid for their declared lengths and scratch
    // is a distinct writable object. No object overlaps the call stack. The
    // dispatcher calls only an implementation the CPU has the features of.
    let valid = unsafe {
        vg_ed25519_verify_auto(
            dit,
            pk,
            message.as_ptr(),
            message.len(),
            signature,
            scratch.0.as_mut_ptr(),
        )
    };
    zeroize(core::slice::from_mut(&mut scratch));
    valid
}

fn sign_message(dit: crate::dit::Dit<'_>, key: &SigningKey, message: &[u8]) -> [u8; 64] {
    let mut signature = [0u8; 64];
    // Uninitialized: each function's contract holds whatever the scratch
    // holds, so filling it with zeros first would only cost time.
    let mut scratch = CacheAligned(MaybeUninit::<[u64; 1024]>::uninit());
    // SAFETY: the input references are valid for their declared lengths.
    // Signature and scratch are distinct writable objects, disjoint from the
    // inputs and the call's stack. None wraps the address space. `expanded`
    // and the public key are the seed's SHA-512 digest and public key: the
    // verified `vg_ed25519_key_pair` wrote both from the seed in `from_seed`,
    // and nothing changes them after. The dispatcher calls only an
    // implementation the CPU has the features of.
    unsafe {
        vg_ed25519_sign_expanded_auto(
            dit,
            &mut signature,
            &key.expanded,
            &key.public.bytes,
            message.as_ptr(),
            message.len(),
            scratch.0.as_mut_ptr(),
        )
    };
    zeroize(core::slice::from_mut(&mut scratch));
    signature
}
