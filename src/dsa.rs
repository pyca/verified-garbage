//! DSA (FIPS 186-4): parameter and key generation, and signing and verification
//! of prehashed messages, with fixed-width big-endian `r || s` signatures.
//!
//! FIPS 186-5 keeps DSA only for verifying existing signatures. Domain
//! parameters are checked for consistency, not primality: take them from a
//! trusted source or validate them separately. `p` and `q` are 128 and 20, 256
//! and 20, 256 and 28, 256 and 32, or 384 and 32 bytes wide, leading zeros
//! allowed (2048 and 160 bits is an extension to FIPS 186-4's sizes); a digest
//! of any length is truncated to the bit length of `q`.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little"),
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

use alloc::{vec, vec::Vec};
use core::fmt;
use core::sync::atomic::{AtomicU8, Ordering};

#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
)))]
use crate::arch::dsa::vg_dsa_sign_random;
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_GENERATE_KEY_ADX_FEATURES, VG_DSA_SIGN_RANDOM_PREVALIDATED_ADX_FEATURES,
    VG_DSA_VALIDATE_PRIVATE_KEY_ADX_FEATURES, VG_DSA_VALIDATE_PUBLIC_KEY_ADX_FEATURES,
    VG_DSA_VERIFY_PREVALIDATED_ADX_FEATURES, vg_dsa_sign_random_prevalidated_adx,
    vg_dsa_validate_private_key_adx, vg_dsa_validate_public_key_adx,
    vg_dsa_verify_prevalidated_adx,
};
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little")
))]
use crate::arch::dsa::{vg_dsa_sign_random_prevalidated, vg_dsa_validate_private_key};
use crate::arch::dsa::{vg_dsa_validate_public_key, vg_dsa_verify_prevalidated};
use crate::cpu::detected;
use crate::entropy::{self, Step, Stop};
use crate::error::InvalidSignature;
use crate::zeroize::{Int, zeroize};
use verified_garbage_cpu::Features;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Baseline,
    #[cfg(target_arch = "x86_64")]
    Adx,
}

impl Backend {
    fn select(_features: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _features.contains(VG_DSA_SIGN_RANDOM_PREVALIDATED_ADX_FEATURES)
            && _features.contains(VG_DSA_VALIDATE_PRIVATE_KEY_ADX_FEATURES)
            && _features.contains(VG_DSA_VALIDATE_PUBLIC_KEY_ADX_FEATURES)
            && _features.contains(VG_DSA_VERIFY_PREVALIDATED_ADX_FEATURES)
            && _features.contains(VG_DSA_GENERATE_KEY_ADX_FEATURES)
        {
            return Self::Adx;
        }
        Self::Baseline
    }
}

struct Secret<T: Int>(Vec<T>);

impl<T: Int> Drop for Secret<T> {
    fn drop(&mut self) {
        zeroize(&mut self.0);
    }
}

/// Why a key import or signing attempt failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// A component has an unsupported or inconsistent encoding width.
    Length,
    /// The domain or key is inconsistent, or bounded draws or retries failed.
    InvalidKeyOrNonce,
    /// The operating system's random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Length => "invalid DSA component length",
            Self::InvalidKeyOrNonce => "invalid DSA domain or key, or exhausted attempts",
            Self::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// An owned DSA public key. Import checks widths; verification checks the
/// domain and public value. Domain primality is the caller's responsibility.
#[derive(Debug)]
pub struct PublicKey {
    packed: Vec<u8>,
    p_len: usize,
    q_len: usize,
    backend: Backend,
    // 0 = unchecked, 1 = valid, 2 = invalid. The owned key bytes never change.
    validated: AtomicU8,
}

impl Clone for PublicKey {
    fn clone(&self) -> Self {
        Self {
            packed: self.packed.clone(),
            p_len: self.p_len,
            q_len: self.q_len,
            backend: self.backend,
            validated: AtomicU8::new(self.validated.load(Ordering::Relaxed)),
        }
    }
}

impl PublicKey {
    /// Import big-endian `p`, `q`, `g` and `y`. `g` and `y` must have the
    /// same width as `p`, including any leading-zero padding.
    pub fn from_components(p: &[u8], q: &[u8], g: &[u8], y: &[u8]) -> Result<Self, Error> {
        if !matches!(
            (p.len(), q.len()),
            (128, 20) | (256, 20 | 28 | 32) | (384, 32)
        ) || g.len() != p.len()
            || y.len() != p.len()
        {
            return Err(Error::Length);
        }
        let mut packed = Vec::with_capacity(3 * p.len() + q.len());
        for component in [p, q, g, y] {
            packed.extend_from_slice(component);
        }
        Ok(Self {
            packed,
            p_len: p.len(),
            q_len: q.len(),
            backend: Backend::select(detected()),
            validated: AtomicU8::new(0),
        })
    }

    /// Verify a prehashed digest and a fixed-width big-endian `r || s`
    /// signature. The first verification validates the immutable public key;
    /// later calls reuse that result while checking every signature independently.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if the signature is not valid, is not twice as
    /// long as `q`, or the key is not valid.
    pub fn verify(&self, digest: &[u8], signature: &[u8]) -> Result<(), InvalidSignature> {
        if signature.len() != 2 * self.q_len {
            return Err(InvalidSignature);
        }
        let validation = self.validated.load(Ordering::Relaxed);
        if validation == 2 {
            return Err(InvalidSignature);
        }
        let mut scratch = Secret(vec![0u64; 16 * self.p_len]);
        if validation == 0 {
            let validate = match self.backend {
                Backend::Baseline => vg_dsa_validate_public_key,
                #[cfg(target_arch = "x86_64")]
                Backend::Adx => vg_dsa_validate_public_key_adx,
            };
            // SAFETY: import establishes widths, the key owns its immutable
            // bytes, and scratch is a separate allocation of 16*p_len words.
            // CPU features select the backend.
            let valid = unsafe {
                validate(
                    self.packed.as_ptr(),
                    self.packed.len(),
                    self.p_len,
                    self.q_len,
                    scratch.0.as_mut_ptr(),
                    scratch.0.len(),
                )
            } == 1;
            // Publication of the immutable key already follows Rust's sharing
            // rules. This atomic carries only the validation result, so relaxed
            // ordering suffices. Concurrent first calls may repeat validation.
            self.validated
                .store(if valid { 1 } else { 2 }, Ordering::Relaxed);
            if !valid {
                return Err(InvalidSignature);
            }
        }
        macro_rules! verify {
            ($function:path) => {
                // SAFETY: import establishes all widths. The key owns its
                // bytes; scratch is a fresh allocation, disjoint from every
                // input, with the contract's 16*p_len words. Read-only inputs
                // may overlap one another. CPU features select the backend.
                unsafe {
                    $function(
                        self.packed.as_ptr(),
                        self.packed.len(),
                        self.p_len,
                        self.q_len,
                        signature.as_ptr(),
                        signature.len(),
                        digest.as_ptr(),
                        digest.len(),
                        scratch.0.as_mut_ptr(),
                        scratch.0.len(),
                    )
                }
            };
        }
        let result = match self.backend {
            // SAFETY: successful validation above, or a cached result for the
            // exact same immutable owned bytes, establishes the new precondition.
            Backend::Baseline => verify!(vg_dsa_verify_prevalidated),
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => verify!(vg_dsa_verify_prevalidated_adx),
        };
        if result == 1 {
            Ok(())
        } else {
            Err(InvalidSignature)
        }
    }
}

/// An owned DSA private key. Debug output never includes its scalar.
pub struct PrivateKey {
    public: PublicKey,
    packed: Secret<u8>,
    // On x86-64, x86, AArch64 and PPC64LE, whether `vg_dsa_validate_private_key`
    // accepts the owned, immutable `packed`: 0 = unchecked, 1 = valid,
    // 2 = invalid.
    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        all(target_arch = "powerpc64", target_endian = "little")
    ))]
    validated: AtomicU8,
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey")
            .field("p_len", &self.public.p_len)
            .field("q_len", &self.public.q_len)
            .finish_non_exhaustive()
    }
}

impl PrivateKey {
    /// Import big-endian `p`, `q`, `g`, `y` and `x`. `x` must have `q`'s
    /// width. Signing checks that `g^x mod p = y` and validates the domain's
    /// algebraic consistency; callers must assure domain primality separately.
    pub fn from_components(
        p: &[u8],
        q: &[u8],
        g: &[u8],
        y: &[u8],
        x: &[u8],
    ) -> Result<Self, Error> {
        let public = PublicKey::from_components(p, q, g, y)?;
        if x.len() != q.len() {
            return Err(Error::Length);
        }
        let mut packed = public.packed.clone();
        packed.extend_from_slice(x);
        Ok(Self::new(public, Secret(packed)))
    }

    /// The key of a public key and its packed private bytes, not yet validated.
    fn new(public: PublicKey, packed: Secret<u8>) -> Self {
        Self {
            public,
            packed,
            #[cfg(any(
                target_arch = "x86_64",
                target_arch = "x86",
                target_arch = "aarch64",
                all(target_arch = "powerpc64", target_endian = "little")
            ))]
            validated: AtomicU8::new(0),
        }
    }

    /// Borrow the public key corresponding to the imported components.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Sign a prehashed digest using a fresh, uniformly sampled nonce from
    /// the operating system. Returns fixed-width big-endian `r || s`.
    ///
    /// At most eight signing attempts are made, each with at most 128 nonce
    /// draws. Invalid keys therefore return an error instead of retrying
    /// indefinitely. Each retry draws a fresh nonce. On x86-64, AArch64 and
    /// PPC64LE the first signature validates the immutable key, and later
    /// ones reuse that result, as [`PublicKey::verify`] does.
    pub fn sign(&self, digest: &[u8]) -> Result<Vec<u8>, Error> {
        self.sign_from(digest, |buf| {
            getrandom::fill(buf).map_err(|_| Error::Randomness)
        })
    }

    /// [`sign`](Self::sign), with its nonces drawn from `random`.
    fn sign_from(
        &self,
        digest: &[u8],
        random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Vec<u8>, Error> {
        let q_len = self.public.q_len;
        let mut scratch = Secret(vec![0u64; 16 * self.public.p_len + 64]);
        #[cfg(any(
            target_arch = "x86_64",
            target_arch = "x86",
            target_arch = "aarch64",
            all(target_arch = "powerpc64", target_endian = "little")
        ))]
        if !self.validate(&mut scratch.0) {
            return Err(Error::InvalidKeyOrNonce);
        }
        let mut output = vec![0u8; 2 * q_len];
        // The first call needs no random bytes: it checks the key first.
        let signed = entropy::serve(0, random, |tape| {
            let mut used = [0u64; 1];
            macro_rules! sign {
                ($function:path) => {
                    // SAFETY: imports establish supported widths. All writable
                    // buffers are separate owned allocations, disjoint from
                    // the key, digest and random tape. Scratch has the required
                    // size, and backend selection establishes CPU features.
                    unsafe {
                        $function(
                            output.as_mut_ptr(),
                            output.len(),
                            &mut used,
                            self.packed.0.as_ptr(),
                            self.packed.0.len(),
                            self.public.p_len,
                            q_len,
                            digest.as_ptr(),
                            digest.len(),
                            tape.as_ptr(),
                            tape.len(),
                            scratch.0.as_mut_ptr(),
                            scratch.0.len(),
                        )
                    }
                };
            }
            // On x86-64, x86, AArch64 and PPC64LE, the validation above, or a
            // cached result for the exact same immutable owned bytes,
            // establishes the prevalidated signer's precondition.
            let status = match self.public.backend {
                #[cfg(not(any(
                    target_arch = "x86_64",
                    target_arch = "x86",
                    target_arch = "aarch64",
                    all(target_arch = "powerpc64", target_endian = "little")
                )))]
                Backend::Baseline => sign!(vg_dsa_sign_random),
                #[cfg(any(
                    target_arch = "x86_64",
                    target_arch = "x86",
                    target_arch = "aarch64",
                    all(target_arch = "powerpc64", target_endian = "little")
                ))]
                Backend::Baseline => sign!(vg_dsa_sign_random_prevalidated),
                #[cfg(target_arch = "x86_64")]
                Backend::Adx => sign!(vg_dsa_sign_random_prevalidated_adx),
            };
            match status {
                1 => Step::Done,
                // The contract permits extending an exhausted tape and
                // replaying this same signing operation, so the whole tape
                // is kept; it is never reused for another signing.
                2 => Step::More {
                    used: 0,
                    requested: tape.len() + q_len,
                },
                _ => Step::Failed,
            }
        });
        match signed {
            Ok(()) => Ok(output),
            Err(Stop::Failed) => Err(Error::InvalidKeyOrNonce),
            Err(Stop::Fill(e)) => Err(e),
        }
    }

    /// Whether `vg_dsa_validate_private_key` accepts the key, validating it
    /// on the first call. `scratch` holds at least 16*p_len words.
    #[cfg(any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        all(target_arch = "powerpc64", target_endian = "little")
    ))]
    fn validate(&self, scratch: &mut [u64]) -> bool {
        match self.validated.load(Ordering::Relaxed) {
            0 => {}
            state => return state == 1,
        }
        let validate = match self.public.backend {
            Backend::Baseline => vg_dsa_validate_private_key,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_dsa_validate_private_key_adx,
        };
        // SAFETY: import establishes the widths and key_len = 3*p_len +
        // 2*q_len; the key owns its immutable bytes, and scratch is a separate
        // allocation of at least 16*p_len words. CPU features select the
        // backend.
        let valid = unsafe {
            validate(
                self.packed.0.as_ptr(),
                self.packed.0.len(),
                self.public.p_len,
                self.public.q_len,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        } == 1;
        // As in `PublicKey::verify`, the atomic carries only the validation
        // result of the immutable bytes; concurrent first calls may repeat it.
        self.validated
            .store(if valid { 1 } else { 2 }, Ordering::Relaxed);
        valid
    }
}

mod keygen;
mod parameters;

// Parameter generation is not yet implemented on RISC-V (`parameters.rs`
// states the architectures it supports).
#[cfg(not(target_arch = "riscv64"))]
pub use parameters::Parameters;

#[cfg(test)]
#[path = "dsa/tests.rs"]
mod tests;
