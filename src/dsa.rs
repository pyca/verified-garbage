//! DSA parameter and key generation, and signing and verification of prehashed messages,
//! with fixed-width big-endian `r || s` signatures (FIPS 186-4).
//!
//! The verified operations check domain and key algebraic consistency and
//! scalar ranges. As with this crate's RSA operations, they do not prove
//! primality: callers must obtain domain parameters from a trusted source
//! or validate them separately. On x86-64 and AArch64, `Parameters::generate` runs
//! probable-prime parameter generation entirely in verified assembly. FIPS 186-5 retains DSA for legacy verification.
//!
//! Supported `(p, q)` encoding widths are `(128, 20)`, `(256, 20)`, `(256, 28)`,
//! `(256, 32)` and `(384, 32)` bytes. The 2048/160 pair is a legacy
//! interoperability extension to the FIPS 186-4 sizes. Leading-zero padding is accepted;
//! the actual domain must have one of the supported bit lengths. Digests
//! may have any length and are truncated to the subgroup's actual bit length.
//! Keys own their components, so each operation's buffers are disjoint.
//! Private keys, nonces and scratch are wiped when their owners are dropped.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm"
    ),
    feature = "alloc"
))]

use alloc::{vec, vec::Vec};
use core::fmt;
#[cfg(target_arch = "aarch64")]
use core::sync::atomic::{AtomicU8, Ordering};

#[cfg(test)]
use crate::arch::dsa::vg_dsa_sign;
#[cfg(all(target_arch = "x86_64", test))]
use crate::arch::dsa::vg_dsa_sign_adx;
use crate::arch::dsa::vg_dsa_sign_random;
#[cfg(any(not(target_arch = "aarch64"), test))]
use crate::arch::dsa::vg_dsa_verify;
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_GENERATE_KEY_ADX_FEATURES, VG_DSA_SIGN_RANDOM_ADX_FEATURES, VG_DSA_VERIFY_ADX_FEATURES,
    vg_dsa_sign_random_adx, vg_dsa_verify_adx,
};
#[cfg(target_arch = "aarch64")]
use crate::arch::dsa::{vg_dsa_validate_public_key, vg_dsa_verify_prevalidated};
use crate::cpu::{Features, detected};
use crate::zeroize::{Int, zeroize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    Baseline,
    #[cfg(target_arch = "x86_64")]
    Adx,
}

impl Backend {
    fn select(_features: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _features.contains(VG_DSA_SIGN_RANDOM_ADX_FEATURES)
            && _features.contains(VG_DSA_VERIFY_ADX_FEATURES)
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
#[cfg_attr(not(target_arch = "aarch64"), derive(Clone))]
pub struct PublicKey {
    packed: Vec<u8>,
    p_len: usize,
    q_len: usize,
    backend: Backend,
    // 0 = unchecked, 1 = valid, 2 = invalid. The owned key bytes never change.
    #[cfg(target_arch = "aarch64")]
    validated: AtomicU8,
}

#[cfg(target_arch = "aarch64")]
impl Clone for PublicKey {
    fn clone(&self) -> Self {
        Self {
            packed: self.packed.clone(),
            p_len: self.p_len,
            q_len: self.q_len,
            backend: self.backend,
            #[cfg(target_arch = "aarch64")]
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
            #[cfg(target_arch = "aarch64")]
            validated: AtomicU8::new(0),
        })
    }

    /// Verify a prehashed digest and a fixed-width big-endian `r || s`
    /// signature. Invalid keys, signatures and signature lengths return false.
    /// On AArch64, the first verification validates the immutable public key;
    /// later calls reuse that result while checking every signature independently.
    pub fn verify(&self, digest: &[u8], signature: &[u8]) -> bool {
        if signature.len() != 2 * self.q_len {
            return false;
        }
        #[cfg(target_arch = "aarch64")]
        let validation = self.validated.load(Ordering::Relaxed);
        #[cfg(target_arch = "aarch64")]
        if validation == 2 {
            return false;
        }
        let mut scratch = Secret(vec![0u64; 16 * self.p_len]);
        #[cfg(target_arch = "aarch64")]
        if validation == 0 {
            // SAFETY: import establishes widths, the key owns its immutable
            // bytes, and scratch is a separate allocation of 16*p_len words.
            let valid = unsafe {
                vg_dsa_validate_public_key(
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
                return false;
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
            #[cfg(target_arch = "aarch64")]
            // SAFETY: successful validation above, or a cached result for the
            // exact same immutable owned bytes, establishes the new precondition.
            Backend::Baseline => verify!(vg_dsa_verify_prevalidated),
            #[cfg(not(target_arch = "aarch64"))]
            Backend::Baseline => verify!(vg_dsa_verify),
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => verify!(vg_dsa_verify_adx),
        };
        result == 1
    }
}

/// An owned DSA private key. Debug output never includes its scalar.
pub struct PrivateKey {
    public: PublicKey,
    packed: Secret<u8>,
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
        Ok(Self {
            public,
            packed: Secret(packed),
        })
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
    /// indefinitely. Each retry draws a fresh nonce.
    pub fn sign(&self, digest: &[u8]) -> Result<Vec<u8>, Error> {
        self.sign_with_rng(digest, |buf| {
            getrandom::fill(buf).map_err(|_| Error::Randomness)
        })
    }

    fn sign_with_rng(
        &self,
        digest: &[u8],
        mut random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Vec<u8>, Error> {
        let mut tape = Secret(Vec::with_capacity(8 * 128 * self.public.q_len));
        let mut scratch = Secret(vec![0u64; 16 * self.public.p_len + 64]);
        let mut output = vec![0u8; 2 * self.public.q_len];
        loop {
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
                            self.public.q_len,
                            digest.as_ptr(),
                            digest.len(),
                            tape.0.as_ptr(),
                            tape.0.len(),
                            scratch.0.as_mut_ptr(),
                            scratch.0.len(),
                        )
                    }
                };
            }
            let status = match self.public.backend {
                Backend::Baseline => sign!(vg_dsa_sign_random),
                #[cfg(target_arch = "x86_64")]
                Backend::Adx => sign!(vg_dsa_sign_random_adx),
            };
            match status {
                1 => return Ok(output),
                2 => {
                    // The contract permits extending an exhausted tape and
                    // replaying this same signing operation. Preserve its
                    // prefix; never reuse the tape for another signing.
                    let start = tape.0.len();
                    tape.0.resize(start + self.public.q_len, 0);
                    random(&mut tape.0[start..])?;
                }
                _ => return Err(Error::InvalidKeyOrNonce),
            }
        }
    }

    #[cfg(test)]
    fn sign_once(
        &self,
        digest: &[u8],
        nonce: &[u8],
        output: &mut [u8],
        scratch: &mut [u64],
    ) -> bool {
        assert_eq!(nonce.len(), self.public.q_len);
        assert_eq!(output.len(), 2 * self.public.q_len);
        assert!(scratch.len() >= 16 * self.public.p_len);
        macro_rules! sign {
            ($function:path) => {
                // SAFETY: import and the assertions establish the contract's
                // widths. The owned packed key cannot alias the output or
                // scratch, and the exclusive output/scratch slices cannot
                // overlap any live input. CPU features select the backend.
                unsafe {
                    $function(
                        output.as_mut_ptr(),
                        output.len(),
                        self.packed.0.as_ptr(),
                        self.packed.0.len(),
                        self.public.p_len,
                        nonce.as_ptr(),
                        nonce.len(),
                        digest.as_ptr(),
                        digest.len(),
                        scratch.as_mut_ptr(),
                        scratch.len(),
                    )
                }
            };
        }
        let result = match self.public.backend {
            Backend::Baseline => sign!(vg_dsa_sign),
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => sign!(vg_dsa_sign_adx),
        };
        result == 1
    }
}

mod keygen;
mod parameters;

pub use parameters::Parameters;

#[cfg(test)]
#[path = "dsa/tests.rs"]
mod tests;
