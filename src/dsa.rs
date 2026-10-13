//! DSA signing and verification of prehashed messages, with fixed-width
//! big-endian `r || s` signatures (FIPS 186-4).
//!
//! The operations check domain and key algebraic consistency and
//! scalar ranges. As with this crate's RSA operations, they do not prove
//! primality: callers must obtain domain parameters from a trusted source
//! or validate them separately. FIPS 186-5 retains DSA for legacy verification.
//!
//! Supported `(p, q)` encoding widths are `(128, 20)`, `(256, 28)`,
//! `(256, 32)` and `(384, 32)` bytes. Leading-zero padding is accepted;
//! the actual domain must have one of the supported bit lengths. Digests
//! may have any length and are truncated to the subgroup's actual bit length.
//! Keys own their components, so each operation's buffers are disjoint.
//! Private keys, nonces and scratch are wiped when their owners are dropped.
//!
//! Lean verifies the complete signing and verification primitives, on
//! x86-64 and AArch64.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use alloc::{vec, vec::Vec};
use core::fmt;

#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_SIGN_ADX_FEATURES, VG_DSA_VERIFY_ADX_FEATURES, vg_dsa_sign_adx, vg_dsa_verify_adx,
};
use crate::arch::dsa::{vg_dsa_sign, vg_dsa_verify};
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
        if _features.contains(VG_DSA_SIGN_ADX_FEATURES)
            && _features.contains(VG_DSA_VERIFY_ADX_FEATURES)
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
    /// The key is inconsistent, or bounded nonce/signature retries failed.
    InvalidKeyOrNonce,
    /// The operating system's random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Length => "invalid DSA component length",
            Self::InvalidKeyOrNonce => "invalid DSA key or exhausted nonce attempts",
            Self::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

// Examine every byte: an early-exit integer comparison would expose a
// prefix of the nonce that is subsequently used for signing.
fn nonce_in_range(nonce: &[u8], q: &[u8]) -> bool {
    let mut borrow = 0u16;
    let mut nonzero = 0u8;
    for (&a, &b) in nonce.iter().zip(q).rev() {
        borrow = (u16::from(a).wrapping_sub(u16::from(b) + borrow)) >> 15;
        nonzero |= a;
    }
    (borrow == 1) & (nonzero != 0)
}

/// An owned DSA public key. Import checks widths; verification checks the
/// domain and public value. Domain primality is the caller's responsibility.
#[derive(Clone, Debug)]
pub struct PublicKey {
    packed: Vec<u8>,
    p_len: usize,
    q_len: usize,
    backend: Backend,
}

impl PublicKey {
    /// Import big-endian `p`, `q`, `g` and `y`. `g` and `y` must have the
    /// same width as `p`, including any leading-zero padding.
    pub fn from_components(p: &[u8], q: &[u8], g: &[u8], y: &[u8]) -> Result<Self, Error> {
        if !matches!((p.len(), q.len()), (128, 20) | (256, 28 | 32) | (384, 32))
            || g.len() != p.len()
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
        })
    }

    /// Verify a prehashed digest and a fixed-width big-endian `r || s`
    /// signature. Invalid keys, signatures and signature lengths return false.
    pub fn verify(&self, digest: &[u8], signature: &[u8]) -> bool {
        if signature.len() != 2 * self.q_len {
            return false;
        }
        let mut scratch = Secret(vec![0u64; 16 * self.p_len]);
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
        let q = &self.public.packed[self.public.p_len..self.public.p_len + self.public.q_len];
        let first = q
            .iter()
            .position(|&b| b != 0)
            .ok_or(Error::InvalidKeyOrNonce)?;
        let high_mask = u8::MAX >> q[first].leading_zeros();
        let mut nonce = Secret(vec![0u8; self.public.q_len]);
        let mut scratch = Secret(vec![0u64; 16 * self.public.p_len]);
        let mut output = vec![0u8; 2 * self.public.q_len];
        for _ in 0..8 {
            let mut sampled = false;
            for _ in 0..128 {
                random(&mut nonce.0[first..])?;
                nonce.0[first] &= high_mask;
                if nonce_in_range(&nonce.0, q) {
                    sampled = true;
                    break;
                }
            }
            if !sampled {
                return Err(Error::InvalidKeyOrNonce);
            }
            if self.sign_once(digest, &nonce.0, &mut output, &mut scratch.0) {
                return Ok(output);
            }
        }
        Err(Error::InvalidKeyOrNonce)
    }

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

#[cfg(test)]
#[path = "dsa/tests.rs"]
mod tests;
