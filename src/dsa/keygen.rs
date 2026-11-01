//! DSA key generation (FIPS 186-4 B.1.2): x sampled uniformly from
//! `[1, q)` by rejection, then `y = g^x mod p`, for a domain the caller
//! assures is prime.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use alloc::{vec, vec::Vec};
#[cfg(any(target_arch = "aarch64", target_arch = "powerpc64"))]
use core::sync::atomic::AtomicU8;

use super::{Backend, Error, PrivateKey, PublicKey, Secret};
use crate::arch::dsa::vg_dsa_generate_key;
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::vg_dsa_generate_key_adx;
use crate::cpu::detected;

// On x86, give one call of the verified sampler eight draws, so that a
// common rejection does not repeat its check of the domain. Eight draws use
// at most 256 random bytes; the sampler still enforces its 128-draw limit.
#[cfg(target_arch = "x86")]
const DRAW_BATCH: usize = 8;
#[cfg(not(target_arch = "x86"))]
const DRAW_BATCH: usize = 1;

impl PrivateKey {
    /// Import big-endian `p`, `q`, `g` and `x`, deriving `y = g^x mod p`.
    /// This accepts private components from PKCS#8, which omits `y`.
    /// `g` must have `p`'s width and `x` must have `q`'s width.
    /// Checks the domain's algebraic consistency and `0 < x < q`;
    /// callers must assure domain primality separately.
    /// Available on x86, x86-64, AArch64, 32-bit ARM and PPC64LE.
    pub fn from_private_components(p: &[u8], q: &[u8], g: &[u8], x: &[u8]) -> Result<Self, Error> {
        if !matches!(
            (p.len(), q.len()),
            (128, 20) | (256, 20 | 28 | 32) | (384, 32)
        ) || g.len() != p.len()
            || x.len() != q.len()
        {
            return Err(Error::Length);
        }
        let (p_len, q_len) = (p.len(), q.len());
        let mut params = Vec::with_capacity(2 * p_len + q_len);
        for component in [p, q, g] {
            params.extend_from_slice(component);
        }
        let backend = Backend::select(detected());
        let mut output = Secret(vec![0u8; 3 * p_len + 2 * q_len]);
        let mut scratch = Secret(vec![0u64; 16 * p_len]);
        let derive = match backend {
            Backend::Baseline => crate::arch::dsa::vg_dsa_derive_key,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => crate::arch::dsa::vg_dsa_derive_key_adx,
        };
        // SAFETY: the checks establish the supported widths and buffer sizes.
        // Output and scratch are separate allocations, disjoint from all inputs.
        // Backend selection establishes the required CPU features. Both secret
        // allocations are wiped on drop, including on failure.
        let status = unsafe {
            derive(
                output.0.as_mut_ptr(),
                output.0.len(),
                params.as_ptr(),
                params.len(),
                p_len,
                x.as_ptr(),
                q_len,
                scratch.0.as_mut_ptr(),
                scratch.0.len(),
            )
        };
        if status != 1 {
            return Err(Error::InvalidKeyOrNonce);
        }
        Ok(Self {
            public: PublicKey {
                packed: output.0[..3 * p_len + q_len].to_vec(),
                p_len,
                q_len,
                backend,
                #[cfg(any(target_arch = "aarch64", target_arch = "powerpc64"))]
                validated: AtomicU8::new(0),
            },
            packed: output,
        })
    }

    /// Generate a key for the big-endian domain `p`, `q` and `g`, sampling
    /// `x` uniformly from `[1, q)` with the operating system's random number
    /// generator and computing `y = g^x mod p`. `g` must have `p`'s width.
    ///
    /// The domain's algebraic consistency is checked before the assembly consumes
    /// the random tape; callers must assure its primality separately. At most 128 draws
    /// are made, so an invalid `q` returns an error instead of retrying
    /// indefinitely.
    pub fn generate(p: &[u8], q: &[u8], g: &[u8]) -> Result<Self, Error> {
        Self::generate_with_rng(p, q, g, |buf| {
            getrandom::fill(buf).map_err(|_| Error::Randomness)
        })
    }

    /// [`generate`](Self::generate), with `x` drawn from `random` instead
    /// of the operating system.
    ///
    /// Not part of the API: it lets benchmarks compare implementations on
    /// identical work, from fixed tapes. The key is secret only if `random`
    /// supplies uniformly random bytes.
    #[doc(hidden)]
    pub fn generate_with_rng(
        p: &[u8],
        q: &[u8],
        g: &[u8],
        mut random: impl FnMut(&mut [u8]) -> Result<(), Error>,
    ) -> Result<Self, Error> {
        if !matches!(
            (p.len(), q.len()),
            (128, 20) | (256, 20 | 28 | 32) | (384, 32)
        ) || g.len() != p.len()
        {
            return Err(Error::Length);
        }
        let (p_len, q_len) = (p.len(), q.len());
        let mut params = Vec::with_capacity(2 * p_len + q_len);
        for component in [p, q, g] {
            params.extend_from_slice(component);
        }
        let backend = Backend::select(detected());
        // A draw never takes more than q_len bytes.
        let mut tape = Secret(vec![0u8; DRAW_BATCH * q_len]);
        random(&mut tape.0)?;
        let mut scratch = Secret(vec![0u64; 64 * p_len + 1024]);
        let mut output = Secret(vec![0u8; 3 * p_len + 2 * q_len]);
        loop {
            let mut used = [0u64; 1];
            macro_rules! generate {
                ($function:path) => {
                    // SAFETY: the checks above establish supported widths,
                    // params_len = 2*p_len + q_len and out_len =
                    // 3*p_len + 2*q_len. All writable buffers are separate
                    // owned allocations, disjoint from the domain and the
                    // random tape. Scratch has the contract's 64*p_len + 1024
                    // words, and backend selection establishes CPU features.
                    unsafe {
                        $function(
                            output.0.as_mut_ptr(),
                            output.0.len(),
                            &mut used,
                            params.as_ptr(),
                            params.len(),
                            p_len,
                            q_len,
                            tape.0.as_ptr(),
                            tape.0.len(),
                            scratch.0.as_mut_ptr(),
                            scratch.0.len(),
                        )
                    }
                };
            }
            let status = match backend {
                Backend::Baseline => generate!(vg_dsa_generate_key),
                #[cfg(target_arch = "x86_64")]
                Backend::Adx => generate!(vg_dsa_generate_key_adx),
            };
            match status {
                1 => break,
                2 => {
                    // The contract permits extending an exhausted tape and
                    // replaying the same generation; never reuse it for another.
                    let start = tape.0.len();
                    tape.0.resize(start + DRAW_BATCH * q_len, 0);
                    random(&mut tape.0[start..])?;
                }
                _ => return Err(Error::InvalidKeyOrNonce),
            }
        }
        let public = PublicKey {
            packed: output.0[..3 * p_len + q_len].to_vec(),
            p_len,
            q_len,
            backend,
            #[cfg(any(target_arch = "aarch64", target_arch = "powerpc64"))]
            validated: AtomicU8::new(0),
        };
        // The packed private key p || q || g || y || x is the output itself.
        Ok(Self {
            public,
            packed: Secret(core::mem::take(&mut output.0)),
        })
    }
}

#[cfg(test)]
mod tests;
