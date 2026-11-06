//! The whole generation in verified code, `vg_rsa_generate`
//! (`VG.Spec.RsaKeyGen.generate`), served random tapes
//! ([`crate::entropy::serve`]).

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;

use super::Error;
use crate::arch::rsa_keygen::{vg_rsa_generate, vg_rsa_generate_adx, vg_rsa_generate_init};
use crate::cpu::detected;
use crate::entropy::{Step, Stop, serve};
use crate::rsa::{Backend, PrivateKey};

/// [`super::generate`], with its random octets drawn from `random`, and the
/// octets of the stream it consumed.
pub(super) fn generate_counted(
    bits: usize,
    public_exponent: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> (Result<PrivateKey, Error>, usize) {
    let mut state = [0u64; 7];
    // SAFETY: `state` is valid for writes and `public_exponent` for reads of
    // its length.
    let init = unsafe {
        vg_rsa_generate_init(
            &mut state,
            bits,
            public_exponent.as_ptr(),
            public_exponent.len(),
        )
    };
    match init {
        1 => {}
        0 => return (Err(Error::InvalidExponent), 0),
        _ => return (Err(Error::InvalidModulusLength), 0),
    }
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_generate,
        // `select` chose it because the CPU has the features it needs.
        Backend::Adx | Backend::Ifma => vg_rsa_generate_adx,
    };
    let len = state[1] as usize;
    let mut key = vec![0u8; 9 * len];
    let mut scratch = vec![0u64; crate::rsa::scratch_words(2 * len)];
    let (mut status, mut consumed) = (0, 0);
    let served = serve(state[3] as usize, random, |tape| {
        let mut used = [0u64; 1];
        // SAFETY: each pointer is valid for its length (all but `tape` for
        // writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; `state` is from `vg_rsa_generate_init`
        // or from the last call, with the same `key`, which returned 0;
        // `key_len` is `9 state[1]`; the tape is as long as the length
        // `state[3]` asked for, which is at most the budget, `state[2]`;
        // `scratch_len` is `32 state[1] + 32`; and the CPU has the features
        // of the function `select` chose.
        status = unsafe {
            f(
                key.as_mut_ptr(),
                key.len(),
                &mut used,
                tape.as_ptr(),
                tape.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
                &mut state,
            )
        };
        consumed += used[0] as usize;
        match status {
            0 => Step::More {
                used: used[0] as usize,
                requested: state[3] as usize,
            },
            1 => Step::Done,
            _ => Step::Failed,
        }
    });
    // The working space holds the primes and the key.
    crate::zeroize::zeroize(&mut scratch);
    let r = match served {
        Ok(()) => Ok(key_from(&key, len, public_exponent)),
        Err(Stop::Fill(e)) => Err(e),
        Err(Stop::Failed) if status == 2 => Err(Error::InvalidKey),
        Err(Stop::Failed) => Err(Error::TooManyIterations),
    };
    crate::zeroize::zeroize(&mut key);
    (r, consumed)
}

/// The key `vg_rsa_generate` wrote to `key` when it returned 1: `n` and `d`
/// of `2 len` octets, then `p`, `q`, `dP`, `dQ` and `qInv` of `len`, a key
/// `PrivateKey` holds (`VG.Spec.RsaKeyGen.keyValid`, and one BoringSSL's
/// `RSA_check_key` accepts), with the exponent `vg_rsa_generate_init`
/// accepted.
fn key_from(key: &[u8], len: usize, public_exponent: &[u8]) -> PrivateKey {
    let (n, rest) = key.split_at(2 * len);
    let (d, rest) = rest.split_at(2 * len);
    let [p, q, dp, dq, qinv] = core::array::from_fn(|i| rest[i * len..][..len].to_vec());
    PrivateKey {
        n: n.to_vec(),
        e: crate::rsa::trim(public_exponent).to_vec(),
        d: d.to_vec(),
        p,
        q,
        dp,
        dq,
        qinv,
    }
}

/// [`super::generate`], with its random octets drawn from `random`.
pub(super) fn generate_from(
    bits: usize,
    public_exponent: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<PrivateKey, Error> {
    generate_counted(bits, public_exponent, random).0
}

#[cfg(test)]
pub(super) mod tests {
    use super::{Error, PrivateKey, generate_counted};

    /// A key of 512 bits for `e` from `rand` as one stream, and the octets
    /// it consumed; [`Error::Randomness`] if it needed more than `rand`. A
    /// tape that reaches past its end is padded with zeros, and the result
    /// discarded if the generation consumed them.
    pub(in crate::rsa::keygen) fn generate_from(
        e: &[u8],
        rand: &[u8],
    ) -> (Result<PrivateKey, Error>, usize) {
        let mut filled = 0;
        let (r, read) = generate_counted(512, e, |out: &mut [u8]| {
            if filled >= rand.len() {
                return Err(Error::Randomness);
            }
            for b in out {
                *b = rand.get(filled).copied().unwrap_or(0);
                filled += 1;
            }
            Ok(())
        });
        (
            if read > rand.len() {
                Err(Error::Randomness)
            } else {
                r
            },
            read,
        )
    }
}
