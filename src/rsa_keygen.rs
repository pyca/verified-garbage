//! RSA key generation (FIPS 186-5 Appendix A.1.3, as BoringSSL does it): so
//! far, one of a key's primes, and the key from its two primes.
//!
//! [`generate_prime`] draws candidates from the operating system's random
//! number generator until one is a probable prime, as BoringSSL's
//! `generate_prime` does (`VG.Spec.RsaKeyGen.generatePrime`): each candidate
//! is the verified `vg_rsa_keygen_candidate` (contract
//! `VG.Spec.RsaKeyGen.candidateContract`), which reads the candidate's
//! octets, sets its two most significant bits and its least significant
//! bit, rejects it if it is too close to the other prime (if any), or
//! divisible by a small prime, or if `gcd(c - 1, e) ≠ 1`, and otherwise
//! tests it with Miller–Rabin, with witnesses read after it. A candidate too
//! close to the other prime does not count; after `5 bits` (`8 bits` for
//! `e = 3`) rejected candidates, the generation fails. Its timing may depend
//! on the lengths, `e`, the rejected candidates (which are discarded), and
//! the number of random octets the accepted candidate's Miller–Rabin test
//! read, but not on the prime or on the other prime. On a CPU with BMI2 and
//! ADX, `vg_rsa_keygen_candidate_adx` does the same with a faster Montgomery
//! multiplication.
//!
//! [`generate_prime_from`] does the same with given random octets, which it
//! reads as one stream, each candidate from where the last one stopped.
//!
//! [`key_from_primes`] derives the private key from its two primes and the
//! public exponent, as BoringSSL's `rsa_generate_key_impl` does after
//! generating them (`VG.Spec.RsaKeyGen.keyFromPrimes`), with the verified
//! `vg_rsa_keygen_key` (contract `VG.Spec.RsaKeyGen.keyContract`): it makes
//! `p` the larger, computes `d = e⁻¹ mod lcm(p - 1, q - 1)`, refuses a `d`
//! of at most half the modulus' bits (for which BoringSSL generates both
//! primes again), computes `n`, `dP`, `dQ` and `qInv`, and checks the key as
//! BoringSSL's `RSA_check_key` does. Its timing may depend on the lengths,
//! `e`, and whether the key was refused for its small `d`, but not on the
//! primes or the key.
//!
//! This module only checks the lengths, allocates the memory the candidates
//! and the key are computed in, and counts the candidates.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa_keygen::{
    vg_rsa_keygen_candidate, vg_rsa_keygen_candidate_adx, vg_rsa_keygen_key,
};
use crate::cpu::detected;
use crate::rsa::{Backend, PrivateKey};

/// The shortest prime, in bits.
pub const MIN_PRIME_BITS: usize = 256;
/// The longest prime, in bits.
pub const MAX_PRIME_BITS: usize = 4096;

/// Why a prime or a key was not generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The prime's length is not a multiple of 64 bits from 256 to 4096.
    InvalidLength,
    /// The public exponent is not 1 to 8 bytes long.
    InvalidExponent,
    /// The other prime is not as long as the prime.
    InvalidOtherPrime,
    /// Too many candidates were rejected (`5 bits`, or `8 bits` for
    /// `e = 3`), as BoringSSL's limit.
    TooManyIterations,
    /// The random octets ran out before a candidate was accepted.
    NotEnoughRandomness,
    /// The operating system's random number generator failed.
    Randomness,
    /// The private exponent `d` has at most half the modulus' bits, for
    /// which BoringSSL generates both primes again.
    SmallPrivateExponent,
    /// `e` has no inverse modulo `lcm(p - 1, q - 1)`, `q` none modulo `p`,
    /// or the key fails a check (`n`'s length, BoringSSL's `RSA_check_key`).
    InvalidKey,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidLength => "invalid RSA prime length",
            Error::InvalidExponent => "invalid RSA public exponent length",
            Error::InvalidOtherPrime => "RSA other prime is not as long as the prime",
            Error::TooManyIterations => "too many RSA prime candidates were rejected",
            Error::NotEnoughRandomness => "not enough random octets for an RSA prime",
            Error::Randomness => "the random number generator failed",
            Error::SmallPrivateExponent => "the RSA private exponent is too small",
            Error::InvalidKey => "the RSA key from the primes is invalid",
        })
    }
}

impl core::error::Error for Error {}

/// The prime's length in bytes, and the most candidates that may be
/// rejected (`VG.Spec.RsaKeyGen.primeLimit`), after checking the arguments.
fn check(
    bits: usize,
    public_exponent: &[u8],
    other: Option<&[u8]>,
) -> Result<(usize, usize), Error> {
    if !(MIN_PRIME_BITS..=MAX_PRIME_BITS).contains(&bits) || !bits.is_multiple_of(64) {
        return Err(Error::InvalidLength);
    }
    if !(1..=8).contains(&public_exponent.len()) {
        return Err(Error::InvalidExponent);
    }
    let len = bits / 8;
    if other.is_some_and(|p| p.len() != len) {
        return Err(Error::InvalidOtherPrime);
    }
    let e3 = public_exponent[..public_exponent.len() - 1]
        .iter()
        .all(|&b| b == 0)
        && public_exponent[public_exponent.len() - 1] == 3;
    Ok((len, if e3 { 8 * bits } else { 5 * bits }))
}

/// A probable prime of `bits` bits (a multiple of 64 from 256 to 4096),
/// big-endian, with its two most significant bits set and
/// `gcd(prime - 1, e) = 1` for the public exponent `e` (big-endian, 1 to 8
/// bytes), not within `2^(bits - 100)` of `other` (big-endian, as long as
/// the prime) if it is given, from the operating system's random number
/// generator.
pub fn generate_prime(
    bits: usize,
    public_exponent: &[u8],
    other: Option<&[u8]>,
) -> Result<Vec<u8>, Error> {
    let (len, _) = check(bits, public_exponent, other)?;
    // Too few octets for a prime's Miller–Rabin test, so that the first
    // attempt always asks for more: each attempt starts again from the
    // first octet, with twice as many.
    let mut rand = vec![0u8; 16 * len];
    let mut fresh = 0;
    loop {
        if getrandom::fill(&mut rand[fresh..]).is_err() {
            // NO-COVERAGE-START
            // The operating system's random number generator does not fail
            // where the tests run.
            crate::zeroize::zeroize(&mut rand);
            return Err(Error::Randomness);
            // NO-COVERAGE-END
        }
        match generate_prime_from(bits, public_exponent, other, &rand) {
            Err(Error::NotEnoughRandomness) => {
                fresh = rand.len();
                rand.resize(2 * fresh, 0);
            }
            r => {
                // The octets hold the prime.
                crate::zeroize::zeroize(&mut rand);
                return r.map(|(prime, _)| prime);
            }
        }
    }
}

/// [`generate_prime`]'s prime from the random octets `rand`, read as one
/// stream (`VG.Spec.RsaKeyGen.generatePrime`), and the number of octets
/// read; [`Error::NotEnoughRandomness`] if they run out first.
pub fn generate_prime_from(
    bits: usize,
    public_exponent: &[u8],
    other: Option<&[u8]>,
    rand: &[u8],
) -> Result<(Vec<u8>, usize), Error> {
    let (len, limit) = check(bits, public_exponent, other)?;
    let other = other.unwrap_or(&[]);
    let mut out = vec![0u8; len];
    let mut scratch = vec![0u64; crate::rsa::scratch_words(len)];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_keygen_candidate,
        // `select` chose it because the CPU has the features it needs.
        Backend::Adx | Backend::Ifma => vg_rsa_keygen_candidate_adx,
    };
    let mut read = 0;
    let mut rejected = 0;
    let r = loop {
        let rest = &rand[read..];
        let mut used = [0u64; 1];
        // SAFETY: each pointer is valid for its length (`out`, `used` and
        // `scratch` for writes), and none overlaps another or wraps around,
        // as they are distinct Rust allocations; `check` gives
        // `out_len = bits / 8`, a multiple of 8 in 32..=512, `e_len` in
        // 1..=8 and `p_len` 0 or `out_len`; `scratch_len = 16 out_len`; and
        // the CPU has the features of the function `select` chose.
        let status = unsafe {
            f(
                out.as_mut_ptr(),
                len,
                &mut used,
                public_exponent.as_ptr(),
                public_exponent.len(),
                other.as_ptr(),
                other.len(),
                rest.as_ptr(),
                rest.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // `used` is at most `rest.len()` (`VG.Spec.RsaKeyGen.candidateOp`
        // reads no more than it has).
        read += used[0] as usize;
        match status {
            0 => break Err(Error::NotEnoughRandomness),
            1 => break Ok(()),
            // Too close to the other prime: not counted.
            2 => {}
            _ => {
                rejected += 1;
                if rejected >= limit {
                    break Err(Error::TooManyIterations);
                }
            }
        }
    };
    // The working space holds the prime.
    crate::zeroize::zeroize(&mut scratch);
    r.map(|()| (out, read))
}

/// The private key with the primes `p` and `q` (big-endian, as long as each
/// other, a multiple of 8 bytes from 32 to 512) and the public exponent `e`
/// (big-endian, 1 to 8 bytes), as BoringSSL derives it
/// (`VG.Spec.RsaKeyGen.keyFromPrimes`): `p` the larger of the two,
/// `d = e⁻¹ mod lcm(p - 1, q - 1)`, `dP = d mod (p - 1)`,
/// `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p`, after checking that `d` has
/// more than half the modulus' bits, that `n = p q` has twice the primes'
/// bits, and the key as BoringSSL's `RSA_check_key` does. It does not check
/// that `p` and `q` are prime.
pub fn key_from_primes(public_exponent: &[u8], p: &[u8], q: &[u8]) -> Result<PrivateKey, Error> {
    let len = p.len();
    if !(MIN_PRIME_BITS / 8..=MAX_PRIME_BITS / 8).contains(&len) || !len.is_multiple_of(8) {
        return Err(Error::InvalidLength);
    }
    if !(1..=8).contains(&public_exponent.len()) {
        return Err(Error::InvalidExponent);
    }
    if q.len() != len {
        return Err(Error::InvalidOtherPrime);
    }
    let mut n = vec![0u8; 2 * len];
    let mut d = vec![0u8; 2 * len];
    let (mut kp, mut kq) = (p.to_vec(), q.to_vec());
    let mut dp = vec![0u8; len];
    let mut dq = vec![0u8; len];
    let mut qinv = vec![0u8; len];
    let mut scratch = vec![0u64; crate::rsa::scratch_words(2 * len)];
    // SAFETY: each pointer is valid for its length (all but `e` for writes),
    // and none overlaps another or wraps around, as they are distinct Rust
    // allocations; `p_len` is a multiple of 8 in 32..=512, `n_len` and
    // `d_len` are `2 p_len`, the other lengths `p_len`, `e_len` is in 1..=8,
    // and `scratch_len` is `16 n_len`.
    let status = unsafe {
        vg_rsa_keygen_key(
            n.as_mut_ptr(),
            n.len(),
            d.as_mut_ptr(),
            d.len(),
            kp.as_mut_ptr(),
            kp.len(),
            kq.as_mut_ptr(),
            kq.len(),
            dp.as_mut_ptr(),
            dp.len(),
            dq.as_mut_ptr(),
            dq.len(),
            qinv.as_mut_ptr(),
            qinv.len(),
            public_exponent.as_ptr(),
            public_exponent.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    // The working space holds the key.
    crate::zeroize::zeroize(&mut scratch);
    // The outputs are zeros but for 1, and `n`'s top bit then makes `p` and
    // `q` as long as they are (`VG.Spec.RsaKeyGen.keyValid`), and `e` valid
    // (`VG.Spec.Rsa.exponentValid`), so that this is the key `PrivateKey`
    // holds.
    let key = PrivateKey {
        n,
        e: crate::rsa::trim(public_exponent).to_vec(),
        d,
        p: kp,
        q: kq,
        dp,
        dq,
        qinv,
    };
    match status {
        1 => Ok(key),
        2 => Err(Error::SmallPrivateExponent),
        _ => Err(Error::InvalidKey),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidLength,
            Error::InvalidExponent,
            Error::InvalidOtherPrime,
            Error::TooManyIterations,
            Error::NotEnoughRandomness,
            Error::Randomness,
            Error::SmallPrivateExponent,
            Error::InvalidKey,
        ] {
            assert!(!alloc::format!("{e}").is_empty());
        }
    }

    #[test]
    fn invalid() {
        for bits in [0, 128, 192, 255, 257, 4096 + 64] {
            assert_eq!(generate_prime(bits, &[3], None), Err(Error::InvalidLength));
            assert_eq!(
                generate_prime_from(bits, &[3], None, &[]),
                Err(Error::InvalidLength)
            );
        }
        assert_eq!(generate_prime(256, &[], None), Err(Error::InvalidExponent));
        assert_eq!(
            generate_prime(256, &[1; 9], None),
            Err(Error::InvalidExponent)
        );
        assert_eq!(
            generate_prime(256, &[3], Some(&[0xff; 31])),
            Err(Error::InvalidOtherPrime)
        );
        assert_eq!(
            generate_prime(256, &[3], Some(&[0xff; 33])),
            Err(Error::InvalidOtherPrime)
        );
    }

    /// Candidates from zeros: `2^255 + 2^254 + 1`, which is 1 modulo 3, so
    /// that it is rejected for `e = 3` (by trial division or the gcd).
    #[test]
    fn too_many_iterations() {
        let zeros = vec![0u8; 32 * 8 * 256];
        assert_eq!(
            generate_prime_from(256, &[3], None, &zeros),
            Err(Error::TooManyIterations)
        );
        assert_eq!(
            generate_prime_from(256, &[0, 0, 3], None, &zeros),
            Err(Error::TooManyIterations)
        );
        // `e = 15` rejects them too, but allows only `5 bits` rejections.
        assert_eq!(
            generate_prime_from(256, &[15], None, &zeros[..32 * 5 * 256]),
            Err(Error::TooManyIterations)
        );
        // One fewer is not enough.
        assert_eq!(
            generate_prime_from(256, &[3], None, &zeros[..32 * (8 * 256 - 1)]),
            Err(Error::NotEnoughRandomness)
        );
    }

    /// A candidate equal to the other prime is too close to it, which does
    /// not count as a rejection.
    #[test]
    fn too_close() {
        let mut other = [0u8; 32];
        other[0] = 0xc0;
        other[31] = 1;
        let zeros = vec![0u8; 32 * 8 * 256 + 32];
        assert_eq!(
            generate_prime_from(256, &[3], Some(&other), &zeros),
            Err(Error::NotEnoughRandomness)
        );
    }

    #[test]
    fn primes() {
        for bits in [256, 512, 1024] {
            for other in [None, Some(&[0x80u8; 128][..bits / 8])] {
                let p = generate_prime(bits, &[1, 0, 1], other).unwrap();
                assert_eq!(p.len(), bits / 8);
                assert_eq!(p[0] >> 6, 3);
                assert_eq!(p[p.len() - 1] & 1, 1);
            }
        }
    }

    #[test]
    fn key_invalid() {
        let p = [0xffu8; 32];
        for len in [0, 24, 33, 520] {
            assert_eq!(
                key_from_primes(&[3], &vec![0xff; len], &vec![0xff; len]).unwrap_err(),
                Error::InvalidLength
            );
        }
        assert_eq!(
            key_from_primes(&[], &p, &p).unwrap_err(),
            Error::InvalidExponent
        );
        assert_eq!(
            key_from_primes(&[1; 9], &p, &p).unwrap_err(),
            Error::InvalidExponent
        );
        assert_eq!(
            key_from_primes(&[3], &p, &p[1..]).unwrap_err(),
            Error::InvalidOtherPrime
        );
    }

    /// With `p = q`, `lcm(p - 1, q - 1) = p - 1`, so that `d < p`: too small,
    /// if `e` has an inverse (`p - 1` not a multiple of 3, for `e = 3`); or
    /// no key, if it has none (`p - 1` a multiple of 3).
    #[test]
    fn key_refused() {
        let mut p = [0u8; 32];
        p[0] = 0xc0;
        p[31] = 3;
        assert_eq!(
            key_from_primes(&[3], &p, &p).unwrap_err(),
            Error::SmallPrivateExponent
        );
        p[31] = 1;
        assert_eq!(
            key_from_primes(&[3], &p, &p).unwrap_err(),
            Error::InvalidKey
        );
    }

    /// Keys from primes the operating system's random octets make.
    #[test]
    fn keys() {
        for bits in [256, 512, 1024] {
            let p = generate_prime(bits, &[1, 0, 1], None).unwrap();
            let q = generate_prime(bits, &[1, 0, 1], Some(&p)).unwrap();
            let key = key_from_primes(&[1, 0, 1], &p, &q).unwrap();
            assert!(key.check_key());
            assert_eq!(key.modulus_len(), bits / 4);
            let (hi, lo) = if p > q { (&p, &q) } else { (&q, &p) };
            let [_, e, _, kp, kq, ..] = key.components();
            assert_eq!((e, kp, kq), (&[1, 0, 1][..], &hi[..], &lo[..]));
        }
    }
}
