//! RSA key generation (FIPS 186-5 Appendix A.1.3, as BoringSSL does it): a
//! key, one of a key's primes, and the key from its two primes.
//!
//! [`generate`] makes a two-prime key as BoringSSL's `RSA_generate_key_ex`
//! does, and then tests it as its `RSA_check_fips` does
//! (`VG.Spec.RsaKeyGen.generate`): it generates `p`, then `q` not too close
//! to it, with [`generate_prime`]'s verified function, derives the key from
//! them with [`key_from_primes`]'s, and generates both primes again while
//! `d` is too small; it starts again, up to four times in all, when a prime
//! took too many candidates; and it refuses a key that fails the pairwise
//! consistency test, a signature by the verified, checked private-key
//! operation ([`PrivateKey::private_op`]) that must verify with the public
//! key ([`PublicKey::public_op`]). [`generate_from`] does the same with given
//! random octets, read as one stream.
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
//! This module only checks the lengths and the exponent, allocates the
//! memory the candidates and the key are computed in, counts the candidates
//! and the generations, and compares the pairwise test's result with its
//! message.
//!
//! On AArch64, so far, the module has the primes alone (`generate_prime`
//! and `generate_prime_from`).

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa_keygen::vg_rsa_keygen_candidate;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_keygen::{vg_rsa_keygen_candidate_adx, vg_rsa_keygen_key};
use crate::cpu::detected;
use crate::rsa::Backend;
#[cfg(target_arch = "x86_64")]
use crate::rsa::{PrivateKey, PublicKey};

/// The shortest prime, in bits.
pub const MIN_PRIME_BITS: usize = 256;
/// The longest prime, in bits.
pub const MAX_PRIME_BITS: usize = 4096;

/// Why a prime or a key was not generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The prime's length is not a multiple of 64 bits from 256 to 4096.
    InvalidLength,
    /// The public exponent is not 1 to 8 bytes long or, for a key
    /// ([`generate`]), not odd from 3 to `2^32 - 1`.
    InvalidExponent,
    /// The requested modulus is longer than 8192 bits or, rounded down to a
    /// multiple of 128 bits, shorter than 512.
    InvalidModulusLength,
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
    /// The generated key failed the pairwise consistency test (a signature
    /// made with the private key did not verify with the public key): a
    /// prime was not prime.
    PairwiseTestFailed,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidLength => "invalid RSA prime length",
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidModulusLength => "invalid RSA modulus length",
            Error::InvalidOtherPrime => "RSA other prime is not as long as the prime",
            Error::TooManyIterations => "too many RSA prime candidates were rejected",
            Error::NotEnoughRandomness => "not enough random octets for an RSA prime",
            Error::Randomness => "the random number generator failed",
            Error::SmallPrivateExponent => "the RSA private exponent is too small",
            Error::InvalidKey => "the RSA key from the primes is invalid",
            Error::PairwiseTestFailed => "the RSA key failed the pairwise consistency test",
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
    let (r, read) = prime_from(len, limit, public_exponent, other, rand);
    r.map(|prime| (prime, read))
}

/// [`generate_prime_from`] of arguments [`check`] accepted (the prime's
/// length `len` in bytes, and the limit of rejected candidates), and the
/// number of octets read, also when it fails.
fn prime_from(
    len: usize,
    limit: usize,
    public_exponent: &[u8],
    other: Option<&[u8]>,
    rand: &[u8],
) -> (Result<Vec<u8>, Error>, usize) {
    let other = other.unwrap_or(&[]);
    let mut out = vec![0u8; len];
    let mut scratch = vec![0u64; crate::rsa::scratch_words(len)];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_keygen_candidate,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
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
    (r.map(|()| out), read)
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
#[cfg(target_arch = "x86_64")]
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

/// The smallest modulus [`generate`] makes, in bits.
#[cfg(target_arch = "x86_64")]
pub const MIN_MODULUS_BITS: usize = 512;
/// The largest modulus [`generate`] makes, in bits.
#[cfg(target_arch = "x86_64")]
pub const MAX_MODULUS_BITS: usize = 8192;

/// The modulus' size in bits for the requested `bits`
/// (`VG.Spec.RsaKeyGen.modulusBits`), and the public exponent without its
/// leading zero bytes, if it is valid (`VG.Spec.RsaKeyGen.exponentValid`).
#[cfg(target_arch = "x86_64")]
fn params(bits: usize, public_exponent: &[u8]) -> Result<(usize, &[u8]), Error> {
    let e = crate::rsa::trim(public_exponent);
    let v = e.iter().fold(0u64, |v, &b| v << 8 | u64::from(b));
    if e.len() > 4 || v & 1 == 0 || v < 3 {
        return Err(Error::InvalidExponent);
    }
    let nlen = bits / 128 * 128;
    if bits > MAX_MODULUS_BITS || nlen < MIN_MODULUS_BITS {
        return Err(Error::InvalidModulusLength);
    }
    Ok((nlen, e))
}

/// The message representative of BoringSSL's pairwise consistency test
/// (`VG.Spec.RsaKeyGen.pairwiseMessage`) for a `k`-byte modulus:
/// EMSA-PKCS1-v1_5 of SHA-256 with a digest of 32 zero bytes.
#[cfg(target_arch = "x86_64")]
fn pairwise_message(k: usize) -> Vec<u8> {
    const PREFIX: [u8; 19] = [
        0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
        0x05, 0x00, 0x04, 0x20,
    ];
    let mut em = vec![0xff; k];
    em[0] = 0;
    em[1] = 1;
    let t = k - PREFIX.len() - 32;
    em[t - 1] = 0;
    em[t..t + PREFIX.len()].copy_from_slice(&PREFIX);
    em[t + PREFIX.len()..].fill(0);
    em
}

/// The pairwise consistency test of BoringSSL's `RSA_check_fips`
/// (`VG.Spec.RsaKeyGen.pairwiseOk`): the message representative signed with
/// the private key, by the private-key operation checked against `e`,
/// verifies with the public key.
#[cfg(target_arch = "x86_64")]
fn pairwise_ok(key: &PrivateKey) -> bool {
    let em = pairwise_message(key.modulus_len());
    let mut s = vec![0u8; em.len()];
    key.private_op(&em, &mut s).is_ok()
        && PublicKey::new(&key.n, &key.e).is_ok_and(|public| {
            let mut v = vec![0u8; em.len()];
            public.public_op(&s, &mut v).is_ok() && v == em
        })
}

/// One generation of BoringSSL's `rsa_generate_key_impl`
/// (`VG.Spec.RsaKeyGen.generateOnce`) of a modulus of `nlen` bits and the
/// valid exponent `e`, from `rand`, and the number of octets read: `p`, then
/// `q`, each of `nlen / 2` bits, and the key from them, both primes again
/// while `d` is too small.
#[cfg(target_arch = "x86_64")]
fn generate_once(nlen: usize, e: &[u8], rand: &[u8]) -> (Result<PrivateKey, Error>, usize) {
    let bits = nlen / 2;
    // The arguments are valid: `nlen / 2` is a multiple of 64 from 256 to
    // 4096, and `e` is 1 to 4 bytes long.
    let limit = if e == [3] { 8 * bits } else { 5 * bits };
    let mut read = 0;
    loop {
        let (p, used) = prime_from(bits / 8, limit, e, None, &rand[read..]);
        read += used;
        let mut p = match p {
            Ok(p) => p,
            Err(err) => return (Err(err), read),
        };
        let (q, used) = prime_from(bits / 8, limit, e, Some(&p), &rand[read..]);
        read += used;
        let r = q.and_then(|mut q| {
            let key = key_from_primes(e, &p, &q);
            crate::zeroize::zeroize(&mut q);
            key
        });
        crate::zeroize::zeroize(&mut p);
        match r {
            // `d ≤ 2^(nlen / 2)`: both primes again.
            Err(Error::SmallPrivateExponent) => {}
            r => return (r, read),
        }
    }
}

/// A two-prime RSA private key with a modulus of `bits` bits, rounded down
/// to a multiple of 128 (from 512 to 8192 bits), and the public exponent
/// `e` (big-endian, odd, from 3 to `2^32 - 1`, with any number of leading
/// zero bytes), from the operating system's random number generator, as
/// BoringSSL's `RSA_generate_key_ex` and then its pairwise consistency test
/// make it (`VG.Spec.RsaKeyGen.generate`).
#[cfg(target_arch = "x86_64")]
pub fn generate(bits: usize, public_exponent: &[u8]) -> Result<PrivateKey, Error> {
    let (nlen, _) = params(bits, public_exponent)?;
    // Too few octets for a key, whose two primes of `nlen / 16` bytes take at
    // least 16 witnesses each, so that the first attempt always asks for
    // more: each attempt starts again from the first octet, with twice as
    // many.
    let mut rand = vec![0u8; nlen / 4];
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
        match generate_from(bits, public_exponent, &rand) {
            Err(Error::NotEnoughRandomness) => {
                fresh = rand.len();
                rand.resize(2 * fresh, 0);
            }
            r => {
                // The octets hold the primes.
                crate::zeroize::zeroize(&mut rand);
                return r.map(|(key, _)| key);
            }
        }
    }
}

/// [`generate`]'s key from the random octets `rand`, read as one stream
/// (`VG.Spec.RsaKeyGen.generate`), and the number of octets read;
/// [`Error::NotEnoughRandomness`] if they run out first. A generation that
/// fails with too many rejected candidates starts again from where it
/// stopped reading, up to four times in all.
#[cfg(target_arch = "x86_64")]
pub fn generate_from(
    bits: usize,
    public_exponent: &[u8],
    rand: &[u8],
) -> Result<(PrivateKey, usize), Error> {
    let (nlen, e) = params(bits, public_exponent)?;
    let mut read = 0;
    for _ in 0..4 {
        let (r, used) = generate_once(nlen, e, &rand[read..]);
        read += used;
        match r {
            Err(Error::TooManyIterations) => {}
            r => {
                let key = r?;
                return if pairwise_ok(&key) {
                    Ok((key, read))
                } else {
                    Err(Error::PairwiseTestFailed)
                };
            }
        }
    }
    Err(Error::TooManyIterations)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidLength,
            Error::InvalidExponent,
            Error::InvalidModulusLength,
            Error::InvalidOtherPrime,
            Error::TooManyIterations,
            Error::NotEnoughRandomness,
            Error::Randomness,
            Error::SmallPrivateExponent,
            Error::InvalidKey,
            Error::PairwiseTestFailed,
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

    #[cfg(target_arch = "x86_64")]
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
    #[cfg(target_arch = "x86_64")]
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
    #[cfg(target_arch = "x86_64")]
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

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn generate_invalid() {
        for bits in [0, 384, 511, 8192 + 1, 8192 + 128] {
            assert_eq!(
                generate(bits, &[1, 0, 1]).unwrap_err(),
                Error::InvalidModulusLength
            );
            assert_eq!(
                generate_from(bits, &[1, 0, 1], &[]).unwrap_err(),
                Error::InvalidModulusLength
            );
        }
        for e in [&[][..], &[0], &[1], &[2], &[0, 4], &[1, 0, 0, 0, 1]] {
            assert_eq!(generate(512, e).unwrap_err(), Error::InvalidExponent);
            assert_eq!(
                generate_from(512, e, &[]).unwrap_err(),
                Error::InvalidExponent
            );
        }
    }

    /// Keys from the operating system's random octets, of sizes rounded
    /// down to a multiple of 128 bits.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn generate_keys() {
        for (bits, e) in [(512, &[3][..]), (639, &[0, 0, 3]), (1024, &[1, 0, 1])] {
            let key = generate(bits, e).unwrap();
            assert!(key.check_key());
            assert_eq!(key.modulus_len(), bits / 128 * 16);
            assert_eq!(key.components()[1], crate::rsa::trim(e));
            assert!(pairwise_ok(&key));
        }
    }

    /// Candidates from zeros are rejected for `e = 3` (see
    /// `too_many_iterations`): each generation fails after `8 · 256`
    /// candidates for `p`, and the next one reads on from there, four in all.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn generate_too_many_iterations() {
        let zeros = vec![0u8; 4 * 8 * 256 * 32];
        assert_eq!(
            generate_from(512, &[3], &zeros).unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            generate_from(512, &[3], &zeros[..zeros.len() - 1]).unwrap_err(),
            Error::NotEnoughRandomness
        );
    }

    // Primes of 256 bits, and a composite, for keys of 512 bits from given
    // octets: each is read as a candidate, then as many witnesses as
    // Miller–Rabin draws for it (27 uniform ones, 32 bytes each). They were
    // found by a search with Python's integers.
    //
    // `SMALL_D_P = 8 g + 1` and `SMALL_D_Q = 10 g + 1` are primes for which
    // `lcm(p - 1, q - 1) = 40 g` is so small that `d = 65537⁻¹ mod 40 g` is
    // less than `2^256`. `PRIME` is a prime whose key with `SMALL_D_Q` has a
    // larger `d`.
    //
    // `COMPOSITE = p₁ p₂` for the primes `p₁ = 2 t + 1` and `p₂ = 2 t r + 1`
    // (`t` prime, `r` even), so that `COMPOSITE - 1 = 2 m` with `t | m`;
    // `LIAR` has order `t` modulo both primes, so that `LIAR^m ≡ 1`: a strong
    // liar for the composite, which therefore passes Miller–Rabin with it as
    // every witness. `p₁ = 0x7801a5f25ad69ed2e17d8e6adf6363`, and
    // `p₂ = 0x1999c5034690190f6755b17bcd41e2d9d55`.
    #[cfg(target_arch = "x86_64")]
    const COMPOSITE: [u8; 32] = [
        0xc0, 0x03, 0xe8, 0xba, 0x68, 0x3b, 0x19, 0x2b, 0xbb, 0x22, 0xca, 0xde, 0x1e, 0x23, 0x63,
        0xa7, 0x7a, 0x7b, 0x22, 0x91, 0x73, 0x6d, 0x49, 0x7b, 0xbe, 0x4e, 0x00, 0xba, 0x8e, 0x86,
        0xb6, 0xdf,
    ];
    #[cfg(target_arch = "x86_64")]
    const LIAR: [u8; 32] = [
        0xb3, 0xf9, 0xee, 0xa9, 0x5d, 0x1a, 0xc5, 0x0d, 0xf5, 0xdc, 0x94, 0x59, 0x6e, 0xad, 0x6d,
        0x84, 0x7c, 0x5a, 0x00, 0x11, 0xef, 0x55, 0x98, 0x40, 0x6a, 0x38, 0x6f, 0x97, 0x1a, 0x94,
        0x37, 0xda,
    ];
    #[cfg(target_arch = "x86_64")]
    const SMALL_D_P: [u8; 32] = [
        0xc4, 0x0e, 0x4b, 0xd4, 0xaf, 0x21, 0x84, 0xf0, 0x07, 0x8b, 0x20, 0x1f, 0xd1, 0xc9, 0x38,
        0x03, 0x46, 0x9d, 0x7b, 0xbe, 0xdb, 0xa1, 0x62, 0x50, 0x52, 0x1a, 0x89, 0x7e, 0x85, 0x9d,
        0x6f, 0x21,
    ];
    #[cfg(target_arch = "x86_64")]
    const SMALL_D_Q: [u8; 32] = [
        0xf5, 0x11, 0xde, 0xc9, 0xda, 0xe9, 0xe6, 0x2c, 0x09, 0x6d, 0xe8, 0x27, 0xc6, 0x3b, 0x86,
        0x04, 0x18, 0x44, 0xda, 0xae, 0x92, 0x89, 0xba, 0xe4, 0x66, 0xa1, 0x2b, 0xde, 0x27, 0x04,
        0xca, 0xe9,
    ];
    #[cfg(target_arch = "x86_64")]
    const PRIME: [u8; 32] = [
        0xc1, 0x1b, 0x69, 0x5a, 0x2d, 0x55, 0x9f, 0x49, 0x3e, 0xc4, 0x37, 0x6f, 0xbd, 0x44, 0xcf,
        0x67, 0x9c, 0xb0, 0x64, 0x2f, 0xba, 0xc4, 0x04, 0x2d, 0x74, 0x28, 0x11, 0x24, 0x50, 0x82,
        0x9e, 0x97,
    ];

    /// The octets of a 256-bit candidate `c` and its 27 witnesses `w`.
    #[cfg(target_arch = "x86_64")]
    fn candidate(c: &[u8; 32], w: &[u8; 32]) -> Vec<u8> {
        let mut v = c.to_vec();
        for _ in 0..27 {
            v.extend_from_slice(w);
        }
        v
    }

    /// A witness in the range for every candidate here.
    #[cfg(target_arch = "x86_64")]
    const W: [u8; 32] = [2; 32];

    /// The primes with the small `d` are generated, refused, and replaced.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn generate_small_d() {
        let mut rand = candidate(&SMALL_D_P, &W);
        rand.extend(candidate(&SMALL_D_Q, &W));
        assert_eq!(
            key_from_primes(&[1, 0, 1], &SMALL_D_P, &SMALL_D_Q).unwrap_err(),
            Error::SmallPrivateExponent
        );
        assert_eq!(
            generate_from(512, &[1, 0, 1], &rand).unwrap_err(),
            Error::NotEnoughRandomness
        );
        rand.extend(candidate(&PRIME, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        let (key, read) = generate_from(512, &[1, 0, 1], &rand).unwrap();
        assert_eq!(read, rand.len());
        assert!(key.check_key());
        let [_, _, _, p, q, ..] = key.components();
        assert_eq!((p, q), (&SMALL_D_Q[..], &PRIME[..]));
    }

    /// A composite `p` that passes Miller–Rabin gives a key that passes
    /// BoringSSL's `RSA_check_key`, which does not test primality, but
    /// fails the pairwise consistency test.
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn generate_composite() {
        let mut rand = candidate(&COMPOSITE, &LIAR);
        rand.extend(candidate(&SMALL_D_Q, &W));
        let key = key_from_primes(&[1, 0, 1], &COMPOSITE, &SMALL_D_Q).unwrap();
        assert!(key.check_key());
        assert!(!pairwise_ok(&key));
        assert_eq!(
            generate_from(512, &[1, 0, 1], &rand).unwrap_err(),
            Error::PairwiseTestFailed
        );
    }
}
