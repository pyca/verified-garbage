//! RSA key generation (FIPS 186-5 Appendix A.1.3, as BoringSSL does it).
//!
//! The timing may depend on the lengths, `e`, the rejected candidates (which
//! are discarded), how many random octets the accepted candidates' Miller–Rabin
//! tests read, and whether a key was refused for its small `d`, but not on the
//! primes or the key. There is no FIPS 140 pairwise consistency test
//! (BoringSSL's `RSA_check_fips`): the key passes BoringSSL's `RSA_check_key`,
//! and every private-key operation releases its result only if it checks
//! against `e`.

#![cfg(all(
    any(
        target_arch = "x86_64",
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64",
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

use alloc::vec;
use core::fmt;

use crate::arch::dispatch::rsa_keygen::vg_rsa_generate_auto;
use crate::arch::rsa_keygen::vg_rsa_generate_init;
use crate::entropy::{Step, Stop, serve};
use crate::rsa::{BigUint, PrivateKey};

/// Why a key was not generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The public exponent is not odd from 3 to `2^32 - 1`.
    InvalidExponent,
    /// The requested modulus is longer than 8192 bits or, rounded down to a
    /// multiple of 128 bits, shorter than 512.
    InvalidModulusLength,
    /// Too many candidates for a prime were rejected (`5 bits`, or `8 bits`
    /// for `e = 3`, BoringSSL's limit), in each of four generations.
    TooManyIterations,
    /// The operating system's random number generator failed.
    Randomness,
    /// `e` has no inverse modulo `lcm(p - 1, q - 1)`, `q` none modulo `p`,
    /// or the key fails a check (`n`'s length, BoringSSL's `RSA_check_key`).
    InvalidKey,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidModulusLength => "invalid RSA modulus length",
            Error::TooManyIterations => "too many RSA prime candidates were rejected",
            Error::Randomness => "the random number generator failed",
            Error::InvalidKey => "the RSA key from the primes is invalid",
        })
    }
}

impl core::error::Error for Error {}

/// Fill from the operating system; injectable at the buffer boundary in tests.
fn fill_random(out: &mut [u8]) -> Result<(), Error> {
    getrandom::fill(out).map_err(|_| {
        // NO-COVERAGE-START
        // The operating system's random number generator does not fail
        // where the tests run.
        Error::Randomness
    })
    // NO-COVERAGE-END
}

/// A two-prime RSA private key with a modulus of `bits` bits, rounded down
/// to a multiple of 128 (from 512 to 8192 bits), and the public exponent
/// `e` (odd, from 3 to `2^32 - 1`; its bytes may have any number of leading
/// zero bytes), from the operating system's random number generator, as
/// BoringSSL's `RSA_generate_key_ex` makes it (`VG.Spec.RsaKeyGen.generate`).
pub fn generate(bits: usize, public_exponent: BigUint<'_>) -> Result<PrivateKey, Error> {
    generate_from(bits, public_exponent.as_be_bytes(), fill_random)
}

/// [`generate`], with its random octets drawn from `random` instead of the
/// operating system.
///
/// Not part of the API: it lets benchmarks measure [`generate`] on
/// identical work, from fixed tapes. The key is secret only if `random`
/// supplies uniformly random octets, never reused.
#[cfg(feature = "internal-bench")]
#[doc(hidden)]
pub fn generate_with_rng(
    bits: usize,
    public_exponent: BigUint<'_>,
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<PrivateKey, Error> {
    generate_from(bits, public_exponent.as_be_bytes(), random)
}

/// [`generate`], with its random octets drawn from `random`, and the
/// octets of the stream it consumed.
fn generate_counted(
    bits: usize,
    public_exponent: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> (Result<PrivateKey, Error>, usize) {
    crate::dit::enter!(dit);
    let mut state = [0u64; 7];
    // SAFETY: `state` is valid for writes and `public_exponent` for reads of
    // its length.
    let init = unsafe {
        vg_rsa_generate_init(
            dit,
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
        // `scratch_len` is `32 state[1] + 32`; and the dispatcher calls only
        // an implementation the CPU has the features of.
        status = unsafe {
            vg_rsa_generate_auto(
                dit,
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

/// [`generate`], with its random octets drawn from `random`.
fn generate_from(
    bits: usize,
    public_exponent: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<PrivateKey, Error> {
    generate_counted(bits, public_exponent, random).0
}

#[cfg(test)]
mod tests {
    use super::{BigUint, Error, PrivateKey, generate, generate_counted};
    use alloc::vec;
    use alloc::vec::Vec;

    /// Whether `key` loads again from its CRT values: whether BoringSSL's
    /// `RSA_check_key` accepts it (`PrivateKey::from_crt`).
    fn reloads(key: &PrivateKey) -> bool {
        let c = key.components().map(BigUint::as_be_bytes);
        PrivateKey::from_crt_bytes(c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]).is_ok()
    }

    /// A key of 512 bits for `e` from `rand` as one stream, and the octets
    /// it consumed; [`Error::Randomness`] if it needed more than `rand`. A
    /// tape that reaches past its end is padded with zeros, and the result
    /// discarded if the generation consumed them.
    fn generate_from(e: &[u8], rand: &[u8]) -> (Result<PrivateKey, Error>, usize) {
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

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidExponent,
            Error::InvalidModulusLength,
            Error::TooManyIterations,
            Error::Randomness,
            Error::InvalidKey,
        ] {
            assert!(!alloc::format!("{e}").is_empty());
        }
    }

    #[test]
    fn generate_invalid() {
        for bits in [0, 384, 511, 8192 + 1, 8192 + 128] {
            assert_eq!(
                generate(bits, BigUint::from_be_bytes(&[1, 0, 1])).unwrap_err(),
                Error::InvalidModulusLength
            );
        }
        for e in [&[][..], &[0], &[1], &[2], &[0, 4], &[1, 0, 0, 0, 1]] {
            assert_eq!(
                generate(512, BigUint::from_be_bytes(e)).unwrap_err(),
                Error::InvalidExponent
            );
        }
    }

    /// Keys from the operating system's random octets, of sizes rounded
    /// down to a multiple of 128 bits.
    #[test]
    fn generate_keys() {
        for (bits, e) in [(512, &[3][..]), (639, &[0, 0, 3]), (1024, &[1, 0, 1])] {
            let key = generate(bits, BigUint::from_be_bytes(e)).unwrap();
            assert!(reloads(&key));
            assert_eq!(key.modulus_len(), bits / 128 * 16);
            assert_eq!(key.components()[1].as_be_bytes(), crate::rsa::trim(e));
        }
    }

    /// Candidates from zeros are rejected for `e = 3` (see
    /// `too_many_iterations`): each generation fails after `8 · 256`
    /// candidates for `p`, and the next one reads on from there, four in all.
    #[test]
    fn generate_too_many_iterations() {
        let zeros = vec![0u8; 4 * 8 * 256 * 32];
        assert_eq!(
            generate_from(&[3], &zeros).0.unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            generate_from(&[3], &zeros[..zeros.len() - 1])
                .0
                .unwrap_err(),
            Error::Randomness
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
    const COMPOSITE: [u8; 32] = [
        0xc0, 0x03, 0xe8, 0xba, 0x68, 0x3b, 0x19, 0x2b, 0xbb, 0x22, 0xca, 0xde, 0x1e, 0x23, 0x63,
        0xa7, 0x7a, 0x7b, 0x22, 0x91, 0x73, 0x6d, 0x49, 0x7b, 0xbe, 0x4e, 0x00, 0xba, 0x8e, 0x86,
        0xb6, 0xdf,
    ];
    const LIAR: [u8; 32] = [
        0xb3, 0xf9, 0xee, 0xa9, 0x5d, 0x1a, 0xc5, 0x0d, 0xf5, 0xdc, 0x94, 0x59, 0x6e, 0xad, 0x6d,
        0x84, 0x7c, 0x5a, 0x00, 0x11, 0xef, 0x55, 0x98, 0x40, 0x6a, 0x38, 0x6f, 0x97, 0x1a, 0x94,
        0x37, 0xda,
    ];
    const SMALL_D_P: [u8; 32] = [
        0xc4, 0x0e, 0x4b, 0xd4, 0xaf, 0x21, 0x84, 0xf0, 0x07, 0x8b, 0x20, 0x1f, 0xd1, 0xc9, 0x38,
        0x03, 0x46, 0x9d, 0x7b, 0xbe, 0xdb, 0xa1, 0x62, 0x50, 0x52, 0x1a, 0x89, 0x7e, 0x85, 0x9d,
        0x6f, 0x21,
    ];
    const SMALL_D_Q: [u8; 32] = [
        0xf5, 0x11, 0xde, 0xc9, 0xda, 0xe9, 0xe6, 0x2c, 0x09, 0x6d, 0xe8, 0x27, 0xc6, 0x3b, 0x86,
        0x04, 0x18, 0x44, 0xda, 0xae, 0x92, 0x89, 0xba, 0xe4, 0x66, 0xa1, 0x2b, 0xde, 0x27, 0x04,
        0xca, 0xe9,
    ];
    const PRIME: [u8; 32] = [
        0xc1, 0x1b, 0x69, 0x5a, 0x2d, 0x55, 0x9f, 0x49, 0x3e, 0xc4, 0x37, 0x6f, 0xbd, 0x44, 0xcf,
        0x67, 0x9c, 0xb0, 0x64, 0x2f, 0xba, 0xc4, 0x04, 0x2d, 0x74, 0x28, 0x11, 0x24, 0x50, 0x82,
        0x9e, 0x97,
    ];

    // `SHARED = p₁ p₃` is another composite with `COMPOSITE`'s factor `p₁`,
    // for the prime `p₃ = 2 t s + 1` (`s` even), and `SHARED_LIAR` a strong
    // liar for it, of order `t` modulo `p₁` and `p₃`, as `LIAR` is for
    // `COMPOSITE`: `p₃ = 0x1a1757bccb88e662d83f64bd335662f8011`. They were
    // found by a search with Python's integers.
    const SHARED: [u8; 32] = [
        0xc3, 0xb1, 0xc2, 0x19, 0x60, 0x4a, 0xbb, 0xa7, 0xd5, 0x02, 0x23, 0xcc, 0x4f, 0xa2, 0x39,
        0x41, 0x65, 0x81, 0xac, 0xbf, 0xd1, 0x57, 0xd5, 0x98, 0x0a, 0xa6, 0x59, 0x00, 0x7b, 0xb4,
        0x19, 0x93,
    ];
    const SHARED_LIAR: [u8; 32] = [
        0x89, 0xf0, 0xec, 0x89, 0xe1, 0x45, 0xe8, 0x6e, 0x67, 0xf5, 0x3d, 0xda, 0x0f, 0xe6, 0x9b,
        0xe0, 0x5b, 0xa9, 0xe9, 0x3e, 0x84, 0x78, 0xe9, 0xa1, 0x38, 0x3c, 0x19, 0x6e, 0xff, 0x61,
        0x0c, 0xf9,
    ];

    /// The octets of a 256-bit candidate `c` and its 27 witnesses `w`.
    fn candidate(c: &[u8; 32], w: &[u8; 32]) -> Vec<u8> {
        let mut v = c.to_vec();
        for _ in 0..27 {
            v.extend_from_slice(w);
        }
        v
    }

    /// A witness in the range for every candidate here.
    const W: [u8; 32] = [2; 32];

    /// A generation whose source fails releases no key, even after it
    /// accepted a prime.
    #[test]
    fn fill_fails() {
        let mut fills = 0;
        let rand = candidate(&PRIME, &W);
        let mut position = 0;
        let r = super::generate_from(512, &[1, 0, 1], |out: &mut [u8]| {
            fills += 1;
            if fills == 2 {
                return Err(Error::Randomness);
            }
            for b in out {
                *b = rand.get(position).copied().unwrap_or(0);
                position += 1;
            }
            Ok(())
        });
        assert_eq!(r.unwrap_err(), Error::Randomness);
    }

    /// The primes with the small `d` are generated, refused, and replaced,
    /// after rejected candidates, across candidate, witness and prime
    /// boundaries.
    #[test]
    fn generate_small_d() {
        let mut rand = vec![0xff; 32 * 3]; // Divisible by 3.
        rand.extend(candidate(&SMALL_D_P, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        assert_eq!(
            generate_from(&[1, 0, 1], &rand).0.unwrap_err(),
            Error::Randomness
        );
        rand.extend(candidate(&PRIME, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        let (key, read) = generate_from(&[1, 0, 1], &rand);
        let key = key.unwrap();
        assert_eq!(read, rand.len());
        assert!(reloads(&key));
        let [_, _, _, p, q, ..] = key.components().map(BigUint::as_be_bytes);
        assert_eq!((p, q), (&SMALL_D_Q[..], &PRIME[..]));
    }

    /// A composite `p` that passes Miller–Rabin gives a key that passes
    /// BoringSSL's `RSA_check_key`, which does not test primality: the
    /// generation returns it, as BoringSSL's `RSA_generate_key_ex` does, and
    /// its private-key operations never release a result (the message of
    /// FIPS 140's pairwise consistency test, which would have refused it,
    /// fails its check against `e`).
    #[test]
    fn generate_composite() {
        let mut rand = candidate(&COMPOSITE, &LIAR);
        rand.extend(candidate(&SMALL_D_Q, &W));
        let (key, read) = generate_from(&[1, 0, 1], &rand);
        let key = key.unwrap();
        assert_eq!(read, rand.len());
        assert!(reloads(&key));
        assert_eq!(key.components()[4].as_be_bytes(), COMPOSITE);
        assert_eq!(
            key.sign_pkcs1v15(&[0; 32], crate::rsa::pkcs1_sig::Hash::Sha256),
            Err(crate::rsa::pkcs1_sig::Error::Fault)
        );
    }

    /// Two composites that pass Miller–Rabin and share a factor: `q` has no
    /// inverse modulo `p`, so the key from them fails its check, which is
    /// the generation's error, not a reason to draw the primes again.
    #[test]
    fn generate_key_check_fails() {
        let mut rand = candidate(&COMPOSITE, &LIAR);
        rand.extend(candidate(&SHARED, &SHARED_LIAR));
        let (key, read) = generate_from(&[1, 0, 1], &rand);
        assert_eq!(key.unwrap_err(), Error::InvalidKey);
        assert_eq!(read, rand.len());
    }
}
