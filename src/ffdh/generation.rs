//! Randomness and bounded retries for probable safe-prime generation.
#[cfg(target_arch = "aarch64")]
use super::arithmetic::{Montgomery, bits, canonical, minus_one, value_cmp};
use super::{Error, MAX_BITS, MIN_BITS, Parameters};
#[cfg(target_arch = "aarch64")]
use crate::zeroize::zeroize;
use alloc::vec;
#[cfg(target_arch = "aarch64")]
use alloc::vec::Vec;

/// Independent uniform integer in [1,upper-1]. The top-bit mask and byte
/// width are public. Only acceptance/rejection controls a branch. The
/// accepted scalar's leading-zero count is never inspected.
#[cfg(target_arch = "aarch64")]
fn sample<E>(
    upper: &[u8],
    fill: &mut impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Vec<u8>, Error> {
    let mut x = vec![0; upper.len()];
    let mask = 0xff >> (8 * upper.len() - bits(upper));
    for _ in 0..128 {
        if fill(&mut x).is_err() {
            zeroize(&mut x);
            return Err(Error::Randomness);
        }
        x[0] &= mask;
        let mut borrow = 0u16;
        let mut nonzero = 0;
        for (&a, &b) in x.iter().rev().zip(upper.iter().rev()) {
            borrow = (u16::from(a).wrapping_sub(u16::from(b) + borrow) >> 8) & 1;
            nonzero |= a;
        }
        if borrow == 1 && nonzero != 0 {
            return Ok(x);
        }
    }
    zeroize(&mut x);
    Err(Error::TooManyIterations)
}

pub(super) fn parameters<E>(
    size: usize,
    generator: u32,
    fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    parameters_limit(
        size,
        generator,
        size.saturating_mul(size).saturating_mul(64),
        fill,
    )
}

#[cfg(target_arch = "x86_64")]
fn parameters_limit<E>(
    size: usize,
    generator: u32,
    limit: usize,
    mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    if !(MIN_BITS..=MAX_BITS).contains(&size) || ![2, 5].contains(&generator) {
        return Err(Error::InvalidParameters);
    }
    let len = size.div_ceil(8);
    let mut p = vec![0; len];
    let mut scratch = crate::rsa::Scratch::new(16 * len + 32);
    // Include a first witness so candidates rejected by their first
    // Miller–Rabin round do not need to replay Montgomery preparation.
    let mut tape = vec![0; 2 * len];
    // Bound entropy consumption even when a failed RNG keeps producing
    // rejected witnesses. The verified routine owns witness selection and
    // round counts; Rust only extends the same tape and replays it.
    let max_tape = (1 + (1 << 15)) * len;
    for _ in 0..limit {
        tape.truncate(2 * len);
        fill(&mut tape).map_err(|_| Error::Randomness)?;
        loop {
            let (status, _) =
                super::x86_64::parameter_candidate(size, generator, &tape, &mut p, &mut scratch);
            match status {
                1 => return Parameters::from_components(&p, &generator.to_be_bytes(), None),
                2 => break,
                // Exhaustion consumes no tape. Preserve its entire prefix
                // when appending fresh entropy, including rejected draws.
                0 => {
                    if tape.len() == max_tape {
                        return Err(Error::TooManyIterations);
                    }
                    let old_len = tape.len();
                    tape.resize((2 * old_len).min(max_tape), 0);
                    fill(&mut tape[old_len..]).map_err(|_| Error::Randomness)?;
                }
                // The verified contract returns only 0, 1 or 2.
                // NO-COVERAGE-START
                _ => unreachable!(),
                // NO-COVERAGE-END
            }
        }
    }
    Err(Error::TooManyIterations)
}

#[cfg(target_arch = "aarch64")]
fn parameters_limit<E>(
    size: usize,
    generator: u32,
    limit: usize,
    mut fill: impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<Parameters, Error> {
    if !(MIN_BITS..=MAX_BITS).contains(&size) || ![2, 5].contains(&generator) {
        return Err(Error::InvalidParameters);
    }
    let len = size.div_ceil(8);
    let mut p = vec![0; len];
    // A generous finite cap; no unbounded loop under a failed RNG.
    for _ in 0..limit {
        fill(&mut p).map_err(|_| Error::Randomness)?;
        p[0] &= 0xff >> (8 * len - size);
        p[0] |= 1 << ((size - 1) % 8);
        p[len - 1] |= 1;
        let shape = if generator == 2 {
            rem_small(&p, 24) == 11
        } else {
            [3, 7].contains(&rem_small(&p, 10))
        };
        if !shape {
            continue;
        }
        let mut q = minus_one(&p);
        halve(&mut q);
        if trial_composite(&p) || trial_composite(&q) {
            continue;
        }
        // Test q first: most candidates fail before p needs exponentiation.
        if probable_prime(&q, &mut fill)? && probable_prime(&p, &mut fill)? {
            return Parameters::from_components(&p, &generator.to_be_bytes(), None);
        }
    }
    Err(Error::TooManyIterations)
}
#[cfg(target_arch = "aarch64")]
fn rem_small(n: &[u8], divisor: u32) -> u32 {
    n.iter().fold(0, |r, &b| (256 * r + u32::from(b)) % divisor)
}
#[cfg(target_arch = "aarch64")]
fn trial_composite(p: &[u8]) -> bool {
    (3..=251)
        .step_by(2)
        .filter(|&d| (3..d).step_by(2).all(|s| d % s != 0))
        .any(|d| rem_small(p, d) == 0 && value_cmp(p, &d.to_be_bytes()).is_ne())
}
#[cfg(target_arch = "aarch64")]
fn halve(n: &mut [u8]) {
    let mut carry = 0;
    for b in n {
        let next = *b & 1;
        *b = (*b >> 1) | (carry << 7);
        carry = next;
    }
}
/// Public probable-primality test. Independent uniform witnesses, never
/// fixed bases or RSA's lower random-candidate-specific round counts.
#[cfg(target_arch = "aarch64")]
fn probable_prime<E>(
    p: &[u8],
    fill: &mut impl FnMut(&mut [u8]) -> Result<(), E>,
) -> Result<bool, Error> {
    let p = canonical(p);
    if value_cmp(p, &[2]).is_le() {
        return Ok(p == [2]);
    }
    if p[p.len() - 1] & 1 == 0 || trial_composite(p) {
        return Ok(false);
    }
    if p == [3] {
        return Ok(true);
    }
    let p1 = minus_one(p);
    let mut d = p1.clone();
    let mut s = 0;
    while d[d.len() - 1] & 1 == 0 {
        halve(&mut d);
        s += 1;
    }
    let mont = Montgomery::new(p);
    for _ in 0..if bits(p) <= 2048 { 64 } else { 128 } {
        let mut witness = None;
        for _ in 0..128 {
            let a = sample(&p1, fill)?;
            if value_cmp(&a, &[2]).is_ge() {
                witness = Some(a);
                break;
            }
        }
        let a = witness.ok_or(Error::TooManyIterations)?;
        if !mont.strong_probable_prime(&a, s) {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn rejection_sampler_bounds_and_error() {
        let mut zero = |out: &mut [u8]| {
            out.fill(0);
            Ok::<_, ()>(())
        };
        assert_eq!(sample(&[17], &mut zero), Err(Error::TooManyIterations));
        let mut high = |out: &mut [u8]| {
            out.fill(0xff);
            Ok::<_, ()>(())
        };
        assert_eq!(sample(&[17], &mut high), Err(Error::TooManyIterations));
        assert_eq!(sample(&[17], &mut |_| Err(())), Err(Error::Randomness));
        let mut calls = 0;
        let x = sample(&[0x01, 0x01], &mut |out| {
            calls += 1;
            out.copy_from_slice(if calls == 1 { &[1, 1] } else { &[0, 1] });
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(x, [0, 1]);
        assert_eq!(calls, 2);
    }
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn probable_prime_and_witness_failures() {
        let mut two = |out: &mut [u8]| {
            out.fill(0);
            *out.last_mut().unwrap() = 2;
            Ok::<_, ()>(())
        };
        for n in [0u32, 1, 4, 9, 15, 257 * 263, 3215031751] {
            assert!(!probable_prime(&n.to_be_bytes(), &mut two).unwrap());
        }
        for n in [2u32, 3, 5, 17, 257, 65537] {
            assert!(probable_prime(&n.to_be_bytes(), &mut two).unwrap());
        }
        // A nontrivial square root of 1 modulo 257*269. Its odd-power
        // residue is neither 1 nor -1, then squares to 1: Miller–Rabin
        // must reject this composite before exhausting the square loop.
        let composite = 257u32 * 269;
        let root = (1u32..269)
            .map(|k| 1 + 257 * k)
            .find(|a| a % 269 == 268)
            .unwrap();
        assert!(
            !probable_prime(&composite.to_be_bytes(), &mut |out| {
                let bytes = root.to_be_bytes();
                out.copy_from_slice(&bytes[4 - out.len()..]);
                Ok::<_, ()>(())
            })
            .unwrap()
        );
        assert_eq!(
            probable_prime(&[17], &mut |_| Err(())),
            Err(Error::Randomness)
        );
        assert_eq!(
            probable_prime(&[17], &mut |out| {
                out.fill(1);
                Ok::<_, ()>(())
            }),
            Err(Error::TooManyIterations)
        );
        // Public witness 3 for 17 exercises the repeated-square success path.
        assert!(
            probable_prime(&[17], &mut |out| {
                out.fill(3);
                Ok::<_, ()>(())
            })
            .unwrap()
        );
    }
    #[test]
    fn parameter_failure_is_bounded() {
        assert_eq!(
            parameters_limit(512, 2, 1, |_| Err(())).unwrap_err(),
            Error::Randomness
        );
        assert_eq!(
            parameters_limit(512, 2, 1, |out| {
                out.fill(0);
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            parameters_limit(512, 5, 1, |out| {
                out.fill(0);
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
        assert_eq!(
            parameters_limit(511, 2, 1, |_| Ok::<_, ()>(())).unwrap_err(),
            Error::InvalidParameters
        );
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod native_tests {
    use super::*;
    use crate::rsa::Scratch;

    fn published_prime(bits: usize) -> alloc::vec::Vec<u8> {
        let text = if bits == 1024 {
            include_str!("../../vectors/cryptography-ffdh/dhkey/dhkey.txt")
        } else {
            include_str!("../../vectors/cryptography-ffdh/rfc3526/rfc3526.txt")
        };
        text.lines()
            .filter_map(|line| line.strip_prefix("P = "))
            .map(|hex| {
                let hex = hex.trim_start_matches('0');
                hex.as_bytes()
                    .as_chunks::<2>()
                    .0
                    .iter()
                    .map(|pair| {
                        u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap()
                    })
                    .collect::<alloc::vec::Vec<_>>()
            })
            .find(|p| p.len() * 8 == bits)
            .unwrap()
    }

    #[test]
    fn published_candidates_and_tape_consumption() {
        // Published safe primes exercise both 64- and 128-witness policies.
        // Zero, one, n-1 and n must be skipped independently for q and p.
        for (bits, generator, rounds) in [(1024, 2, 64), (3072, 5, 128)] {
            let prime = published_prime(bits);
            let len = prime.len();
            let mut tape = prime.clone();
            let mut carry = 0;
            let q: alloc::vec::Vec<u8> = prime
                .iter()
                .map(|&b| {
                    let half = (b >> 1) | carry;
                    carry = b << 7;
                    half
                })
                .collect();
            for modulus in [&q, &prime] {
                let mut upper = modulus.clone();
                *upper.last_mut().unwrap() -= 1;
                tape.extend_from_slice(&upper);
                tape.extend_from_slice(modulus);
                for value in [0, 1].into_iter().chain(core::iter::repeat_n(2, rounds)) {
                    tape.resize(tape.len() + len, 0);
                    *tape.last_mut().unwrap() = value;
                }
            }
            let used = tape.len();
            tape.extend_from_slice(&[0xff; 17]);
            let mut p = vec![0xaa; len];
            let mut scratch = Scratch::new(16 * len + 32);
            assert_eq!(
                super::super::x86_64::parameter_candidate(
                    bits,
                    generator,
                    &tape,
                    &mut p,
                    &mut scratch,
                ),
                (1, used)
            );
            assert_eq!(p, prime);
            for cut in [0, len - 1, len, used - 1] {
                assert_eq!(
                    super::super::x86_64::parameter_candidate(
                        bits,
                        generator,
                        &tape[..cut],
                        &mut p,
                        &mut scratch,
                    ),
                    (0, 0)
                );
                assert!(p.iter().all(|&b| b == 0));
            }
        }
    }

    #[test]
    fn tape_extension_preserves_candidate_and_reports_rng_failure() {
        let prime = published_prime(1024);
        let mut calls = 0;
        let params = parameters_limit(1024, 2, 1, |out| {
            calls += 1;
            if calls == 1 {
                out.fill(0);
                out[..prime.len()].copy_from_slice(&prime);
                *out.last_mut().unwrap() = 2;
            } else {
                for draw in out.chunks_exact_mut(prime.len()) {
                    draw.fill(0);
                    *draw.last_mut().unwrap() = 2;
                }
            }
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(params.components().0, prime);
        assert!(calls > 2);
        let mut calls = 0;
        assert_eq!(
            parameters_limit(1024, 2, 1, |out| {
                calls += 1;
                if calls == 1 {
                    out[..prime.len()].copy_from_slice(&prime);
                    Ok(())
                } else {
                    Err(())
                }
            })
            .unwrap_err(),
            Error::Randomness
        );
        let mut calls = 0;
        assert_eq!(
            parameters_limit(1024, 2, 1, |out| {
                calls += 1;
                out.fill(0);
                if calls == 1 {
                    out[..prime.len()].copy_from_slice(&prime);
                }
                Ok::<_, ()>(())
            })
            .unwrap_err(),
            Error::TooManyIterations
        );
    }

    #[test]
    fn composite_q_at_modulus_width_boundaries() {
        // Construct p with q=(p-1)/2 divisible by seven, while p passes
        // generator congruences and the small-prime sieve. In particular,
        // 513-bit p has one more limb than q: loading q must clear that limb.
        for bits in [512_usize, 513, 2049, 8192] {
            let len = bits.div_ceil(8);
            let mut candidate = vec![0; len];
            candidate[0] = 1 << ((bits - 1) % 8);
            let rem = |p: &[u8], d: u32| p.iter().fold(0, |r, &b| (256 * r + u32::from(b)) % d);
            let small_primes: alloc::vec::Vec<u32> = (3..=251)
                .step_by(2)
                .filter(|&d| (3..d).step_by(2).all(|s| d % s != 0))
                .collect();
            let offset = (1u32..65536)
                .step_by(2)
                .find(|&offset| {
                    candidate[len - 2..].copy_from_slice(&(offset as u16).to_be_bytes());
                    rem(&candidate, 24) == 11
                        && rem(&candidate, 14) == 1
                        && small_primes.iter().all(|&d| rem(&candidate, d) != 0)
                })
                .unwrap();
            candidate[len - 2..].copy_from_slice(&(offset as u16).to_be_bytes());
            let mut p = vec![0xaa; len];
            let mut scratch = Scratch::new(16 * len + 32);
            assert_eq!(
                super::super::x86_64::parameter_candidate(
                    bits,
                    2,
                    &candidate,
                    &mut p,
                    &mut scratch,
                ),
                (2, len)
            );
            assert!(p.iter().all(|&b| b == 0));
        }
    }
}
