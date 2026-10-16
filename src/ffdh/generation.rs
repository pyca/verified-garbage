//! OS randomness, rejection sampling and probable safe-prime generation.
use super::arithmetic::{Montgomery, bits, canonical, minus_one, value_cmp};
use super::{Error, MAX_BITS, MIN_BITS, Parameters};
use crate::zeroize::zeroize;
use alloc::{vec, vec::Vec};

/// Independent uniform integer in [1,upper-1]. The top-bit mask and byte
/// width are public. Only acceptance/rejection controls a branch. The
/// accepted scalar's leading-zero count is never inspected.
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
fn rem_small(n: &[u8], divisor: u32) -> u32 {
    n.iter().fold(0, |r, &b| (256 * r + u32::from(b)) % divisor)
}
fn trial_composite(p: &[u8]) -> bool {
    (3..=251)
        .step_by(2)
        .filter(|&d| (3..d).step_by(2).all(|s| d % s != 0))
        .any(|d| rem_small(p, d) == 0 && value_cmp(p, &d.to_be_bytes()).is_ne())
}
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
pub(super) fn probable_prime<E>(
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
