//! The generation's outer loop, BoringSSL's `RSA_generate_key_ex`
//! (`VG.Spec.RsaKeyGen.generate`), around the verified prime search and key
//! derivation, on the targets that have no verified `vg_rsa_generate` yet.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64",
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

use alloc::vec;
use alloc::vec::Vec;

use super::Error;
use crate::arch::rsa_keygen::vg_rsa_keygen_key;
#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
use crate::arch::rsa_keygen::vg_rsa_prime_search_umaal;
use crate::arch::rsa_keygen::{vg_rsa_prime_search, vg_rsa_prime_search_init};
use crate::cpu::detected;
use crate::rsa::{Backend, PrivateKey};

/// A random stream shared by successive candidates and primes. Only an
/// unfinished candidate is replayed when more witnesses are needed.
struct Random<F> {
    octets: Vec<u8>,
    read: usize,
    fill: F,
}

impl<F: FnMut(&mut [u8]) -> Result<(), Error>> Random<F> {
    fn new(fill: F) -> Self {
        Self {
            octets: Vec::new(),
            read: 0,
            fill,
        }
    }

    /// The verified search over the stream, refilled to the length it asks
    /// for.
    fn prime(
        &mut self,
        len: usize,
        limit: usize,
        e: &[u8],
        other: Option<&[u8]>,
    ) -> Result<Vec<u8>, Error> {
        let mut search = Search::new(len, limit, e, other);
        loop {
            let (status, used) = search.run(&self.octets[self.read..]);
            self.read += used;
            match status {
                1 => return Ok(search.prime()),
                0 => self.refill(search.requested())?,
                _ => return Err(Error::TooManyIterations),
            }
        }
    }

    /// The unread octets, then fresh ones, `size` in all (more than are
    /// unread).
    fn refill(&mut self, size: usize) -> Result<(), Error> {
        let remaining = self.octets.len() - self.read;
        let mut grown = vec![0; size];
        grown[..remaining].copy_from_slice(&self.octets[self.read..]);
        // Wipe the old allocation before replacing it.
        crate::zeroize::zeroize(&mut self.octets);
        self.octets = grown;
        self.read = 0;
        (self.fill)(&mut self.octets[remaining..])
    }
}

impl<F> Drop for Random<F> {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.octets);
    }
}

/// The verified prime search's buffers and state, for one prime.
struct Search<'a> {
    e: &'a [u8],
    other: &'a [u8],
    out: Vec<u8>,
    scratch: Vec<u64>,
    state: [u64; 4],
}

impl<'a> Search<'a> {
    /// The search for a prime of `len` octets (a multiple of 8 from 32 to
    /// 512) with the exponent `e` (1 to 8 bytes), not too close to `other`
    /// (`len` octets) if given, which allows `limit` rejected candidates
    /// (`VG.Spec.RsaKeyGen.primeLimit`: `8 · 8 len` for `e = 3`, `5 · 8 len`
    /// otherwise).
    fn new(len: usize, limit: usize, e: &'a [u8], other: Option<&'a [u8]>) -> Self {
        assert!(other.is_none_or(|p| p.len() == len));
        let mut state = [0u64; 4];
        // SAFETY: `state` is valid for writes and `e` for reads of its length.
        let ok = unsafe { vg_rsa_prime_search_init(&mut state, len, e.as_ptr(), e.len()) };
        // The search accepts the lengths, with the same limit.
        assert_eq!((ok, state[0]), (1, limit as u64));
        Self {
            e,
            other: other.unwrap_or(&[]),
            out: vec![0; len],
            scratch: vec![0; crate::rsa::scratch_words(len)],
            state,
        }
    }

    /// The next tape's length, after the search returned 0.
    fn requested(&self) -> usize {
        self.state[3] as usize
    }

    /// The search over `tape` (at most `state[2]` octets): 1 if it
    /// accepted a prime, 0 if the tape ran out inside a candidate, 3 if it
    /// is exhausted; and the octets it consumed, at most `tape.len()`.
    fn run(&mut self, tape: &[u8]) -> (u32, usize) {
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_prime_search,
            // `select` chose it because the CPU has the features it needs.
            #[cfg(all(
                target_arch = "arm",
                any(
                    target_os = "linux",
                    target_os = "android",
                    target_os = "freebsd",
                    target_os = "netbsd",
                    target_os = "openbsd"
                )
            ))]
            Backend::Umaal => vg_rsa_prime_search_umaal,
        };
        let mut used = [0u64; 1];
        // SAFETY: each pointer is valid for its length (`out`, `used`,
        // `scratch` and `state` for writes), and none overlaps another or
        // wraps around, as they are distinct Rust allocations;
        // `vg_rsa_prime_search_init` accepted `out_len` and `e_len`, and
        // `p_len` is 0 or `out_len` (`Search::new`); `state` is from
        // `vg_rsa_prime_search_init` or from the last call, which returned
        // 0; `rand_len` is at most the budget, `state[2]`; `scratch_len` is
        // `16 out_len + 32`; and the CPU has the features of the function
        // `select` chose.
        let status = unsafe {
            f(
                self.out.as_mut_ptr(),
                self.out.len(),
                &mut used,
                self.e.as_ptr(),
                self.e.len(),
                self.other.as_ptr(),
                self.other.len(),
                tape.as_ptr(),
                tape.len(),
                self.scratch.as_mut_ptr(),
                self.scratch.len(),
                &mut self.state,
            )
        };
        (status, used[0] as usize)
    }

    /// The prime the search accepted.
    fn prime(mut self) -> Vec<u8> {
        core::mem::take(&mut self.out)
    }
}

impl Drop for Search<'_> {
    fn drop(&mut self) {
        // The working space holds the prime.
        crate::zeroize::zeroize(&mut self.scratch);
    }
}

/// The private key with the primes `p` and `q` (big-endian, as long as each
/// other, a multiple of 8 bytes from 32 to 512) and the public exponent `e`
/// (big-endian, 1 to 8 bytes), as BoringSSL derives it
/// (`VG.Spec.RsaKeyGen.keyFromPrimes`): `p` the larger of the two,
/// `d = e⁻¹ mod lcm(p - 1, q - 1)`, `dP = d mod (p - 1)`,
/// `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p`, after checking that `n = p q`
/// has twice the primes' bits, and the key as BoringSSL's `RSA_check_key`
/// does; `None` if `d` has at most half the modulus' bits, for which
/// BoringSSL generates both primes again. It does not check that `p` and `q`
/// are prime.
fn key_from_primes(
    public_exponent: &[u8],
    p: &[u8],
    q: &[u8],
) -> Result<Option<PrivateKey>, Error> {
    let len = p.len();
    assert!((32..=512).contains(&len) && len.is_multiple_of(8) && q.len() == len);
    assert!((1..=8).contains(&public_exponent.len()));
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
    // and `scratch_len` is `16 n_len + 32`.
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
    // `q` as long as they are (`VG.Spec.RsaKeyGen.keyValid`), `e` valid
    // (`VG.Spec.Rsa.exponentValid`), and the key one `RSA_check_key`
    // accepts, so that this is a key `PrivateKey` holds.
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
        1 => Ok(Some(key)),
        2 => Ok(None),
        _ => Err(Error::InvalidKey),
    }
}

/// The smallest modulus [`super::generate`] makes, in bits.
const MIN_MODULUS_BITS: usize = 512;
/// The largest modulus [`super::generate`] makes, in bits.
const MAX_MODULUS_BITS: usize = 8192;

/// The modulus' size in bits for the requested `bits`
/// (`VG.Spec.RsaKeyGen.modulusBits`), and the public exponent without its
/// leading zero bytes, if it is valid (`VG.Spec.RsaKeyGen.exponentValid`).
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

/// One generation of BoringSSL's `rsa_generate_key_impl`
/// (`VG.Spec.RsaKeyGen.generateOnce`) of a modulus of `nlen` bits and the
/// valid exponent `e`, drawing `p`, then `q` from the same source, and
/// deriving the key from them, drawing both primes again
/// while `d` is too small.
fn generate_once(
    e: &[u8],
    prime: &mut impl FnMut(Option<&[u8]>) -> Result<Vec<u8>, Error>,
) -> Result<PrivateKey, Error> {
    loop {
        let mut p = prime(None)?;
        let q = prime(Some(&p));
        let r = q.and_then(|mut q| {
            let key = key_from_primes(e, &p, &q);
            crate::zeroize::zeroize(&mut q);
            key
        });
        crate::zeroize::zeroize(&mut p);
        // `None`: `d ≤ 2^(nlen / 2)`, both primes again.
        if let Some(key) = r? {
            return Ok(key);
        }
    }
}

/// [`super::generate`], with its random octets drawn from `random`.
pub(super) fn generate_from(
    bits: usize,
    public_exponent: &[u8],
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<PrivateKey, Error> {
    let (nlen, e) = params(bits, public_exponent)?;
    let len = nlen / 16;
    let limit = if e == [3] { 8 * nlen / 2 } else { 5 * nlen / 2 };
    let mut random = Random::new(random);
    generate_with(e, &mut |other| random.prime(len, limit, e, other))
}

fn generate_with(
    e: &[u8],
    prime: &mut impl FnMut(Option<&[u8]>) -> Result<Vec<u8>, Error>,
) -> Result<PrivateKey, Error> {
    for _ in 0..4 {
        match generate_once(e, prime) {
            Err(Error::TooManyIterations) => {}
            r => return r,
        }
    }
    Err(Error::TooManyIterations)
}

#[cfg(test)]
pub(super) mod tests {
    use super::super::fill_random;
    use super::super::tests::{SMALL_D_P, SMALL_D_Q, reloads};
    use super::{Error, PrivateKey, Random, Vec, generate_with, key_from_primes, vec};
    use crate::rsa::BigUint;

    /// The source of a [`Random`] in [`stream`].
    type Fill<'a> = &'a mut dyn FnMut(&mut [u8]) -> Result<(), Error>;

    /// `run` over a [`Random`] that reads `rand` as one stream, and the
    /// octets it read; [`Error::Randomness`] if it needed more than `rand`.
    /// A refill past its end is padded with zeros, and its result discarded
    /// if the search read them.
    fn stream<T>(
        rand: &[u8],
        run: impl FnOnce(&mut Random<Fill<'_>>) -> Result<T, Error>,
    ) -> (Result<T, Error>, usize) {
        let mut filled = 0;
        let mut fill = |out: &mut [u8]| {
            if filled >= rand.len() {
                return Err(Error::Randomness);
            }
            for b in out {
                *b = rand.get(filled).copied().unwrap_or(0);
                filled += 1;
            }
            Ok(())
        };
        let mut random = Random::new(&mut fill as Fill<'_>);
        let r = run(&mut random);
        let unread = random.octets.len() - random.read;
        drop(random);
        let read = filled - unread;
        (
            if read > rand.len() {
                Err(Error::Randomness)
            } else {
                r
            },
            read,
        )
    }

    /// A prime of 256 bits for `e` from `rand`, as [`stream`] reads it.
    fn prime_from(
        limit: usize,
        e: &[u8],
        other: Option<&[u8]>,
        rand: &[u8],
    ) -> Result<Vec<u8>, Error> {
        stream(rand, |random| random.prime(32, limit, e, other)).0
    }

    /// A key of 512 bits for `e` from `rand`, as [`stream`] reads it, and the
    /// octets read.
    pub(in crate::rsa::keygen) fn generate_from(
        e: &[u8],
        rand: &[u8],
    ) -> (Result<PrivateKey, Error>, usize) {
        let limit = if e == [3] { 8 * 256 } else { 5 * 256 };
        stream(rand, |random| {
            generate_with(e, &mut |other| random.prime(32, limit, e, other))
        })
    }

    /// A prime of `bits` bits for `e`, from the operating system's random
    /// octets.
    fn prime(bits: usize, e: &[u8], other: Option<&[u8]>) -> Vec<u8> {
        Random::new(fill_random)
            .prime(bits / 8, 5 * bits, e, other)
            .unwrap()
    }

    /// Candidates from zeros: `2^255 + 2^254 + 1`, which is 1 modulo 3, so
    /// that it is rejected for `e = 3` (by trial division or the gcd).
    #[test]
    fn too_many_iterations() {
        let zeros = vec![0u8; 32 * 8 * 256];
        let from = |e: &[u8], limit, rand: &[u8]| prime_from(limit, e, None, rand);
        assert_eq!(from(&[3], 8 * 256, &zeros), Err(Error::TooManyIterations));
        // `e = 15` rejects them too, but allows only `5 bits` rejections.
        assert_eq!(
            from(&[15], 5 * 256, &zeros[..32 * 5 * 256]),
            Err(Error::TooManyIterations)
        );
        // One fewer is not enough.
        assert_eq!(
            from(&[3], 8 * 256, &zeros[..32 * (8 * 256 - 1)]),
            Err(Error::Randomness)
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
            prime_from(8 * 256, &[3], Some(&other), &zeros),
            Err(Error::Randomness)
        );
    }

    #[test]
    fn primes() {
        for bits in [256, 512, 1024] {
            for other in [None, Some(&[0x80u8; 128][..bits / 8])] {
                let p = prime(bits, &[1, 0, 1], other);
                assert_eq!(p.len(), bits / 8);
                assert_eq!(p[0] >> 6, 3);
                assert_eq!(p[p.len() - 1] & 1, 1);
            }
        }
    }

    /// With `p = q`, `lcm(p - 1, q - 1) = p - 1`, so that `d < p`: too small,
    /// if `e` has an inverse (`p - 1` not a multiple of 3, for `e = 3`); or
    /// no key, if it has none (`p - 1` a multiple of 3).
    #[test]
    fn key_refused() {
        let mut p = [0u8; 32];
        p[0] = 0xc0;
        p[31] = 3;
        assert!(
            key_from_primes(&[1, 0, 1], &SMALL_D_P, &SMALL_D_Q)
                .unwrap()
                .is_none()
        );
        assert!(key_from_primes(&[3], &p, &p).unwrap().is_none());
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
            let p = prime(bits, &[1, 0, 1], None);
            let q = prime(bits, &[1, 0, 1], Some(&p));
            let key = key_from_primes(&[1, 0, 1], &p, &q).unwrap().unwrap();
            assert!(reloads(&key));
            assert_eq!(key.modulus_len(), bits / 4);
            let (hi, lo) = if p > q { (&p, &q) } else { (&q, &p) };
            let [_, e, _, kp, kq, ..] = key.components().map(BigUint::as_be_bytes);
            assert_eq!((e, kp, kq), (&[1, 0, 1][..], &hi[..], &lo[..]));
        }
    }

    /// Refills preserve rejection counts, and a candidate too close to the
    /// other prime is never counted as rejected.
    #[test]
    fn refilled_errors() {
        let mut random = Random::new(|out: &mut [u8]| {
            out.fill(0xff); // Every candidate is divisible by 3.
            Ok(())
        });
        assert_eq!(
            random.prime(32, 5 * 256, &[1, 0, 1], None),
            Err(Error::TooManyIterations)
        );
        let mut fills = 0;
        let mut random = Random::new(|out: &mut [u8]| {
            fills += 1;
            if fills == 3 {
                return Err(Error::Randomness);
            }
            out.fill(0xff);
            Ok(())
        });
        // Equal to the other prime: too close, never counted as rejected.
        assert_eq!(
            random.prime(32, 5 * 256, &[1, 0, 1], Some(&[0xff; 32])),
            Err(Error::Randomness)
        );
    }
}
