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
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa_keygen::vg_rsa_keygen_key;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_keygen::vg_rsa_prime_search_adx;
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
    /// The random octets given to `generate_from` ran out before a key was
    /// generated.
    NotEnoughRandomness,
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
            Error::NotEnoughRandomness => "not enough random octets for an RSA key",
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

    /// The most octets a tape may have (only `prime_from` reads it).
    #[cfg(any(test, feature = "internal-bench"))]
    fn budget(&self) -> usize {
        self.state[2] as usize
    }

    /// The next tape's length, after the search returned 0.
    fn requested(&self) -> usize {
        self.state[3] as usize
    }

    /// The search over `tape` (at most [`Search::budget`] octets): 1 if it
    /// accepted a prime, 0 if the tape ran out inside a candidate, 3 if it
    /// is exhausted; and the octets it consumed, at most `tape.len()`.
    fn run(&mut self, tape: &[u8]) -> (u32, usize) {
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_prime_search,
            // `select` chose it because the CPU has the features it needs.
            #[cfg(target_arch = "x86_64")]
            Backend::Adx | Backend::Ifma => vg_rsa_prime_search_adx,
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

/// A prime of `len` octets, with the limit of rejected candidates `limit`
/// (as [`Search::new`] takes them), from the random octets `rand`, read as
/// one stream (`VG.Spec.RsaKeyGen.generatePrime`), and the number of octets
/// read, also when it fails; [`Error::NotEnoughRandomness`] if they run out
/// first.
#[cfg(any(test, feature = "internal-bench"))]
fn prime_from(
    len: usize,
    limit: usize,
    public_exponent: &[u8],
    other: Option<&[u8]>,
    rand: &[u8],
) -> (Result<Vec<u8>, Error>, usize) {
    let mut search = Search::new(len, limit, public_exponent, other);
    let mut read = 0;
    loop {
        // The stream cut into tapes of the budget, which no request exceeds.
        let end = rand.len().min(read + search.budget());
        let (status, used) = search.run(&rand[read..end]);
        read += used;
        match status {
            1 => return (Ok(search.prime()), read),
            0 if end < rand.len() => {}
            0 => return (Err(Error::NotEnoughRandomness), read),
            _ => return (Err(Error::TooManyIterations), read),
        }
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

/// The smallest modulus [`generate`] makes, in bits.
const MIN_MODULUS_BITS: usize = 512;
/// The largest modulus [`generate`] makes, in bits.
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

/// A two-prime RSA private key with a modulus of `bits` bits, rounded down
/// to a multiple of 128 (from 512 to 8192 bits), and the public exponent
/// `e` (big-endian, odd, from 3 to `2^32 - 1`, with any number of leading
/// zero bytes), from the operating system's random number generator, as
/// BoringSSL's `RSA_generate_key_ex` makes it (`VG.Spec.RsaKeyGen.generate`).
pub fn generate(bits: usize, public_exponent: &[u8]) -> Result<PrivateKey, Error> {
    let (nlen, e) = params(bits, public_exponent)?;
    let len = nlen / 16;
    let limit = if e == [3] { 8 * nlen / 2 } else { 5 * nlen / 2 };
    let mut random = Random::new(fill_random);
    generate_with(e, &mut |other| random.prime(len, limit, e, other))
}

/// [`generate`]'s key from the random octets `rand`, read as one stream
/// (`VG.Spec.RsaKeyGen.generate`), and the number of octets read;
/// [`Error::NotEnoughRandomness`] if they run out first. A generation that
/// fails with too many rejected candidates starts again from where it
/// stopped reading, up to four times in all.
///
/// Not part of the API: it lets benchmarks measure [`generate`] on
/// identical work, from fixed tapes. The key is secret only if `rand` is
/// uniformly random, and never reused.
#[cfg(any(test, feature = "internal-bench"))]
#[doc(hidden)]
pub fn generate_from(
    bits: usize,
    public_exponent: &[u8],
    rand: &[u8],
) -> Result<(PrivateKey, usize), Error> {
    let (nlen, e) = params(bits, public_exponent)?;
    let len = nlen / 16;
    let limit = if e == [3] { 8 * nlen / 2 } else { 5 * nlen / 2 };
    let mut read = 0;
    let r = generate_with(e, &mut |other| {
        let (r, used) = prime_from(len, limit, e, other, &rand[read..]);
        read += used;
        r
    });
    r.map(|key| (key, read))
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
mod tests {
    use super::{
        Error, PrivateKey, Random, Vec, fill_random, generate, generate_from, generate_with,
        key_from_primes, prime_from, vec,
    };

    /// Whether `key` loads again from its CRT values: whether BoringSSL's
    /// `RSA_check_key` accepts it (`PrivateKey::from_crt`).
    pub(super) fn reloads(key: &PrivateKey) -> bool {
        let c = key.components();
        PrivateKey::from_crt(c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]).is_ok()
    }

    /// A prime of `bits` bits for `e`, from the operating system's random
    /// octets.
    fn prime(bits: usize, e: &[u8], other: Option<&[u8]>) -> Vec<u8> {
        Random::new(fill_random)
            .prime(bits / 8, 5 * bits, e, other)
            .unwrap()
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidExponent,
            Error::InvalidModulusLength,
            Error::TooManyIterations,
            Error::NotEnoughRandomness,
            Error::Randomness,
            Error::InvalidKey,
        ] {
            assert!(!alloc::format!("{e}").is_empty());
        }
    }

    /// Candidates from zeros: `2^255 + 2^254 + 1`, which is 1 modulo 3, so
    /// that it is rejected for `e = 3` (by trial division or the gcd).
    #[test]
    fn too_many_iterations() {
        let zeros = vec![0u8; 32 * 8 * 256];
        let from = |e: &[u8], limit, rand: &[u8]| prime_from(32, limit, e, None, rand).0;
        assert_eq!(from(&[3], 8 * 256, &zeros), Err(Error::TooManyIterations));
        // `e = 15` rejects them too, but allows only `5 bits` rejections.
        assert_eq!(
            from(&[15], 5 * 256, &zeros[..32 * 5 * 256]),
            Err(Error::TooManyIterations)
        );
        // One fewer is not enough.
        assert_eq!(
            from(&[3], 8 * 256, &zeros[..32 * (8 * 256 - 1)]),
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
            prime_from(32, 8 * 256, &[3], Some(&other), &zeros).0,
            Err(Error::NotEnoughRandomness)
        );
    }

    /// A stream longer than the search's entropy budget, of candidates
    /// too close to the other prime: read in tapes of the budget, to its end.
    #[test]
    fn longer_than_budget() {
        let mut other = [0u8; 32];
        other[0] = 0xc0;
        other[31] = 1;
        let zeros = vec![0u8; 32 * 32769 + 64];
        assert_eq!(
            prime_from(32, 5 * 256, &[1, 0, 1], Some(&other), &zeros),
            (Err(Error::NotEnoughRandomness), zeros.len())
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
            let [_, e, _, kp, kq, ..] = key.components();
            assert_eq!((e, kp, kq), (&[1, 0, 1][..], &hi[..], &lo[..]));
        }
    }

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
    #[test]
    fn generate_keys() {
        for (bits, e) in [(512, &[3][..]), (639, &[0, 0, 3]), (1024, &[1, 0, 1])] {
            let key = generate(bits, e).unwrap();
            assert!(reloads(&key));
            assert_eq!(key.modulus_len(), bits / 128 * 16);
            assert_eq!(key.components()[1], crate::rsa::trim(e));
        }
    }

    /// Candidates from zeros are rejected for `e = 3` (see
    /// `too_many_iterations`): each generation fails after `8 · 256`
    /// candidates for `p`, and the next one reads on from there, four in all.
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

    /// Compare the refill path with the fixed-stream API across candidate,
    /// witness and prime boundaries, including a rejected small-d key.
    #[test]
    fn refilled_generation() {
        let mut rand = vec![0xff; 32 * 3]; // Divisible by 3.
        rand.extend(candidate(&SMALL_D_P, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        rand.extend(candidate(&PRIME, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        let (expected, used) = generate_from(512, &[1, 0, 1], &rand).unwrap();
        let filled = core::cell::Cell::new(0);
        let mut random = Random::new(|out: &mut [u8]| {
            for b in out {
                *b = rand.get(filled.get()).copied().unwrap_or(0);
                filled.set(filled.get() + 1);
            }
            Ok(())
        });
        let key = generate_with(&[1, 0, 1], &mut |other| {
            random.prime(32, 5 * 256, &[1, 0, 1], other)
        })
        .unwrap();
        assert_eq!(key.components(), expected.components());
        assert_eq!(filled.get() - (random.octets.len() - random.read), used);
    }

    /// Refills preserve rejection counts and release no incomplete prime
    /// when entropy fails, including a failure after witnesses were read.
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
        let rand = candidate(&PRIME, &W);
        let mut position = 0;
        let mut random = Random::new(|out: &mut [u8]| {
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
        assert_eq!(
            generate_with(&[1, 0, 1], &mut |other| {
                random.prime(32, 5 * 256, &[1, 0, 1], other)
            })
            .unwrap_err(),
            Error::Randomness
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

    /// The primes with the small `d` are generated, refused, and replaced.
    #[test]
    fn generate_small_d() {
        let mut rand = candidate(&SMALL_D_P, &W);
        rand.extend(candidate(&SMALL_D_Q, &W));
        assert!(
            key_from_primes(&[1, 0, 1], &SMALL_D_P, &SMALL_D_Q)
                .unwrap()
                .is_none()
        );
        assert_eq!(
            generate_from(512, &[1, 0, 1], &rand).unwrap_err(),
            Error::NotEnoughRandomness
        );
        rand.extend(candidate(&PRIME, &W));
        rand.extend(candidate(&SMALL_D_Q, &W));
        let (key, read) = generate_from(512, &[1, 0, 1], &rand).unwrap();
        assert_eq!(read, rand.len());
        assert!(reloads(&key));
        let [_, _, _, p, q, ..] = key.components();
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
        let (key, read) = generate_from(512, &[1, 0, 1], &rand).unwrap();
        assert_eq!(read, rand.len());
        assert!(reloads(&key));
        assert_eq!(key.components()[4], COMPOSITE);
        assert_eq!(
            crate::rsa::pkcs1_sig::sign(&key, &[0; 32], crate::rsa::pkcs1_sig::Hash::Sha256),
            Err(crate::rsa::pkcs1_sig::Error::Fault)
        );
    }
}
