//! The RSA private key and its loading, which checks it as BoringSSL's
//! `RSA_check_key` does.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use super::{BigUint, Error, MAX_MODULUS_LEN, MIN_MODULUS_LEN, exponent, scratch_words, trim};
use crate::arch::rsa::{vg_rsa_check_key, vg_rsa_crt_values, vg_rsa_recover_primes_det};

/// `x` (big-endian) in `len` bytes, if it fits.
fn widen(x: &[u8], len: usize) -> Option<Vec<u8>> {
    let x = trim(x);
    (x.len() <= len).then(|| {
        let mut v = vec![0; len];
        v[len - x.len()..].copy_from_slice(x);
        v
    })
}

/// Whether SP 800-56B Rev. 2 Appendix C.2's method
/// (`vg_rsa_recover_primes_det`) finds the primes of `(n, e, d)`, which it
/// writes to `p` and `q`, through `scratch`.
///
/// # Safety
///
/// `64 ≤ n.len() ≤ 1024`, `1 ≤ e.len() ≤ 5`, `1 ≤ d.len() ≤ n.len()`,
/// `p.len() = q.len() = n.len()` and `scratch.len() = scratch_words(n.len())`.
unsafe fn recover(
    p: &mut [u8],
    q: &mut [u8],
    n: &[u8],
    e: &[u8],
    d: &[u8],
    scratch: &mut [u64],
) -> bool {
    // SAFETY: each pointer is valid for its length (`p`, `q` and `scratch`
    // for writes), and none overlaps another or wraps around, as they are
    // distinct Rust slices; the caller gives the lengths, and the function
    // needs no CPU feature.
    let r = unsafe {
        vg_rsa_recover_primes_det(
            p.as_mut_ptr(),
            p.len(),
            q.as_mut_ptr(),
            q.len(),
            n.as_ptr(),
            n.len(),
            e.as_ptr(),
            e.len(),
            d.as_ptr(),
            d.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    r == 1
}

/// An RSA private key in the Chinese remainder form `(p, q, dP, dQ, qInv)`
/// of RFC 8017 §3.2, with its public key `(n, e)` and its private exponent
/// `d`, which passes BoringSSL's `RSA_check_key` (see the
/// [module](super) documentation). Its private values are wiped when it is
/// dropped.
pub struct PrivateKey {
    pub(crate) n: Vec<u8>,
    pub(crate) e: Vec<u8>,
    pub(crate) d: Vec<u8>,
    pub(crate) p: Vec<u8>,
    pub(crate) q: Vec<u8>,
    pub(crate) dp: Vec<u8>,
    pub(crate) dq: Vec<u8>,
    pub(crate) qinv: Vec<u8>,
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl Drop for PrivateKey {
    fn drop(&mut self) {
        for x in [
            &mut self.d,
            &mut self.p,
            &mut self.q,
            &mut self.dp,
            &mut self.dq,
            &mut self.qinv,
        ] {
            crate::zeroize::zeroize(x);
        }
    }
}

impl PrivateKey {
    /// The key with the modulus `n`, the public exponent `e`, the private
    /// exponent `d` and the values `p`, `q`, `dP`, `dQ` and `qInv`, each with
    /// any number of leading zero bytes but `n`. `n` must be odd, from 512 to
    /// 8192 bits long, with no leading zero byte; `e` must be odd, from 3 to
    /// `2^33 - 1`, as BoringSSL requires; without their leading zero bytes,
    /// `d` must not be zero or have more bytes than `n`, `p` and `q` must have
    /// fewer bytes than `n`, and `dP` and `qInv` no more bytes than `p` and
    /// `dQ` no more than `q`. The
    /// values must pass the checks of BoringSSL's
    /// `RSA_check_key`, the verified `vg_rsa_check_key`: `d < n`, `p q = n`,
    /// `d e ≡ 1` modulo `p - 1` and `q - 1`, `dP < p - 1`,
    /// `e dP ≡ 1 (mod p - 1)`, `dQ < q - 1`, `e dQ ≡ 1 (mod q - 1)`,
    /// `qInv < p` and `q qInv ≡ 1 (mod p)`.
    ///
    /// Like `RSA_check_key`, nothing checks that `p` and `q` are prime: with
    /// a factor that is not, the private-key operations' results fail their
    /// check against `e` and are never released.
    #[allow(clippy::too_many_arguments)]
    pub fn from_crt(
        n: BigUint<'_>,
        e: BigUint<'_>,
        d: BigUint<'_>,
        p: BigUint<'_>,
        q: BigUint<'_>,
        dp: BigUint<'_>,
        dq: BigUint<'_>,
        qinv: BigUint<'_>,
    ) -> Result<Self, Error> {
        let b = BigUint::as_be_bytes;
        Self::from_crt_bytes(b(n), b(e), b(d), b(p), b(q), b(dp), b(dq), b(qinv))
    }

    /// The key with the modulus `n`, the public exponent `e`, the private
    /// exponent `d` and the primes `p` and `q`, each with any number of
    /// leading zero bytes but `n`, as RFC 8017 §3.2's first form with the
    /// primes: computes the CRT values `dP = d mod (p - 1)`,
    /// `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p` and loads the key as
    /// [`from_crt`](Self::from_crt) does. `n` must be odd, from 512 to 8192
    /// bits long, with no leading zero byte; `e` must be odd, from 3 to
    /// `2^33 - 1`, as BoringSSL requires; `d` must not be zero, and `p` and `q` must have fewer bytes
    /// than `n`; `p q = n`, `d < n`, `q` must have an inverse modulo `p`, and `d e ≡ 1`
    /// modulo `p - 1` and `q - 1`. Nothing checks that `p` and `q` are prime
    /// (see [`from_crt`](Self::from_crt)).
    pub fn from_primes(
        n: BigUint<'_>,
        e: BigUint<'_>,
        d: BigUint<'_>,
        p: BigUint<'_>,
        q: BigUint<'_>,
    ) -> Result<Self, Error> {
        let b = BigUint::as_be_bytes;
        Self::from_primes_bytes(b(n), b(e), b(d), b(p), b(q))
    }

    /// The key with the modulus `n`, the public exponent `e` and the private
    /// exponent `d`, RFC 8017 §3.2's first form: recovers the primes `p > q`
    /// of `n` and loads the key as [`from_primes`](Self::from_primes) does.
    /// `n` must be odd, from 512 to 8192 bits long, with no leading zero
    /// byte, `e` odd, from 3 to `2^33 - 1`, and `d` not zero and less than
    /// `n`.
    ///
    /// It recovers the primes by SP 800-56B Rev. 2 Appendix C.2's
    /// deterministic method, and refuses a key it does not factor. Its step 1
    /// makes `a = K φ(n)`, with `K ≤ k²` for `k = (d e - 1) / λ(n)` (so
    /// `K < e²` for the least private exponent), and the method finds the
    /// primes whenever `K (p + q - 1) ≤ n`: it refuses only keys with a tiny
    /// prime factor (a few dozen bits at most) and those that are not valid
    /// two-prime keys. (Every valid `d < n` of Wycheproof's two-prime keys
    /// factors, as do `e = 3` and `e = 2^33 - 1`, and primes as unbalanced as
    /// 24 bits.)
    pub fn from_components(n: BigUint<'_>, e: BigUint<'_>, d: BigUint<'_>) -> Result<Self, Error> {
        Self::from_components_bytes(n.as_be_bytes(), e.as_be_bytes(), d.as_be_bytes())
    }

    /// [`from_crt`](Self::from_crt) of the values' big-endian bytes (with any
    /// number of leading zero bytes but `n`).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_crt_bytes(
        n: &[u8],
        e: &[u8],
        d: &[u8],
        p: &[u8],
        q: &[u8],
        dp: &[u8],
        dq: &[u8],
        qinv: &[u8],
    ) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        let e = exponent(e)?;
        let (d, p, q) = (trim(d), trim(p), trim(q));
        if d.is_empty()
            || d.len() > k
            || p.is_empty()
            || p.len() >= k
            || q.is_empty()
            || q.len() >= k
        {
            return Err(Error::InvalidPrivateKey);
        }
        let (Some(dp), Some(dq), Some(qinv)) =
            (widen(dp, p.len()), widen(dq, q.len()), widen(qinv, p.len()))
        else {
            return Err(Error::InvalidPrivateKey);
        };
        let key = PrivateKey {
            n: n.to_vec(),
            e: e.to_vec(),
            d: d.to_vec(),
            p: p.to_vec(),
            q: q.to_vec(),
            dp,
            dq,
            qinv,
        };
        if key.valid() {
            Ok(key)
        } else {
            Err(Error::InvalidPrivateKey)
        }
    }

    /// Whether BoringSSL's `RSA_check_key` accepts the key, by the verified
    /// `vg_rsa_check_key` (`VG.Spec.Rsa.checkKey`), which implies what the
    /// private-key operations check of the key (a valid modulus, `p q = n`
    /// and `qInv < p`), so that they refuse only an input not below the
    /// modulus.
    fn valid(&self) -> bool {
        let k = self.n.len();
        let mut scratch = vec![0u64; scratch_words(k)];
        // SAFETY: each pointer is valid for its length (`scratch` for
        // writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; `from_crt`'s checks give
        // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ d_len ≤ n_len`,
        // `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
        // `dp_len = qinv_len = p_len`, `dq_len = q_len`, and
        // `scratch_len = 16 n_len + 32`.
        let r = unsafe {
            vg_rsa_check_key(
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                self.d.as_ptr(),
                self.d.len(),
                self.p.as_ptr(),
                self.p.len(),
                self.q.as_ptr(),
                self.q.len(),
                self.dp.as_ptr(),
                self.dp.len(),
                self.dq.as_ptr(),
                self.dq.len(),
                self.qinv.as_ptr(),
                self.qinv.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds the private key.
        crate::zeroize::zeroize(&mut scratch);
        r == 1
    }

    /// [`from_primes`](Self::from_primes) of the values' big-endian bytes
    /// (with any number of leading zero bytes but `n`).
    pub(crate) fn from_primes_bytes(
        n: &[u8],
        e: &[u8],
        d: &[u8],
        p: &[u8],
        q: &[u8],
    ) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        let e = exponent(e)?;
        let (d, p, q) = (trim(d), trim(p), trim(q));
        if d.is_empty()
            || d.len() > k
            || p.is_empty()
            || p.len() >= k
            || q.is_empty()
            || q.len() >= k
        {
            return Err(Error::InvalidPrivateKey);
        }
        let (mut dp, mut dq, mut qinv) = (vec![0; p.len()], vec![0; q.len()], vec![0; p.len()]);
        let mut scratch = vec![0u64; scratch_words(k)];
        // SAFETY: each pointer is valid for its length (`dp`, `dq`, `qinv`
        // and `scratch` for writes), and none overlaps another or wraps
        // around, as they are distinct Rust allocations; the checks above
        // give `64 ≤ n_len ≤ 1024`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`
        // and `1 ≤ d_len ≤ n_len`, and `dp_len = qinv_len = p_len`,
        // `dq_len = q_len` and `scratch_len = 16 n_len + 32`.
        let r = unsafe {
            vg_rsa_crt_values(
                dp.as_mut_ptr(),
                dp.len(),
                dq.as_mut_ptr(),
                dq.len(),
                qinv.as_mut_ptr(),
                qinv.len(),
                n.as_ptr(),
                k,
                p.as_ptr(),
                p.len(),
                q.as_ptr(),
                q.len(),
                d.as_ptr(),
                d.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds the private key.
        crate::zeroize::zeroize(&mut scratch);
        let key = if r == 1 {
            PrivateKey::from_crt_bytes(n, e, d, p, q, &dp, &dq, &qinv)
        } else {
            Err(Error::InvalidPrivateKey)
        };
        for x in [&mut dp, &mut dq, &mut qinv] {
            crate::zeroize::zeroize(x);
        }
        key
    }

    /// [`from_components`](Self::from_components) of the values' big-endian
    /// bytes (with any number of leading zero bytes but `n`).
    pub(crate) fn from_components_bytes(n: &[u8], e: &[u8], d: &[u8]) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        let (e, d) = (exponent(e)?, trim(d));
        if d.is_empty() || d.len() > k {
            return Err(Error::InvalidPrivateKey);
        }
        let (mut p, mut q) = (vec![0; k], vec![0; k]);
        let mut scratch = vec![0u64; scratch_words(k)];
        // SAFETY: the checks above give `64 ≤ n_len ≤ 1024`,
        // `1 ≤ e_len ≤ 5` and `1 ≤ d_len ≤ n_len`, and `p_len = q_len = n_len`
        // and `scratch_len = scratch_words(n_len)`.
        let found = unsafe { recover(&mut p, &mut q, n, e, d, &mut scratch) };
        // The working space holds the private key.
        crate::zeroize::zeroize(&mut scratch);
        let key = if found {
            PrivateKey::from_primes_bytes(n, e, d, &p, &q)
        } else {
            Err(Error::InvalidPrivateKey)
        };
        for x in [&mut p, &mut q] {
            crate::zeroize::zeroize(x);
        }
        key
    }

    /// The length of the modulus in bytes, which is that of the key's
    /// ciphertexts and signatures.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }

    /// The key's values as it holds them, `[n, e, d, p, q, dP, dQ, qInv]`
    /// (`dP` and `qInv` in as many bytes as `p`, `dQ` as `q`; `p > q` for a
    /// key loaded by [`from_components`](Self::from_components) or generated
    /// by [`keygen::generate`](super::keygen::generate)).
    pub fn components(&self) -> [BigUint<'_>; 8] {
        [
            &self.n, &self.e, &self.d, &self.p, &self.q, &self.dp, &self.dq, &self.qinv,
        ]
        .map(|x| BigUint::from_be_bytes(x))
    }
}

#[cfg(test)]
mod tests {
    use super::{BigUint, Error, PrivateKey, Vec, trim, vec};
    use crate::rsa::tests::{composite, composite_d, mul};

    /// The sizes of `composite`'s keys: 64 to 1024 bytes, with primes of
    /// whole words and not.
    const SIZES: [usize; 6] = [32, 33, 39, 43, 64, 511];

    /// `composite`'s keys load, with either prime first, of lengths that are
    /// and are not whole words.
    #[test]
    fn crt_loads() {
        for a in SIZES {
            for swap in [false, true] {
                let [n, p, q, dp, dq, qinv] = composite(a, swap);
                let k = n.len();
                assert_eq!(k, 2 * a);
                let d = composite_d(a);
                let key =
                    PrivateKey::from_crt_bytes(&n, &[3], &d, &p, &q, &dp, &dq, &qinv).unwrap();
                assert_eq!(key.modulus_len(), k);
            }
        }
        // Leading zeros on the values and on `e`.
        let [n, p, q, dp, dq, qinv] = composite(32, false);
        let z = |x: &[u8]| [&[0, 0][..], x].concat();
        let d = composite_d(32);
        assert!(
            PrivateKey::from_crt_bytes(&n, &[0, 3], &z(&d), &z(&p), &q, &z(&dp), &dq, &z(&qinv))
                .is_ok()
        );
        assert!(PrivateKey::from_crt_bytes(&n, &[3], &d, &p, &z(&q), &dp, &z(&dq), &qinv).is_ok());
    }

    #[test]
    fn private_invalid() {
        let [n, p, q, dp, dq, qi] = composite(32, false);
        let d = composite_d(32);
        let new = |n: &[u8], e: &[u8], p: &[u8], q: &[u8], dp: &[u8], dq: &[u8], qi: &[u8]| {
            PrivateKey::from_crt_bytes(n, e, &d, p, q, dp, dq, qi).map(|_| ())
        };
        assert_eq!(new(&n, &[3], &p, &q, &dp, &dq, &qi), Ok(()));
        assert_eq!(
            new(&n[1..], &[3], &p, &q, &dp, &dq, &qi),
            Err(Error::InvalidModulus)
        );
        assert_eq!(
            new(&[1; 1025], &[3], &p, &q, &dp, &dq, &qi),
            Err(Error::InvalidModulus)
        );
        for e in [&[][..], &[1], &[4], &[2, 0, 0, 0, 1]] {
            assert_eq!(
                new(&n, e, &p, &q, &dp, &dq, &qi),
                Err(Error::InvalidExponent)
            );
        }
        let bad = Err(Error::InvalidPrivateKey);
        // Lengths.
        assert_eq!(new(&n, &[3], &[0; 3], &q, &dp, &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &p, &[], &dp, &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &n, &q, &dp, &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &p, &n, &dp, &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &p, &q, &[1; 33], &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &p, &q, &dp, &[1; 34], &qi), bad);
        assert_eq!(new(&n, &[3], &p, &q, &dp, &dq, &[1; 33]), bad);
        // Each of the checks: an even `n`, `p q ≠ n`, `qInv ≥ p`, and
        // `dP = dQ = 0`.
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        assert_eq!(new(&even, &[3], &p, &q, &dp, &dq, &qi), bad);
        let mut n2 = n.clone();
        n2[10] ^= 1;
        assert_eq!(new(&n2, &[3], &p, &q, &dp, &dq, &qi), bad);
        assert_eq!(new(&n, &[3], &p, &q, &dp, &dq, &p), bad);
        assert_eq!(new(&n, &[3], &p, &q, &[0], &[0], &qi), bad);
        // A `dP`, `dQ` or `qInv` that does not match, `dP = p - 1`,
        // `dQ = (q - 1) + dQ` (`q - 1 = 2^256`), an `e` that does not match,
        // and each of them all zeros or all ones in its prime's bytes.
        let flip = |x: &[u8]| {
            let mut x = x.to_vec();
            *x.last_mut().unwrap() ^= 1;
            x
        };
        let mut pm1 = p.clone();
        pm1[31] = 0xfe;
        let mut dq2 = dq.clone();
        dq2.insert(0, 1);
        for r in [
            new(&n, &[3], &p, &q, &flip(&dp), &dq, &qi),
            new(&n, &[3], &p, &q, &dp, &flip(&dq), &qi),
            new(&n, &[3], &p, &q, &dp, &dq, &flip(&qi)),
            new(&n, &[3], &p, &q, &pm1, &dq, &qi),
            new(&n, &[3], &p, &q, &dp, &dq2, &qi),
            new(&n, &[5], &p, &q, &dp, &dq, &qi),
        ] {
            assert_eq!(r, bad);
        }
        for byte in [0, 0xff] {
            assert_eq!(new(&n, &[3], &p, &q, &[byte; 32], &dq, &qi), bad);
            assert_eq!(new(&n, &[3], &p, &q, &dp, &[byte; 33], &qi), bad);
            assert_eq!(new(&n, &[3], &p, &q, &dp, &dq, &[byte; 32]), bad);
        }
        let key = PrivateKey::from_crt_bytes(&n, &[3], &d, &p, &q, &dp, &dq, &qi).unwrap();
        assert!(!alloc::format!("{key:?}").contains('['));
    }

    /// The checks of `d`: `d e ≡ 1` modulo `p - 1` and `q - 1`, and
    /// `d < n` (`n`, all ones, is the only `d` as long as `n` but not less),
    /// before which a `d` of zero or longer than `n` is refused. `d` plus
    /// `lcm(p - 1, q - 1)` matches `e` too, and is still less than `n`.
    #[test]
    fn private_exponent() {
        for a in SIZES {
            for swap in [false, true] {
                let [n, p, q, dp, dq, qi] = composite(a, swap);
                let new = |d: &[u8]| PrivateKey::from_crt_bytes(&n, &[3], d, &p, &q, &dp, &dq, &qi);
                let d = composite_d(a);
                let bad = Err(Error::InvalidPrivateKey);
                // `lcm(p - 1, q - 1) = lcm(2^(8a) - 2, 2^(8a))
                // = (2^(8a - 1) - 1) 2^(8a)`.
                let mut lcm = vec![0xff; a];
                lcm[0] = 0x7f;
                lcm.extend(vec![0; a]);
                let plus = |x: &[u8], y: &[u8]| {
                    let len = x.len().max(y.len()) + 1;
                    let mut r = vec![0u8; len];
                    let mut carry = 0u16;
                    for i in 0..len {
                        let at =
                            |v: &[u8]| u16::from(v.len().checked_sub(i + 1).map_or(0, |j| v[j]));
                        let s = at(x) + at(y) + carry;
                        r[len - 1 - i] = s as u8;
                        carry = s >> 8;
                    }
                    r
                };
                assert!(new(&d).is_ok());
                assert!(new(&plus(&d, &lcm)).is_ok());
                for d in [
                    vec![7],
                    vec![],
                    vec![0, 0],
                    vec![1; 2 * a + 1],
                    n.clone(),
                    plus(&d, &n),
                ] {
                    assert_eq!(new(&d).map(|_| ()), bad);
                }
            }
        }
    }

    /// `composite`'s keys from `(n, e, d, p, q)`: they have its CRT values.
    /// With `d = 1`, `d e` matches neither prime.
    #[test]
    fn from_primes() {
        for a in SIZES {
            for swap in [false, true] {
                let [n, p, q, dp, dq, qi] = composite(a, swap);
                let d = composite_d(a);
                let key =
                    PrivateKey::from_primes_bytes(&n, &[0, 3], &d, &[&[0][..], &p].concat(), &q)
                        .unwrap();
                let crt: Vec<Vec<u8>> = key.components().map(BigUint::as_be_bytes)[5..]
                    .iter()
                    .map(|x| trim(x).to_vec())
                    .collect();
                assert_eq!(crt, [&dp, &dq, &qi].map(|x| trim(x).to_vec()));
                // `d = 1`: refused, as loading checks `dP` and `dQ`; and `d = n`.
                assert!(PrivateKey::from_primes_bytes(&n, &[3], &[1], &p, &q).is_err());
                assert!(PrivateKey::from_primes_bytes(&n, &[3], &n, &p, &q).is_err());
            }
        }
        let [n, p, q, ..] = composite(32, false);
        let new = |n: &[u8], e: &[u8], d: &[u8], p: &[u8], q: &[u8]| {
            PrivateKey::from_primes_bytes(n, e, d, p, q).map(|_| ())
        };
        assert_eq!(new(&n[1..], &[3], &[1], &p, &q), Err(Error::InvalidModulus));
        assert_eq!(
            new(&[1; 1025], &[3], &[1], &p, &q),
            Err(Error::InvalidModulus)
        );
        assert_eq!(new(&n, &[0], &[1], &p, &q), Err(Error::InvalidExponent));
        assert_eq!(new(&n, &[1; 65], &[1], &p, &q), Err(Error::InvalidExponent));
        let bad = Err(Error::InvalidPrivateKey);
        assert_eq!(new(&n, &[3], &[0, 0], &p, &q), bad);
        assert_eq!(new(&n, &[3], &[1; 65], &p, &q), bad);
        assert_eq!(new(&n, &[3], &[1], &[0; 3], &q), bad);
        // `p = 1`.
        assert_eq!(new(&n, &[3], &[1], &[0, 1], &q), bad);
        assert_eq!(new(&n, &[3], &[1], &n, &q), bad);
        assert_eq!(new(&n, &[3], &[1], &p, &[]), bad);
        assert_eq!(new(&n, &[3], &[1], &p, &n), bad);
        // `p q ≠ n`, and `q` with no inverse modulo `p`: `p = 2^288 - 1` and
        // `q = 2^256 - 3` (`gcd = 13`).
        let mut n2 = n.clone();
        n2[10] ^= 1;
        assert_eq!(new(&n2, &[3], &[1], &p, &q), bad);
        let p3 = vec![0xff; 36];
        let mut q3 = vec![0xff; 32];
        q3[31] = 0xfd;
        assert_eq!(new(&mul(&p3, &q3), &[3], &[1], &p3, &q3), bad);
    }

    #[test]
    fn components_round_trip() {
        let [n, p, q, dp, dq, qi] = composite(32, false);
        let d = composite_d(32);
        let z = |x: &[u8]| [&[0][..], x].concat();
        let key =
            PrivateKey::from_crt_bytes(&n, &[0, 3], &z(&d), &z(&p), &q, &dp, &dq, &qi).unwrap();
        let c = key.components().map(BigUint::as_be_bytes);
        // `dQ` in `q`'s 33 bytes.
        assert_eq!(
            c,
            [
                &n[..],
                &[3],
                &d,
                &p,
                &q,
                &dp,
                &[&[0][..], &dq].concat(),
                &qi
            ]
        );
        let again =
            PrivateKey::from_crt_bytes(c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]).unwrap();
        assert_eq!(again.components().map(BigUint::as_be_bytes), c);
    }

    #[test]
    fn private_from_components_invalid() {
        let [n, ..] = composite(32, false);
        let new =
            |n: &[u8], e: &[u8], d: &[u8]| PrivateKey::from_components_bytes(n, e, d).map(|_| ());
        assert_eq!(new(&n[1..], &[3], &[1]), Err(Error::InvalidModulus));
        assert_eq!(new(&[1; 1025], &[3], &[1]), Err(Error::InvalidModulus));
        assert_eq!(new(&n, &[0, 0], &[1]), Err(Error::InvalidExponent));
        assert_eq!(new(&n, &[1; 65], &[1]), Err(Error::InvalidExponent));
        let bad = Err(Error::InvalidPrivateKey);
        assert_eq!(new(&n, &[3], &[]), bad);
        assert_eq!(new(&n, &[3], &[1; 65]), bad);
        // `d e - 1 = 2`: no candidate finds a factor.
        assert_eq!(new(&n, &[3], &[1]), bad);
        // `d e` even: step 1 fails. An even modulus.
        assert_eq!(new(&n, &[3], &[2]), bad);
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        assert_eq!(new(&even, &[3], &[1]), bad);
    }
}
