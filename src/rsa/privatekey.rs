//! The RSA private-key operation (RSADP with the CRT, checked against the
//! public exponent), the loading of a private key from its CRT values, from
//! `(n, e, d, p, q)` or from `(n, e, d)`, and the check of a key: see the
//! parent module.

#![cfg(target_arch = "x86_64")]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use super::{Backend, Error, MAX_MODULUS_LEN, MIN_MODULUS_LEN, exponent, scratch_words, trim};
use crate::arch::rsa::{
    vg_rsa_check_key, vg_rsa_crt_values, vg_rsa_private_checked, vg_rsa_private_checked_adx,
    vg_rsa_private_checked_ifma, vg_rsa_recover_primes, vg_rsa_recover_primes_adx,
};
use crate::cpu::detected;

/// `x` (big-endian) in `len` bytes, if it fits.
fn widen(x: &[u8], len: usize) -> Option<Vec<u8>> {
    let x = trim(x);
    (x.len() <= len).then(|| {
        let mut v = vec![0; len];
        v[len - x.len()..].copy_from_slice(x);
        v
    })
}

/// An RSA private key in the Chinese remainder form `(p, q, dP, dQ, qInv)`
/// of RFC 8017 §3.2, with its public key `(n, e)` and its private exponent
/// `d`. Its private values are wiped when it is dropped.
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
    /// exponent `d` and the values `p`, `q`, `dP`, `dQ` and `qInv`, all
    /// big-endian (with any number of leading zero bytes but `n`). `n` must
    /// be odd, from 512 to 8192 bits long, with no leading zero byte; `e`
    /// must be odd, from 3 to `2^33 - 1`, as BoringSSL requires; `p` and `q`
    /// must be shorter than `n`, `p q = n`, `dP` and `qInv` must be less than
    /// `2^(8 len(p))` and `dQ` less than `2^(8 len(q))` (each fitting in its
    /// prime's bytes, without its leading zeros), and `qInv < p`. `d` is
    /// kept as it is given, and not used by the operation.
    ///
    /// Nothing else is checked here: not that `p` and `q` are prime, nor
    /// that the exponents match each other (see
    /// [`private_op`](Self::private_op), which never releases a result that
    /// does not match `e`).
    #[allow(clippy::too_many_arguments)]
    pub fn from_crt(
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
        let (p, q) = (trim(p), trim(q));
        if p.is_empty() || p.len() >= k || q.is_empty() || q.len() >= k {
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
        // The operation checks the modulus and the key along with the input:
        // as 0 is below any modulus, it computes a result for 0 exactly when
        // the key is valid.
        let mut out = vec![0; k];
        match key.private_op(&vec![0; k], &mut out) {
            Ok(()) => Ok(key),
            Err(_) => Err(Error::InvalidPrivateKey),
        }
    }

    /// The key with the modulus `n`, the public exponent `e`, the private
    /// exponent `d` and the primes `p` and `q`, all big-endian (with any
    /// number of leading zero bytes but `n`), as RFC 8017 §3.2's first form
    /// with the primes: computes the CRT values `dP = d mod (p - 1)`,
    /// `dQ = d mod (q - 1)` and `qInv = q⁻¹ mod p` and loads the key as
    /// [`from_crt`](Self::from_crt) does. `n` must be odd, from 512 to 8192
    /// bits long, with no leading zero byte; `e` must be odd, from 3 to
    /// `2^33 - 1`, as BoringSSL requires; `d` must be 1 to `n.len()` bytes
    /// long without its leading zeros, and `p` and `q` shorter than `n`;
    /// `p q = n`, and `q` must have an inverse modulo `p`. Nothing checks
    /// that `p` and `q` are prime or that `d` is the private exponent of
    /// `e` (but [`private_op`](Self::private_op) never releases a result
    /// that does not match `e`).
    pub fn from_primes(n: &[u8], e: &[u8], d: &[u8], p: &[u8], q: &[u8]) -> Result<Self, Error> {
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
        // `dq_len = q_len` and `scratch_len = 16 n_len`.
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
            PrivateKey::from_crt(n, e, d, p, q, &dp, &dq, &qinv)
        } else {
            Err(Error::InvalidPrivateKey)
        };
        for x in [&mut dp, &mut dq, &mut qinv] {
            crate::zeroize::zeroize(x);
        }
        key
    }

    /// The key with the modulus `n`, the public exponent `e` and the private
    /// exponent `d`, all big-endian (with any number of leading zero bytes
    /// but `n`), RFC 8017 §3.2's first form: recovers the primes `p > q` of
    /// `n` by SP 800-56B Rev. 2 Appendix C.1, trying the candidates
    /// `g = 2, 3, …` up to 100 of them, and loads the key as
    /// [`from_primes`](Self::from_primes) does. `n` must be odd, from 512 to
    /// 8192 bits long, with no leading zero byte, `e` odd, from 3 to
    /// `2^33 - 1`, and `d` 1 to `n.len()` bytes long without its leading
    /// zeros. For a valid RSA key
    /// the primes are found, but for a negligible fraction of keys.
    pub fn from_components(n: &[u8], e: &[u8], d: &[u8]) -> Result<Self, Error> {
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
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_recover_primes,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx | Backend::Ifma => vg_rsa_recover_primes_adx,
        };
        // SAFETY: each pointer is valid for its length (`p`, `q` and
        // `scratch` for writes), and none overlaps another or wraps around,
        // as they are distinct Rust allocations; the checks above give
        // `64 ≤ n_len ≤ 1024` and `1 ≤ e_len, d_len ≤ n_len`, and
        // `p_len = q_len = n_len` and `scratch_len = 16 n_len`; and the CPU
        // has the features of the function `select` chose.
        let r = unsafe {
            f(
                p.as_mut_ptr(),
                k,
                q.as_mut_ptr(),
                k,
                n.as_ptr(),
                k,
                e.as_ptr(),
                e.len(),
                d.as_ptr(),
                d.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds the private key.
        crate::zeroize::zeroize(&mut scratch);
        let key = if r == 1 {
            PrivateKey::from_primes(n, e, d, &p, &q)
        } else {
            Err(Error::InvalidPrivateKey)
        };
        for x in [&mut p, &mut q] {
            crate::zeroize::zeroize(x);
        }
        key
    }

    /// The length of the modulus in bytes, which is that of every input and
    /// output.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }

    /// The key's values, big-endian, as it holds them:
    /// `[n, e, d, p, q, dP, dQ, qInv]`.
    pub fn components(&self) -> [&[u8]; 8] {
        [
            &self.n, &self.e, &self.d, &self.p, &self.q, &self.dp, &self.dq, &self.qinv,
        ]
    }

    /// Whether BoringSSL's `RSA_check_key` accepts the key: `d < n`,
    /// `p < n`, `q < n`, `p q = n`, `d e ≡ 1` modulo `p - 1` and `q - 1`,
    /// `dP < p - 1`, `e dP ≡ 1 (mod p - 1)`, `dQ < q - 1`,
    /// `e dQ ≡ 1 (mod q - 1)`, `qInv < p` and `q qInv ≡ 1 (mod p)` (the
    /// modulus and `e` were checked when the key was loaded). Like
    /// `RSA_check_key`, it does not check that `p` and `q` are prime. Loading
    /// a key does not run this check, which costs about as much as two
    /// private-key operations.
    pub fn check_key(&self) -> bool {
        let k = self.n.len();
        let d = trim(&self.d);
        // `d = 0` fails `d e ≡ 1 (mod p - 1)`, and a `d` longer than `n`
        // fails `d < n`.
        if d.is_empty() || d.len() > k {
            return false;
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        // SAFETY: each pointer is valid for its length (`scratch` for
        // writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; `PrivateKey::from_crt` and the check
        // above give `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`,
        // `1 ≤ d_len ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
        // `dp_len = qinv_len = p_len`, `dq_len = q_len`, and
        // `scratch_len = 16 n_len`.
        let r = unsafe {
            vg_rsa_check_key(
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                d.as_ptr(),
                d.len(),
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

    /// RSADP (RSASP1) by §5.1.2's step 2.b, checked against the public
    /// exponent: computes `m = m_2 + q ((m_1 - m_2) qInv mod p)` for
    /// `m_1 = input^dP mod p` and `m_2 = input^dQ mod q`, and writes it to
    /// `out` if `m^e mod n` is the input, both big-endian and
    /// [`modulus_len`](Self::modulus_len) bytes long; for a valid RSA key
    /// this is `input^d mod n`. The input must be less than `n`. If
    /// `m^e mod n` is not the input (the key's values do not match, or the
    /// computation was faulted), returns [`Error::Fault`]. On an error `out`
    /// is left as zeros.
    pub fn private_op(&self, input: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let k = self.n.len();
        if input.len() != k || out.len() != k {
            return Err(Error::InvalidLength);
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_private_checked,
            // `select` chose them because the CPU has the features they need.
            Backend::Adx => vg_rsa_private_checked_adx,
            Backend::Ifma => vg_rsa_private_checked_ifma,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they
        // are distinct Rust allocations; `PrivateKey::from_crt` and the check
        // above give `64 ≤ n_len ≤ 1024`, `out_len = input_len = n_len`,
        // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
        // `dp_len = qinv_len = p_len`, `dq_len = q_len`, and
        // `scratch_len = 16 n_len`; and the CPU has the features of the
        // function `select` chose.
        let r = unsafe {
            f(
                out.as_mut_ptr(),
                k,
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                input.as_ptr(),
                k,
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
        // The working space holds the private key and powers of the input.
        crate::zeroize::zeroize(&mut scratch);
        // `PrivateKey::from_crt` checked `e` and the key, so a refusal means
        // the input is not below the modulus.
        match r {
            1 => Ok(()),
            2 => Err(Error::Fault),
            _ => Err(Error::InputOutOfRange),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rsa::tests::be;

    /// `a b`, big-endian, in `a.len() + b.len()` bytes.
    fn mul(a: &[u8], b: &[u8]) -> Vec<u8> {
        let mut r = vec![0u32; a.len() + b.len()];
        for (i, &x) in a.iter().rev().enumerate() {
            for (j, &y) in b.iter().rev().enumerate() {
                r[i + j] += u32::from(x) * u32::from(y);
            }
            for t in i..r.len() - 1 {
                r[t + 1] += r[t] >> 8;
                r[t] &= 0xff;
            }
        }
        r.iter().rev().map(|&x| x as u8).collect()
    }

    /// A key `p q = n` of two odd numbers with `dP = dQ = 1` and
    /// `qInv = 0`, for which the unchecked operation is `input mod q`.
    fn crt_key(pl: usize, ql: usize) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let p = vec![0xff; pl];
        let mut q = vec![0xff; ql];
        q[ql - 1] = 0xfd;
        (mul(&p, &q), p, q)
    }

    fn private(key: &PrivateKey, x: &[u8]) -> Result<Vec<u8>, Error> {
        let mut out = vec![0xa5; x.len()];
        let r = key.private_op(x, &mut out);
        if r.is_err() {
            assert_eq!(out, vec![0; x.len()]);
        }
        r.map(|()| out)
    }

    /// With `crt_key`'s keys and `e = 3`, 0 and 1 are their own result and
    /// pass the check; 2 is its own result too, but `2^3 ≠ 2`: the check
    /// refuses it. At lengths of `p` and `q` that are and are not whole
    /// words, equal or not.
    #[test]
    fn private_identities() {
        for (pl, ql) in [(32, 32), (33, 31), (40, 24), (100, 28), (512, 512)] {
            let (n, p, q) = crt_key(pl, ql);
            let k = n.len();
            assert_eq!(k, pl + ql);
            let key = PrivateKey::from_crt(&n, &[3], &[1], &p, &q, &[1], &[0, 1], &[0]).unwrap();
            assert_eq!(key.modulus_len(), k);
            for x in [be(0, k), be(1, k)] {
                assert_eq!(private(&key, &x), Ok(x.clone()));
            }
            assert_eq!(private(&key, &be(2, k)), Err(Error::Fault));
            assert_eq!(private(&key, &n), Err(Error::InputOutOfRange));
            assert_eq!(private(&key, &vec![0xff; k]), Err(Error::InputOutOfRange));
        }
        // Leading zeros on the primes and on `e`.
        let (n, p, q) = crt_key(32, 32);
        let p0 = [&[0, 0][..], &p].concat();
        assert!(PrivateKey::from_crt(&n, &[0, 3], &[], &p0, &q, &[1], &[1], &[0]).is_ok());
    }

    #[test]
    fn private_invalid() {
        let (n, p, q) = crt_key(32, 32);
        let new = |n: &[u8], e: &[u8], p: &[u8], q: &[u8], dp: &[u8], dq: &[u8], qi: &[u8]| {
            PrivateKey::from_crt(n, e, &[7], p, q, dp, dq, qi).map(|_| ())
        };
        assert_eq!(new(&n, &[3], &p, &q, &[1], &[1], &[0]), Ok(()));
        assert_eq!(
            new(&n, &[1, 0xff, 0xff, 0xff, 0xff], &p, &q, &[1], &[1], &[0]),
            Ok(())
        );
        assert_eq!(
            new(&n[1..], &[3], &p, &q, &[1], &[1], &[0]),
            Err(Error::InvalidModulus)
        );
        assert_eq!(
            new(&[1; 1025], &[3], &p, &q, &[1], &[1], &[0]),
            Err(Error::InvalidModulus)
        );
        for e in [&[][..], &[1], &[4], &[2, 0, 0, 0, 1]] {
            assert_eq!(
                new(&n, e, &p, &q, &[1], &[1], &[0]),
                Err(Error::InvalidExponent)
            );
        }
        let bad = Err(Error::InvalidPrivateKey);
        assert_eq!(new(&n, &[3], &[0; 3], &q, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &[3], &p, &[], &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &[3], &n, &q, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &[3], &p, &n, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &[3], &p, &q, &[1; 33], &[1], &[0]), bad);
        assert_eq!(new(&n, &[3], &p, &q, &[1], &[1; 33], &[0]), bad);
        assert_eq!(new(&n, &[3], &p, &q, &[1], &[1], &[1; 33]), bad);
        // `qInv = p`, `p q ≠ n`, an even `n`.
        assert_eq!(new(&n, &[3], &p, &q, &[1], &[1], &p), bad);
        let mut n2 = n.clone();
        n2[10] ^= 1;
        assert_eq!(new(&n2, &[3], &p, &q, &[1], &[1], &[0]), bad);
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        assert_eq!(new(&even, &[3], &p, &q, &[1], &[1], &[0]), bad);
        // `dP = dQ = 0`: the result for 0 is not 0, and fails the check.
        assert_eq!(new(&n, &[3], &p, &q, &[0], &[0], &[0]), bad);
        let key = PrivateKey::from_crt(&n, &[3], &[7], &p, &q, &[1], &[1], &[0]).unwrap();
        let mut out = [0; 64];
        assert_eq!(
            key.private_op(&[0; 63], &mut out),
            Err(Error::InvalidLength)
        );
        assert_eq!(
            key.private_op(&[0; 64], &mut out[..63]),
            Err(Error::InvalidLength)
        );
        assert!(!alloc::format!("{key:?}").contains('['));
    }

    /// With `d = 1`, `dP = dQ = 1`: as for `private_identities`, 0 and 1 are
    /// their own result, and 2 is refused by the check against `e = 3`.
    #[test]
    fn private_from_primes() {
        for (pl, ql) in [(32, 32), (33, 31), (40, 24), (100, 28)] {
            let (n, p, q) = crt_key(pl, ql);
            let k = n.len();
            let key = PrivateKey::from_primes(&n, &[0, 3], &[0, 1], &[&[0][..], &p].concat(), &q)
                .unwrap();
            for x in [be(0, k), be(1, k)] {
                assert_eq!(private(&key, &x), Ok(x.clone()));
            }
            assert_eq!(private(&key, &be(2, k)), Err(Error::Fault));
        }
        let (n, p, q) = crt_key(32, 32);
        let new = |n: &[u8], e: &[u8], d: &[u8], p: &[u8], q: &[u8]| {
            PrivateKey::from_primes(n, e, d, p, q).map(|_| ())
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
        assert_eq!(new(&n, &[3], &[1], &n, &q), bad);
        assert_eq!(new(&n, &[3], &[1], &p, &[]), bad);
        assert_eq!(new(&n, &[3], &[1], &p, &n), bad);
        // `p q ≠ n`, and `q` with no inverse modulo `p` (`gcd = 13`).
        let mut n2 = n.clone();
        n2[10] ^= 1;
        assert_eq!(new(&n2, &[3], &[1], &p, &q), bad);
        let (n3, p3, q3) = crt_key(36, 32);
        assert_eq!(new(&n3, &[3], &[1], &p3, &q3), bad);
    }

    /// `crt_key`'s keys fail the check (`d e = 21`, not 1 modulo `p - 1`),
    /// and so does a `d` of zero or longer than `n`, which the check refuses
    /// before the arithmetic.
    #[test]
    fn check_key_invalid() {
        let (n, p, q) = crt_key(32, 32);
        let key = |d: &[u8]| PrivateKey::from_crt(&n, &[3], d, &p, &q, &[1], &[1], &[0]).unwrap();
        for d in [&[7][..], &[0, 7], &[], &[0, 0], &[1; 65]] {
            assert!(!key(d).check_key());
        }
    }

    #[test]
    fn private_from_components_invalid() {
        let (n, _, _) = crt_key(32, 32);
        let new = |n: &[u8], e: &[u8], d: &[u8]| PrivateKey::from_components(n, e, d).map(|_| ());
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
