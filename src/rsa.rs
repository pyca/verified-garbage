//! The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also the
//! signature verification primitive RSAVP1 (§5.2.2), and the private-key
//! operation: RSADP (§5.1.2), which is also the signature primitive RSASP1
//! (§5.2.1), without any padding.
//!
//! A key is made by the verified `vg_rsa_public_precompute` (contract
//! `VG.Spec.Rsa.publicPrecomputeContract`), which checks the modulus and
//! computes what Montgomery multiplication needs of it once; the operation is
//! the verified `vg_rsa_public_precomputed` (contract
//! `VG.Spec.Rsa.publicPrecomputedContract`), which checks the input, computes
//! `input^e mod n` by Montgomery multiplication, and writes it out. Their
//! timing may depend on the public key (`n` and `e`) but not on the input.
//! On a CPU with BMI2 and ADX, `vg_rsa_public_precompute_adx` and
//! `vg_rsa_public_precomputed_adx`, with the same contracts, do the same with
//! a faster Montgomery multiplication.
//!
//! The private-key operation, with a key in the Chinese remainder form
//! `(p, q, dP, dQ, qInv)` (§3.2), is the verified `vg_rsa_private_crt`
//! (contract `VG.Spec.Rsa.privateCrtContract`), which checks the key and the
//! input and computes the result of §5.1.2's step 2.b. Its timing may depend
//! on the modulus `n` and the lengths of `p` and `q`, but not on the input
//! or on the private key's values. On a CPU with BMI2 and ADX,
//! `vg_rsa_private_crt_adx` does the same with the faster Montgomery
//! multiplication; on one with AVX512_IFMA and AVX512VL too,
//! `vg_rsa_private_crt_ifma` does the same, computing the two
//! exponentiations of a 2048-bit key with primes of 1024 bits at once, in
//! 256-bit vector registers.
//!
//! This module only checks the lengths and allocates the memory they work in.
//!
//! This is a primitive for building padding schemes (OAEP, PSS, PKCS #1
//! v1.5) on: raw RSA on its own is not a secure encryption or signature
//! scheme.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa::{
    VG_RSA_PRIVATE_CRT_ADX_FEATURES, VG_RSA_PRIVATE_CRT_IFMA_FEATURES,
    VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES, VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES,
    vg_rsa_private_crt, vg_rsa_private_crt_adx, vg_rsa_private_crt_ifma, vg_rsa_public_precompute,
    vg_rsa_public_precompute_adx, vg_rsa_public_precomputed, vg_rsa_public_precomputed_adx,
};
use crate::cpu::{Features, detected};

/// The implementations of `vg_rsa_public_precompute`,
/// `vg_rsa_public_precomputed` and `vg_rsa_private_crt`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA.
    Baseline,
    /// Montgomery multiplication with BMI2's `mulx` and ADX's `adcx` and
    /// `adox`.
    Adx,
    /// `Adx`, and for the private-key operation, AVX512_IFMA's
    /// multiplications for 2048-bit keys.
    Ifma,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    fn select(f: Features) -> Backend {
        let adx = f.contains(VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES)
            && f.contains(VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES)
            && f.contains(VG_RSA_PRIVATE_CRT_ADX_FEATURES);
        if adx && f.contains(VG_RSA_PRIVATE_CRT_IFMA_FEATURES) {
            Backend::Ifma
        } else if adx {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }
}

/// The shortest modulus, in bytes (512 bits).
pub const MIN_MODULUS_LEN: usize = 64;
/// The longest modulus, in bytes (8192 bits).
pub const MAX_MODULUS_LEN: usize = 1024;

/// Why an RSA operation was refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The modulus is not an odd number of 512 to 8192 bits, written in
    /// as few bytes as it takes.
    InvalidModulus,
    /// The public exponent is empty or longer than the modulus.
    InvalidExponent,
    /// The input or the output is not as long as the modulus.
    InvalidLength,
    /// The input, as a number, is not less than the modulus.
    InputOutOfRange,
    /// The private key's values are too long for its modulus, the modulus
    /// is not valid, `p q` is not the modulus, or `qInv` is not less than
    /// `p`.
    InvalidPrivateKey,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidModulus => "invalid RSA modulus",
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidLength => "RSA input or output length is not the modulus length",
            Error::InputOutOfRange => "RSA input is not less than the modulus",
            Error::InvalidPrivateKey => "invalid RSA private key",
        })
    }
}

impl core::error::Error for Error {}

/// The words of working space the operations need for an `n_len`-byte
/// modulus (`VG.Spec.Rsa.scratchWords`).
fn scratch_words(n_len: usize) -> usize {
    16 * n_len
}

/// The words of a modulus' precomputed values for an `n_len`-byte modulus
/// (`VG.Spec.Rsa.precomputedWords`).
fn precomputed_words(n_len: usize) -> usize {
    2 * n_len.div_ceil(8)
}

/// An RSA public key `(n, e)`, with the values of `n` that the operation
/// needs (`VG.Spec.Rsa.publicPrecompute`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    n_len: usize,
    e: Vec<u8>,
    pre: Vec<u64>,
}

impl PublicKey {
    /// The key with the modulus `n` and the public exponent `e`, both
    /// big-endian. `n` must be odd, from 512 to 8192 bits long, with no
    /// leading zero byte; `e` must be 1 to `n.len()` bytes long.
    pub fn new(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        if e.is_empty() || e.len() > k {
            return Err(Error::InvalidExponent);
        }
        let mut pre = vec![0u64; precomputed_words(k)];
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precompute,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx | Backend::Ifma => vg_rsa_public_precompute_adx,
        };
        // SAFETY: each pointer is valid for its length (`pre` and `scratch`
        // for writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; the check above gives
        // `64 ≤ n_len ≤ 1024`, and `pre_len = 2 ⌈n_len / 8⌉` and
        // `scratch_len = 16 n_len`; and the CPU has the features of the
        // function `select` chose.
        let r = unsafe {
            f(
                pre.as_mut_ptr(),
                pre.len(),
                n.as_ptr(),
                k,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds only values of the public modulus, so it is
        // not destroyed. `vg_rsa_public_precompute` refuses a modulus that is
        // not valid (`VG.Spec.Rsa.modulusValid`).
        if r != 1 {
            return Err(Error::InvalidModulus);
        }
        Ok(PublicKey {
            n_len: k,
            e: e.to_vec(),
            pre,
        })
    }

    /// The length of the modulus in bytes, which is that of every input and
    /// output.
    pub fn modulus_len(&self) -> usize {
        self.n_len
    }

    /// RSAEP (RSAVP1): writes `input^e mod n` to `out`, both big-endian and
    /// [`modulus_len`](Self::modulus_len) bytes long. The input must be
    /// less than `n`; on an error `out` is left as zeros.
    pub fn public_op(&self, input: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let k = self.n_len;
        if input.len() != k || out.len() != k {
            return Err(Error::InvalidLength);
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precomputed,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx | Backend::Ifma => vg_rsa_public_precomputed_adx,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they
        // are distinct Rust allocations; `PublicKey::new` and the check above
        // give `64 ≤ out_len ≤ 1024`, `input_len = out_len`,
        // `pre_len = 2 ⌈out_len / 8⌉`, `1 ≤ e_len ≤ out_len`, and
        // `scratch_len = 16 out_len`; `pre` holds what
        // `vg_rsa_public_precompute` (or its variant, with the same contract)
        // wrote for the modulus, returning 1; and the CPU has the features of
        // the function `select` chose.
        let r = unsafe {
            f(
                out.as_mut_ptr(),
                k,
                self.pre.as_ptr(),
                self.pre.len(),
                self.e.as_ptr(),
                self.e.len(),
                input.as_ptr(),
                k,
                scratch.as_mut_ptr(),
                scratch.len(),
            )
        };
        // The working space holds powers of the input.
        crate::zeroize::zeroize(&mut scratch);
        // `pre` holds a valid modulus' values (`PublicKey::new`), so a refusal
        // means the input is not below it.
        if r == 1 {
            Ok(())
        } else {
            Err(Error::InputOutOfRange)
        }
    }
}

/// `x` without its leading zero bytes.
fn trim(x: &[u8]) -> &[u8] {
    let z = x.iter().take_while(|&&b| b == 0).count();
    &x[z..]
}

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
/// of RFC 8017 §3.2, with its modulus `n`. Its values are wiped when it is
/// dropped.
pub struct PrivateKey {
    n: Vec<u8>,
    p: Vec<u8>,
    q: Vec<u8>,
    dp: Vec<u8>,
    dq: Vec<u8>,
    qinv: Vec<u8>,
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

impl Drop for PrivateKey {
    fn drop(&mut self) {
        for x in [
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
    /// The key with the modulus `n` and the values `p`, `q`, `dP`, `dQ`
    /// and `qInv`, all big-endian (with any number of leading zero bytes
    /// but `n`). `n` must be odd, from 512 to 8192 bits long, with no
    /// leading zero byte; `p` and `q` must be shorter than `n`, `p q = n`,
    /// `dP` and `qInv` must be less than `2^(8 len(p))` and `dQ` less than
    /// `2^(8 len(q))` (each fitting in its prime's bytes, without its
    /// leading zeros), and `qInv < p`. Nothing checks that `p` and `q` are
    /// prime or that the exponents match a public exponent: for a key that
    /// RFC 8017 does not allow, the operation's result is still
    /// [`private_op`](Self::private_op)'s formula, but not `input^d mod n`.
    pub fn from_crt(
        n: &[u8],
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
            p: p.to_vec(),
            q: q.to_vec(),
            dp,
            dq,
            qinv,
        };
        // The operation checks the modulus and the key along with the input:
        // as 0 is below any modulus, it succeeds on 0 exactly when the key
        // is valid.
        let mut out = vec![0; k];
        match key.private_op(&vec![0; k], &mut out) {
            Ok(()) => Ok(key),
            Err(_) => Err(Error::InvalidPrivateKey),
        }
    }

    /// The length of the modulus in bytes, which is that of every input and
    /// output.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }

    /// RSADP (RSASP1) by §5.1.2's step 2.b: writes
    /// `m_2 + q ((m_1 - m_2) qInv mod p)` for `m_1 = input^dP mod p` and
    /// `m_2 = input^dQ mod q` to `out`, both big-endian and
    /// [`modulus_len`](Self::modulus_len) bytes long; for a valid RSA key
    /// this is `input^d mod n`. The input must be less than `n`; on an error
    /// `out` is left as zeros.
    pub fn private_op(&self, input: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let k = self.n.len();
        if input.len() != k || out.len() != k {
            return Err(Error::InvalidLength);
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_private_crt,
            // `select` chose them because the CPU has the features they need.
            Backend::Adx => vg_rsa_private_crt_adx,
            Backend::Ifma => vg_rsa_private_crt_ifma,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they
        // are distinct Rust allocations; `PrivateKey::from_crt` and the check
        // above give `64 ≤ n_len ≤ 1024`, `out_len = input_len = n_len`,
        // `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
        // `dp_len = qinv_len = p_len`, `dq_len = q_len`, and
        // `scratch_len = 16 n_len`; and the CPU has the features of the
        // function `select` chose.
        let r = unsafe {
            f(
                out.as_mut_ptr(),
                k,
                self.n.as_ptr(),
                k,
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
        // `PrivateKey::from_crt` checked the key, so a refusal means the
        // input is not below the modulus.
        if r == 1 {
            Ok(())
        } else {
            Err(Error::InputOutOfRange)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

    /// An odd `k`-byte modulus with its top bit set, with bytes from a
    /// simple generator so that no word is all ones.
    fn modulus(k: usize) -> Vec<u8> {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut n: Vec<u8> = (0..k)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x as u8
            })
            .collect();
        n[0] |= 0x80;
        n[k - 1] |= 1;
        n
    }

    fn minus_one(n: &[u8]) -> Vec<u8> {
        let mut m = n.to_vec();
        // `n` is odd: only its last byte changes.
        *m.last_mut().unwrap() -= 1;
        m
    }

    /// `x` as `k` big-endian bytes.
    fn be(x: u64, k: usize) -> Vec<u8> {
        let mut v = vec![0; k];
        v[k - 8..].copy_from_slice(&x.to_be_bytes());
        v
    }

    fn op(n: &[u8], e: &[u8], x: &[u8]) -> Result<Vec<u8>, Error> {
        let mut out = vec![0xa5; n.len()];
        let r = PublicKey::new(n, e)?.public_op(x, &mut out);
        if r.is_err() {
            assert_eq!(out, vec![0; n.len()]);
        }
        r.map(|()| out)
    }

    #[test]
    fn backends() {
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
        assert_eq!(Backend::select(Features::of(&["bmi2"])), Backend::Baseline);
        assert_eq!(
            Backend::select(VG_RSA_PUBLIC_PRECOMPUTED_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_PRIVATE_CRT_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_PRIVATE_CRT_IFMA_FEATURES),
            Backend::Ifma
        );
        assert_eq!(
            Backend::select(Features::of(&["avx", "avx2", "avx512ifma", "avx512vl"])),
            Backend::Baseline
        );
    }

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
    /// `qInv = 0`, for which the operation is `input mod q`.
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

    /// Inputs below `q` are their own result, at lengths of `p` and `q`
    /// that are and are not whole words, equal or not.
    #[test]
    fn private_identities() {
        for (pl, ql) in [(32, 32), (33, 31), (40, 24), (100, 28), (512, 512)] {
            let (n, p, q) = crt_key(pl, ql);
            let k = n.len();
            assert_eq!(k, pl + ql);
            let key = PrivateKey::from_crt(&n, &p, &q, &[1], &[0, 1], &[0]).unwrap();
            assert_eq!(key.modulus_len(), k);
            for x in [be(0, k), be(1, k), be(2, k), be(0x1234_5678_9abc_def0, k)] {
                assert_eq!(private(&key, &x), Ok(x.clone()));
            }
            assert_eq!(private(&key, &n), Err(Error::InputOutOfRange));
            assert_eq!(private(&key, &vec![0xff; k]), Err(Error::InputOutOfRange));
        }
        // Leading zeros on the primes.
        let (n, p, q) = crt_key(32, 32);
        let p0 = [&[0, 0][..], &p].concat();
        assert!(PrivateKey::from_crt(&n, &p0, &q, &[1], &[1], &[0]).is_ok());
    }

    #[test]
    fn private_invalid() {
        let (n, p, q) = crt_key(32, 32);
        let new = |n: &[u8], p: &[u8], q: &[u8], dp: &[u8], dq: &[u8], qi: &[u8]| {
            PrivateKey::from_crt(n, p, q, dp, dq, qi).map(|_| ())
        };
        assert_eq!(new(&n, &p, &q, &[1], &[1], &[0]), Ok(()));
        assert_eq!(
            new(&n[1..], &p, &q, &[1], &[1], &[0]),
            Err(Error::InvalidModulus)
        );
        assert_eq!(
            new(&[1; 1025], &p, &q, &[1], &[1], &[0]),
            Err(Error::InvalidModulus)
        );
        let bad = Err(Error::InvalidPrivateKey);
        assert_eq!(new(&n, &[0; 3], &q, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &p, &[], &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &n, &q, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &p, &n, &[1], &[1], &[0]), bad);
        assert_eq!(new(&n, &p, &q, &[1; 33], &[1], &[0]), bad);
        assert_eq!(new(&n, &p, &q, &[1], &[1; 33], &[0]), bad);
        assert_eq!(new(&n, &p, &q, &[1], &[1], &[1; 33]), bad);
        // `qInv = p`, `p q ≠ n`, an even `n`.
        assert_eq!(new(&n, &p, &q, &[1], &[1], &p), bad);
        let mut n2 = n.clone();
        n2[10] ^= 1;
        assert_eq!(new(&n2, &p, &q, &[1], &[1], &[0]), bad);
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        assert_eq!(new(&even, &p, &q, &[1], &[1], &[0]), bad);
        let key = PrivateKey::from_crt(&n, &p, &q, &[1], &[1], &[0]).unwrap();
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

    /// Identities that hold for every modulus, at every length from 512 to
    /// 8192 bits, including lengths that are not a whole number of words.
    #[test]
    fn identities() {
        for k in [64, 65, 71, 72, 127, 128, 255, 256, 384, 512, 1023, 1024] {
            for n in [modulus(k), vec![0xff; k]] {
                let m1 = minus_one(&n);
                let one = be(1, k);
                assert_eq!(op(&n, &[0], &m1), Ok(one.clone()));
                assert_eq!(op(&n, &[1], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[2], &m1), Ok(one.clone()));
                assert_eq!(op(&n, &[0, 3], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[1], &one), Ok(one.clone()));
                assert_eq!(op(&n, &[0x41], &vec![0; k]), Ok(vec![0; k]));
                // 2^63 and 2^(8 + 63): no reduction.
                assert_eq!(op(&n, &[63], &be(2, k)), Ok(be(1 << 63, k)));
                let mut big = vec![0; k];
                big[k - 9] = 0x80;
                assert_eq!(op(&n, &[0, 71], &be(2, k)), Ok(big));
                // The input `n - 1` with a long exponent of all ones (odd).
                assert_eq!(op(&n, &vec![0xff; k], &m1), Ok(m1.clone()));
                // Out of range.
                assert_eq!(op(&n, &[3], &n), Err(Error::InputOutOfRange));
                assert_eq!(op(&n, &[3], &vec![0xff; k]), Err(Error::InputOutOfRange));
            }
            // For `n = 2^(8k) - 1`, `2^(8k) = 1` and `2^(8k + 5) = 32`.
            let n = vec![0xff; k];
            let bits = (8 * k) as u64;
            assert_eq!(op(&n, &bits.to_be_bytes(), &be(2, k)), Ok(be(1, k)));
            assert_eq!(
                op(&n, &(bits + 5).to_be_bytes()[6..], &be(2, k)),
                Ok(be(32, k))
            );
        }
    }

    #[test]
    fn invalid() {
        let n = modulus(64);
        assert_eq!(PublicKey::new(&n, &[3]).unwrap().modulus_len(), 64);
        let mut half = n.clone();
        half[0] = 0x7f;
        let mut zero = modulus(65);
        zero[0] = 0;
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        let mut ok = modulus(65);
        ok[0] = 1;
        assert!(PublicKey::new(&ok, &[3]).is_ok());
        let bad: [&[u8]; 6] = [&modulus(63), &half, &zero, &even, &modulus(1025), &[]];
        for bad in bad {
            assert_eq!(PublicKey::new(bad, &[3]), Err(Error::InvalidModulus));
        }
        assert_eq!(PublicKey::new(&n, &[]), Err(Error::InvalidExponent));
        assert_eq!(PublicKey::new(&n, &[1; 65]), Err(Error::InvalidExponent));
        assert!(PublicKey::new(&n, &[1; 64]).is_ok());
        let key = PublicKey::new(&n, &[3]).unwrap();
        let mut out = [0; 64];
        assert_eq!(key.public_op(&[0; 63], &mut out), Err(Error::InvalidLength));
        assert_eq!(
            key.public_op(&[0; 64], &mut out[..63]),
            Err(Error::InvalidLength)
        );
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidModulus,
            Error::InvalidExponent,
            Error::InvalidLength,
            Error::InputOutOfRange,
            Error::InvalidPrivateKey,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
