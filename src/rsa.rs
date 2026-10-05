//! The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also the
//! signature verification primitive RSAVP1 (§5.2.2), and the private-key
//! operation: RSADP (§5.1.2), which is also the signature primitive RSASP1
//! (§5.2.1), without any padding.
//!
//! A key is made by the verified `vg_rsa_public_precompute` (contract
//! `VG.Spec.Rsa.publicPrecomputeContract`), which checks the modulus and
//! computes what Montgomery multiplication needs of it once; the operation is
//! the verified `vg_rsa_public_precomputed_checked` (contract
//! `VG.Spec.Rsa.publicPrecomputedCheckedContract`), which checks the public
//! exponent within BoringSSL's limits (odd, from 3 to `2^33 - 1`) and the
//! input, computes `input^e mod n` by Montgomery multiplication, and writes it
//! out. Their timing may depend on the public key (`n` and `e`) but not on
//! the input. On a CPU with BMI2 and ADX, `vg_rsa_public_precompute_adx` and
//! `vg_rsa_public_precomputed_checked_adx`, with the same contracts, do the
//! same with a faster Montgomery multiplication.
//!
//! The private-key operation, with a key in the Chinese remainder form
//! `(p, q, dP, dQ, qInv)` (§3.2) and its public exponent `e`, is the verified
//! `vg_rsa_private_checked` (contract `VG.Spec.Rsa.privateCheckedContract`),
//! which checks the key and the input, computes the result `m` of §5.1.2's
//! step 2.b, and releases it only if `m^e mod n` is the input, as BoringSSL
//! does: a fault in the computation, or a key whose values do not match, is
//! never released ([`Error::Fault`]). Its timing may depend on the public key
//! and the lengths of `p` and `q`, but not on the input or on the private
//! key's values. On a CPU with BMI2 and ADX, `vg_rsa_private_checked_adx`
//! does the same with the faster Montgomery multiplication; on one with
//! AVX512_IFMA and AVX512VL too, `vg_rsa_private_checked_ifma` does the same,
//! computing the two exponentiations of a 2048-bit key with primes of 1024
//! bits at once, in 256-bit vector registers.
//!
//! A private key can also be loaded from its modulus, its exponents and its
//! primes `(n, e, d, p, q)`, whose CRT values `dP`, `dQ` and `qInv` the
//! verified `vg_rsa_crt_values` (contract `VG.Spec.Rsa.crtValuesContract`)
//! computes, or from `(n, e, d)` alone, whose primes the verified
//! `vg_rsa_recover_primes` (contract `VG.Spec.Rsa.recoverPrimesContract`)
//! recovers by SP 800-56B Rev. 2 Appendix C.1 (`vg_rsa_recover_primes_adx`
//! on a CPU with BMI2 and ADX). The timing of the first may depend on `n`
//! but not on the private key; that of the second on `n`, `e` and the number
//! of candidates the recovery tried (1 or 2 for most keys), but not
//! otherwise on `d`.
//!
//! This module only checks the lengths and the public exponent, and
//! allocates the memory they work in.
//!
//! This is a primitive for building padding schemes (OAEP, PSS, PKCS #1
//! v1.5) on: raw RSA on its own is not a secure encryption or signature
//! scheme.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa::{
    VG_RSA_PRIVATE_CHECKED_ADX_FEATURES, VG_RSA_PRIVATE_CHECKED_IFMA_FEATURES,
    VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES, VG_RSA_PUBLIC_PRECOMPUTED_CHECKED_ADX_FEATURES,
    VG_RSA_RECOVER_PRIMES_ADX_FEATURES, vg_rsa_crt_values, vg_rsa_private_checked,
    vg_rsa_private_checked_adx, vg_rsa_private_checked_ifma, vg_rsa_public_precompute,
    vg_rsa_public_precompute_adx, vg_rsa_public_precomputed_checked,
    vg_rsa_public_precomputed_checked_adx, vg_rsa_recover_primes, vg_rsa_recover_primes_adx,
};
use crate::arch::rsa_pkcs1_sig::{VG_RSA_PKCS1_SIGN_ADX_FEATURES, VG_RSA_PKCS1_SIGN_IFMA_FEATURES};
use crate::cpu::{Features, detected};

/// The implementations of `vg_rsa_public_precompute`,
/// `vg_rsa_public_precomputed_checked`, `vg_rsa_private_checked` and
/// `vg_rsa_recover_primes`, and of the functions built on them
/// (`vg_rsa_pkcs1_sign`, `crate::rsa_pkcs1_sig`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
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
    pub(crate) fn select(f: Features) -> Backend {
        let adx = f.contains(VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES)
            && f.contains(VG_RSA_PUBLIC_PRECOMPUTED_CHECKED_ADX_FEATURES)
            && f.contains(VG_RSA_PRIVATE_CHECKED_ADX_FEATURES)
            && f.contains(VG_RSA_RECOVER_PRIMES_ADX_FEATURES)
            && f.contains(VG_RSA_PKCS1_SIGN_ADX_FEATURES);
        if adx
            && f.contains(VG_RSA_PRIVATE_CHECKED_IFMA_FEATURES)
            && f.contains(VG_RSA_PKCS1_SIGN_IFMA_FEATURES)
        {
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
    /// The public exponent is not within BoringSSL's limits: odd, from 3
    /// to `2^33 - 1`.
    InvalidExponent,
    /// The input or the output is not as long as the modulus.
    InvalidLength,
    /// The input, as a number, is not less than the modulus.
    InputOutOfRange,
    /// The private key's values are too long for its modulus, the modulus
    /// is not valid, `p q` is not the modulus, or `qInv` is not less than
    /// `p`.
    InvalidPrivateKey,
    /// The private-key operation's result failed the check against the
    /// public exponent (its `e`-th power modulo `n` is not the input): the
    /// key's values do not match each other, or the computation was
    /// faulted. The result is not released.
    Fault,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidModulus => "invalid RSA modulus",
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidLength => "RSA input or output length is not the modulus length",
            Error::InputOutOfRange => "RSA input is not less than the modulus",
            Error::InvalidPrivateKey => "invalid RSA private key",
            Error::Fault => {
                "RSA private-key operation failed its check against the public exponent"
            }
        })
    }
}

impl core::error::Error for Error {}

/// The words of working space the operations need for an `n_len`-byte
/// modulus (`VG.Spec.Rsa.scratchWords`).
pub(crate) fn scratch_words(n_len: usize) -> usize {
    16 * n_len
}

/// The words of a modulus' precomputed values for an `n_len`-byte modulus
/// (`VG.Spec.Rsa.precomputedWords`).
fn precomputed_words(n_len: usize) -> usize {
    2 * n_len.div_ceil(8)
}

/// `x` without its leading zero bytes.
fn trim(x: &[u8]) -> &[u8] {
    let z = x.iter().take_while(|&&b| b == 0).count();
    &x[z..]
}

/// The public exponent `e` (big-endian) without its leading zero bytes, if
/// it is within BoringSSL's limits (`VG.Spec.Rsa.exponentValid`): odd, and
/// from 3 to `2^33 - 1`.
fn exponent(e: &[u8]) -> Result<&[u8], Error> {
    let e = trim(e);
    let v = e.iter().fold(0u64, |v, &b| v << 8 | u64::from(b));
    if e.len() <= 5 && v & 1 == 1 && (3..1 << 33).contains(&v) {
        Ok(e)
    } else {
        Err(Error::InvalidExponent)
    }
}

/// An RSA public key `(n, e)`, with the values of `n` that the operation
/// needs (`VG.Spec.Rsa.publicPrecompute`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub(crate) n: Vec<u8>,
    pub(crate) e: Vec<u8>,
    pre: Vec<u64>,
}

impl PublicKey {
    /// The key with the modulus `n` and the public exponent `e`, both
    /// big-endian. `n` must be odd, from 512 to 8192 bits long, with no
    /// leading zero byte; `e` must be odd, from 3 to `2^33 - 1` (with any
    /// number of leading zero bytes), as BoringSSL requires.
    pub fn new(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        let k = n.len();
        if !(MIN_MODULUS_LEN..=MAX_MODULUS_LEN).contains(&k) {
            return Err(Error::InvalidModulus);
        }
        let e = exponent(e)?;
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
            n: n.to_vec(),
            e: e.to_vec(),
            pre,
        })
    }

    /// The length of the modulus in bytes, which is that of every input and
    /// output.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }

    /// RSAEP (RSAVP1): writes `input^e mod n` to `out`, both big-endian and
    /// [`modulus_len`](Self::modulus_len) bytes long. The input must be
    /// less than `n`; on an error `out` is left as zeros.
    pub fn public_op(&self, input: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let k = self.n.len();
        if input.len() != k || out.len() != k {
            return Err(Error::InvalidLength);
        }
        let mut scratch = vec![0u64; scratch_words(k)];
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precomputed_checked,
            // `select` chose it because the CPU has the features it needs.
            Backend::Adx | Backend::Ifma => vg_rsa_public_precomputed_checked_adx,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they
        // are distinct Rust allocations; `PublicKey::new` and the check above
        // give `64 ≤ out_len ≤ 1024`, `input_len = out_len`,
        // `pre_len = 2 ⌈out_len / 8⌉`, `1 ≤ e_len ≤ 5 ≤ out_len`, and
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
        // `pre` holds a valid modulus' values and `e` is within the limits
        // (`PublicKey::new`), so a refusal means the input is not below `n`.
        if r == 1 {
            Ok(())
        } else {
            Err(Error::InputOutOfRange)
        }
    }
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
/// of RFC 8017 §3.2, with its public key `(n, e)` and its private exponent
/// `d`. Its private values are wiped when it is dropped.
pub struct PrivateKey {
    pub(crate) n: Vec<u8>,
    pub(crate) e: Vec<u8>,
    d: Vec<u8>,
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
            Backend::select(VG_RSA_PUBLIC_PRECOMPUTED_CHECKED_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_PRIVATE_CHECKED_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_RECOVER_PRIMES_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_PRIVATE_CHECKED_IFMA_FEATURES),
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

    /// BoringSSL's limits on `e`: odd, from 3 to `2^33 - 1`, with any number
    /// of leading zero bytes.
    #[test]
    fn exponents() {
        let ok: [&[u8]; 5] = [
            &[3],
            &[0, 0, 3],
            &[1, 0, 1],
            &[1, 0xff, 0xff, 0xff, 0xff],
            &[0x41],
        ];
        for e in ok {
            assert_eq!(exponent(e), Ok(trim(e)));
        }
        let bad: [&[u8]; 8] = [
            &[],
            &[0],
            &[1],
            &[2],
            &[0, 0, 4],
            &[2, 0, 0, 0, 1],
            &[1, 0, 0, 0, 0, 1],
            &[0xff; 64],
        ];
        for e in bad {
            assert_eq!(exponent(e), Err(Error::InvalidExponent));
        }
    }

    /// Identities that hold for every modulus, at every length from 512 to
    /// 8192 bits, including lengths that are not a whole number of words.
    #[test]
    fn identities() {
        for k in [64, 65, 71, 72, 127, 128, 255, 256, 384, 512, 1023, 1024] {
            for n in [modulus(k), vec![0xff; k]] {
                let m1 = minus_one(&n);
                let one = be(1, k);
                assert_eq!(op(&n, &[3], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[0, 3], &m1), Ok(m1.clone()));
                assert_eq!(op(&n, &[3], &one), Ok(one.clone()));
                assert_eq!(op(&n, &[0x41], &vec![0; k]), Ok(vec![0; k]));
                // 2^63 and 2^(8 + 63): no reduction.
                assert_eq!(op(&n, &[63], &be(2, k)), Ok(be(1 << 63, k)));
                let mut big = vec![0; k];
                big[k - 9] = 0x80;
                assert_eq!(op(&n, &[0, 71], &be(2, k)), Ok(big));
                // The input `n - 1` with the longest exponent, of all ones.
                assert_eq!(op(&n, &[1, 0xff, 0xff, 0xff, 0xff], &m1), Ok(m1.clone()));
                // Out of range.
                assert_eq!(op(&n, &[3], &n), Err(Error::InputOutOfRange));
                assert_eq!(op(&n, &[3], &vec![0xff; k]), Err(Error::InputOutOfRange));
            }
            // For `n = 2^(8k) - 1`, `2^(8k + 1) = 2` and `2^(8k + 5) = 32`.
            let n = vec![0xff; k];
            let bits = (8 * k) as u64;
            assert_eq!(op(&n, &(bits + 1).to_be_bytes(), &be(2, k)), Ok(be(2, k)));
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
        for e in [&[][..], &[1], &[2], &[1; 64]] {
            assert_eq!(PublicKey::new(&n, e), Err(Error::InvalidExponent));
        }
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
            Error::Fault,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
