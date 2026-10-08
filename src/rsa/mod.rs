//! The RSA public-key operation: RSAEP (RFC 8017 §5.1.1), which is also the
//! signature verification primitive RSAVP1 (§5.2.2), and the private-key
//! operation: RSADP (§5.1.2), which is also the signature primitive RSASP1
//! (§5.2.1), without any padding.
//!
//! A key's first operation runs the verified `vg_rsa_public_precompute`
//! (contract `VG.Spec.Rsa.publicPrecomputeContract`), which checks the
//! modulus and computes what Montgomery multiplication needs of it, once for
//! the key, as OpenSSL and AWS-LC set up their Montgomery values at a key's
//! first operation: loading the key only checks the modulus as it does. The
//! operation is the verified `vg_rsa_public_precomputed_checked` (contract
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
//! computing the two exponentiations of a 2048-, 3072- or 4096-bit key with
//! primes of half its size at once, in 256-bit vector registers.
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
//! [`PrivateKey::check_key`] checks a loaded key as BoringSSL's
//! `RSA_check_key` does, by the verified `vg_rsa_check_key` (contract
//! `VG.Spec.Rsa.checkKeyContract`): `d < n`, `p q = n`, `d` and the CRT
//! exponents inverse to `e` modulo `p - 1` and `q - 1`, `qInv < p` and
//! `q qInv ≡ 1 (mod p)`. Its timing may depend on the public key and the
//! lengths of the private values, but not on their values. Loading a key does
//! not run it.
//!
//! This module only checks the lengths, the form of the modulus and the
//! public exponent, and allocates the memory they work in.
//!
//! This is a primitive for building padding schemes (OAEP, PSS, PKCS #1
//! v1.5) on: raw RSA on its own is not a secure encryption or signature
//! scheme.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

mod precomputed;
use precomputed::{Precomputed, modulus_valid};
mod scratch;
pub(crate) use scratch::Scratch;
use scratch::VerifyScratch;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa::vg_rsa_public_precomputed_checked;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa::{
    VG_RSA_PRIVATE_CHECKED_ADX_FEATURES, VG_RSA_PRIVATE_CHECKED_IFMA_FEATURES,
    VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES, VG_RSA_PUBLIC_PRECOMPUTED_CHECKED_ADX_FEATURES,
    VG_RSA_RECOVER_PRIMES_ADX_FEATURES, vg_rsa_public_precomputed_checked_adx,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_keygen::VG_RSA_KEYGEN_CANDIDATE_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pkcs1_sig::{VG_RSA_PKCS1_SIGN_ADX_FEATURES, VG_RSA_PKCS1_SIGN_IFMA_FEATURES};
use crate::cpu::{Features, detected};

/// The implementations of `vg_rsa_public_precompute`,
/// `vg_rsa_public_precomputed_checked`, `vg_rsa_private_checked` and
/// `vg_rsa_recover_primes`, and of the functions built on them
/// (`vg_rsa_pkcs1_sign`, `crate::rsa_pkcs1_sig`; `vg_rsa_keygen_candidate`,
/// `crate::rsa_keygen`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline ISA.
    Baseline,
    /// Montgomery multiplication with BMI2's `mulx` and ADX's `adcx` and
    /// `adox`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `Adx`, and for the private-key operation, AVX512_IFMA's
    /// multiplications for 2048-, 3072- and 4096-bit keys.
    #[cfg(target_arch = "x86_64")]
    Ifma,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        let adx = f.contains(VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES)
            && f.contains(VG_RSA_PUBLIC_PRECOMPUTED_CHECKED_ADX_FEATURES)
            && f.contains(VG_RSA_PRIVATE_CHECKED_ADX_FEATURES)
            && f.contains(VG_RSA_RECOVER_PRIMES_ADX_FEATURES)
            && f.contains(VG_RSA_PKCS1_SIGN_ADX_FEATURES)
            && f.contains(VG_RSA_KEYGEN_CANDIDATE_ADX_FEATURES);
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

    /// The best implementation a CPU with the features `f` can run: on
    /// AArch64, the baseline is the only one.
    #[cfg(target_arch = "aarch64")]
    pub(crate) fn select(_f: Features) -> Backend {
        Backend::Baseline
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

/// `x` without its leading zero bytes.
pub(crate) fn trim(x: &[u8]) -> &[u8] {
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
/// needs (`VG.Spec.Rsa.publicPrecompute`), once its first operation has
/// computed them.
///
/// After PSS verification, retains one wiped working buffer for reuse.
/// Concurrent verifications use independent buffers; cloning a key starts with an
/// empty cache, and with the values of `n` if they are computed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub(crate) n: Vec<u8>,
    pub(crate) e: Vec<u8>,
    pre: Precomputed,
    pub(crate) verify_scratch: VerifyScratch,
}

impl PublicKey {
    /// The key with the modulus `n` and the public exponent `e`, both
    /// big-endian. `n` must be odd, from 512 to 8192 bits long, with no
    /// leading zero byte; `e` must be odd, from 3 to `2^33 - 1` (with any
    /// number of leading zero bytes), as BoringSSL requires.
    pub fn new(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        if !modulus_valid(n) {
            return Err(Error::InvalidModulus);
        }
        let e = exponent(e)?;
        Ok(PublicKey {
            n: n.to_vec(),
            e: e.to_vec(),
            pre: Precomputed::new(),
            verify_scratch: VerifyScratch::new(),
        })
    }

    /// The values of `n` (`VG.Spec.Rsa.publicPrecompute`), computed in
    /// `scratch` (at least `scratch_words(n_len)` words, left holding only
    /// values of `n`) at the key's first operation.
    pub(crate) fn pre(&self, scratch: &mut [u64]) -> &[u64] {
        self.pre.get(&self.n, scratch)
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
        let pre = self.pre(&mut scratch);
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_public_precomputed_checked,
            // `select` chose it because the CPU has the features it needs.
            #[cfg(target_arch = "x86_64")]
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
                pre.as_ptr(),
                pre.len(),
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

mod privatekey;
pub use privatekey::PrivateKey;

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use alloc::string::ToString;

    /// The CRT form `[n, p, q, dP, dQ, qInv]` of a key whose values match
    /// each other for `e = 3`, but whose factors are not prime: `p = 2^(8a) - 1`
    /// (`a` bytes of `0xff`, `3 | p`) and `q = 2^(8a) + 1` (`a + 1` bytes),
    /// `n = 2^(16a) - 1`, `dP = p / 3` (`3 dP = (p - 1) + 1`),
    /// `dQ = (2^(8a + 1) + 1) / 3` (`3 dQ = 2 (q - 1) + 1`) and
    /// `qInv = 2^(8a - 1)` (`q ≡ 2 (mod p)`). With `swap`, `p` and `q` are
    /// the other way round, and still `qInv = 2^(8a - 1)` (`q ≡ -2`). Every
    /// check of `PrivateKey::from_crt` passes; the private-key operation's
    /// result for most inputs does not pass its check against `e`.
    pub(crate) fn composite(a: usize, swap: bool) -> [Vec<u8>; 6] {
        let ones = vec![0xff; a];
        let mut plus = vec![0; a + 1];
        plus[0] = 1;
        plus[a] = 1;
        let third = vec![0x55; a];
        let mut two_thirds = vec![0xaa; a];
        two_thirds[a - 1] = 0xab;
        let mut half = vec![0; a];
        half[0] = 0x80;
        let n = vec![0xff; 2 * a];
        if swap {
            [n, plus, ones, two_thirds, third, half]
        } else {
            [n, ones, plus, third, two_thirds, half]
        }
    }

    /// `composite(32, false)` loaded, with `d = 1`, and its public key.
    pub(crate) fn composite_key() -> (PrivateKey, PublicKey) {
        let [n, p, q, dp, dq, qinv] = composite(32, false);
        (
            PrivateKey::from_crt(&n, &[3], &[1], &p, &q, &dp, &dq, &qinv).unwrap(),
            PublicKey::new(&n, &[3]).unwrap(),
        )
    }

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
    pub(super) fn be(x: u64, k: usize) -> Vec<u8> {
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
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn backends_x86_64() {
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
            Backend::select(Features::of(&["avx", "avx512f", "avx512ifma", "avx512vl"])),
            Backend::Baseline
        );
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
