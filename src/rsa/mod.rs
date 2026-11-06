//! RSA keys (RFC 8017 §3) and their operations: the padding schemes are
//! methods of the keys ([`PublicKey::encrypt_oaep`],
//! [`PrivateKey::sign_pss`], …), with each scheme's types in its submodule
//! ([`oaep`], [`pss`], [`pkcs1_sig`], and for compatibility only
//! [`pkcs1_enc`]), and key generation is [`keygen::generate`].
//!
//! The keys' values (`n`, `e`, `d`, the primes and the CRT values) are
//! [`BigUint`]s, made from and read as big-endian bytes. Raw RSA is not part
//! of the API: on its own it is not a secure encryption or signature scheme.
//! Public exponents are odd, from 3 to `2^33 - 1` (BoringSSL's limits). Every
//! way of loading a [`PrivateKey`] checks it as BoringSSL's `RSA_check_key`
//! does, and like it does not check that its factors are prime: every
//! private-key operation releases its result only if raising it to `e` gives
//! back the input, so a fault, or a key with a composite factor, never
//! releases one. The timing may depend on the public key and the lengths of
//! the primes `p` and `q`, but not on the private values themselves: as
//! BoringSSL does, a key holds `d` in as many bytes as `n` and the CRT values
//! in as many as their primes, whatever lengths they were given in, and its
//! arithmetic modulo each prime is at that prime's length.

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

mod precomputed;
use precomputed::{Precomputed, modulus_valid};
mod scratch;
pub(crate) use scratch::Scratch;
use scratch::VerifyScratch;

use alloc::vec::Vec;
use core::fmt;

#[cfg(target_arch = "x86_64")]
use crate::arch::rsa::VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_keygen::VG_RSA_GENERATE_ADX_FEATURES;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pkcs1_sig::{
    VG_RSA_PKCS1_SIGN_ADX_FEATURES, VG_RSA_PKCS1_SIGN_IFMA_FEATURES,
    VG_RSA_PKCS1_VERIFY_PRECOMPUTED_ADX_FEATURES, VG_RSA_PKCS1_VERIFY_PRECOMPUTED_IFMA_FEATURES,
};
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
use crate::arch::{
    rsa_keygen::VG_RSA_PRIME_SEARCH_UMAAL_FEATURES, rsa_pkcs1_sig::VG_RSA_PKCS1_SIGN_UMAAL_FEATURES,
};
use verified_garbage_cpu::Features;

/// The implementations of `vg_rsa_public_precompute` and of the functions
/// built on the verified code's own RSA operations,
/// `vg_rsa_public_precomputed_checked` and `vg_rsa_private_checked` (which
/// only verified code calls): the padding schemes' (`vg_rsa_pkcs1_sign`,
/// `crate::rsa::pkcs1_sig`, …) and key generation's (`crate::rsa::keygen`):
/// `vg_rsa_generate` on x86-64, `vg_rsa_prime_search` elsewhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Baseline,
    /// `_adx`.
    #[cfg(target_arch = "x86_64")]
    Adx,
    /// `_ifma` where a function has one, and `_adx` otherwise.
    #[cfg(target_arch = "x86_64")]
    Ifma,
    /// `_umaal`.
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
    Umaal,
}

impl Backend {
    /// The CPU features `select` requires to choose each implementation, by
    /// its discriminant: every CPU it is chosen for has them, so a function
    /// chosen with it may need no other, which its caller checks when it
    /// compiles (`assert!` in a `const`).
    #[cfg(target_arch = "x86_64")]
    pub(crate) const REQUIRES: &[Features] = &{
        let adx = Features::all(&[
            VG_RSA_PUBLIC_PRECOMPUTE_ADX_FEATURES,
            VG_RSA_PKCS1_VERIFY_PRECOMPUTED_ADX_FEATURES,
            VG_RSA_PKCS1_SIGN_ADX_FEATURES,
            VG_RSA_GENERATE_ADX_FEATURES,
        ]);
        let ifma = Features::all(&[
            adx,
            VG_RSA_PKCS1_VERIFY_PRECOMPUTED_IFMA_FEATURES,
            VG_RSA_PKCS1_SIGN_IFMA_FEATURES,
        ]);
        [Features(0), adx, ifma]
    };

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(Self::REQUIRES[Backend::Ifma as usize]) {
            Backend::Ifma
        } else if f.contains(Self::REQUIRES[Backend::Adx as usize]) {
            Backend::Adx
        } else {
            Backend::Baseline
        }
    }

    /// The best implementation a CPU with the features `f` can run: on
    /// i686, AArch64, PPC64LE, RISC-V, and ARMv7 where `umaal` is not
    /// detected, the baseline is the only one.
    #[cfg(any(
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "riscv64",
        all(
            target_arch = "arm",
            not(any(
                target_os = "linux",
                target_os = "android",
                target_os = "freebsd",
                target_os = "netbsd",
                target_os = "openbsd"
            ))
        )
    ))]
    pub(crate) fn select(_f: Features) -> Backend {
        Backend::Baseline
    }

    /// The CPU features `select` requires to choose each implementation, by
    /// its discriminant: none, of the only one. (Only the callers' checks
    /// use it, which the builds without `alloc` leave out.)
    #[cfg(any(
        target_arch = "x86",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "riscv64",
        all(
            target_arch = "arm",
            not(any(
                target_os = "linux",
                target_os = "android",
                target_os = "freebsd",
                target_os = "netbsd",
                target_os = "openbsd"
            ))
        )
    ))]
    #[allow(dead_code)]
    pub(crate) const REQUIRES: &[Features] = &[Features(0)];

    /// The CPU features `select` requires to choose each implementation, by
    /// its discriminant.
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
    pub(crate) const REQUIRES: &[Features] = &[
        Features(0),
        Features::all(&[
            VG_RSA_PKCS1_SIGN_UMAAL_FEATURES,
            VG_RSA_PRIME_SEARCH_UMAAL_FEATURES,
        ]),
    ];

    /// The best implementation a CPU with the features `f` can run, on
    /// ARMv7.
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
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(Self::REQUIRES[Backend::Umaal as usize]) {
            Backend::Umaal
        } else {
            Backend::Baseline
        }
    }
}

/// The shortest modulus, in bytes (512 bits).
pub const MIN_MODULUS_LEN: usize = 64;
/// The longest modulus, in bytes (8192 bits).
pub const MAX_MODULUS_LEN: usize = 1024;

/// Why an RSA key was not loaded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The modulus is not an odd number of 512 to 8192 bits, written in
    /// as few bytes as it takes.
    InvalidModulus,
    /// The public exponent is not within BoringSSL's limits: odd, from 3
    /// to `2^33 - 1`.
    InvalidExponent,
    /// The private key's values are too long for its modulus or fail
    /// BoringSSL's `RSA_check_key` (`p q = n`, `d < n`, `d`, `dP` and `dQ`
    /// inverse to `e` modulo `p - 1` and `q - 1`, `qInv` the inverse of `q`
    /// modulo `p`), or (from `(n, e, d)`) its primes were not found.
    InvalidPrivateKey,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidModulus => "invalid RSA modulus",
            Error::InvalidExponent => "invalid RSA public exponent",
            Error::InvalidPrivateKey => "invalid RSA private key",
        })
    }
}

impl core::error::Error for Error {}

/// The words of working space the operations need for an `n_len`-byte
/// modulus (`VG.Spec.Rsa.scratchWords`).
pub(crate) fn scratch_words(n_len: usize) -> usize {
    16 * n_len + 32
}

/// The words of working space the public-key operation and its
/// precomputation need for an `n_len`-byte modulus
/// (`VG.Spec.Rsa.publicScratchWords`).
pub(crate) fn public_scratch_words(n_len: usize) -> usize {
    8 * n_len.div_ceil(8) + 48
}

/// `x` without its leading zero bytes, for the public exponent and the
/// primes, whose lengths are public.
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
/// After OAEP encryption, PSS or PKCS #1 signature verification, retains
/// one wiped working buffer for reuse. Concurrent operations use independent
/// buffers; cloning a key starts with an empty cache, and with the values
/// of `n` if they are computed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicKey {
    pub(crate) n: Vec<u8>,
    pub(crate) e: Vec<u8>,
    pre: Precomputed,
    pub(crate) verify_scratch: VerifyScratch,
}

impl PublicKey {
    /// The key with the modulus `n` and the public exponent `e`. `n` must be
    /// odd, from 512 to 8192 bits long, with no leading zero byte; `e` must be
    /// odd, from 3 to `2^33 - 1` (with any number of leading zero bytes), as
    /// BoringSSL requires.
    pub fn new(n: BigUint<'_>, e: BigUint<'_>) -> Result<Self, Error> {
        Self::from_bytes(n.as_be_bytes(), e.as_be_bytes())
    }

    /// [`new`](Self::new) of `n` and `e`, big-endian: `n` with no leading
    /// zero byte, `e` with any number of them.
    pub(crate) fn from_bytes(n: &[u8], e: &[u8]) -> Result<Self, Error> {
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
    /// `scratch` (at least `public_scratch_words(n_len)` words, left holding only
    /// values of `n`) at the key's first operation.
    pub(crate) fn pre(&self, scratch: &mut [u64]) -> &[u64] {
        self.pre.get(&self.n, scratch)
    }

    /// The length of the modulus in bytes, which is that of the key's
    /// ciphertexts and signatures.
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }
}

mod biguint;
pub use biguint::BigUint;
mod privatekey;
pub use privatekey::PrivateKey;

pub mod keygen;
pub mod oaep;
pub mod pkcs1_enc;
pub mod pkcs1_sig;
pub mod pss;

#[cfg(test)]
pub(crate) mod tests {
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
    use super::VG_RSA_PKCS1_SIGN_UMAAL_FEATURES;
    use super::{
        Backend, BigUint, Error, Features, MAX_MODULUS_LEN, MIN_MODULUS_LEN, PrivateKey, PublicKey,
        Vec, exponent, public_scratch_words, scratch_words, trim,
    };
    #[cfg(target_arch = "x86_64")]
    use super::{
        VG_RSA_PKCS1_SIGN_ADX_FEATURES, VG_RSA_PKCS1_SIGN_IFMA_FEATURES,
        VG_RSA_PKCS1_VERIFY_PRECOMPUTED_ADX_FEATURES,
    };
    use alloc::string::ToString;
    use alloc::vec;

    #[test]
    fn public_scratch_within_scratch() {
        // Over every modulus length the functions accept, the public-key
        // operation's working space is no more than the private-key
        // operation's.
        for n_len in MIN_MODULUS_LEN..=MAX_MODULUS_LEN {
            assert!(public_scratch_words(n_len) <= scratch_words(n_len));
        }
        assert_eq!(public_scratch_words(256), 8 * 32 + 48);
        assert_eq!(public_scratch_words(257), 8 * 33 + 48);
    }

    /// The CRT form `[n, p, q, dP, dQ, qInv]` of a key whose values match
    /// each other for `e = 3`, but whose factors are not prime: `p = 2^(8a) - 1`
    /// (`a` bytes of `0xff`, `3 | p`) and `q = 2^(8a) + 1` (`a + 1` bytes),
    /// `n = 2^(16a) - 1`, `dP = p / 3` (`3 dP = (p - 1) + 1`),
    /// `dQ = (2^(8a + 1) + 1) / 3` (`3 dQ = 2 (q - 1) + 1`) and
    /// `qInv = 2^(8a - 1)` (`q ≡ 2 (mod p)`). With `swap`, `p` and `q` are
    /// the other way round, and still `qInv = 2^(8a - 1)` (`q ≡ -2`). With
    /// [`composite_d`]'s private exponent, every check of
    /// `PrivateKey::from_crt` passes; the private-key operation's result for
    /// most inputs does not pass its check against `e`.
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

    /// The private exponent of `composite(a, swap)`: `d = (2^(8a) - 1)^2 / 3`,
    /// the product of its factor `2^(8a) - 1` and that factor's `dP` (or
    /// `dQ`), which is `3⁻¹` modulo `2^(8a) - 2` and `2^(8a)` (`3 d` is 1
    /// modulo both), and less than `n`.
    pub(crate) fn composite_d(a: usize) -> Vec<u8> {
        mul(&vec![0xff; a], &vec![0x55; a])
    }

    /// `a b`, big-endian, in `a.len() + b.len()` bytes.
    pub(crate) fn mul(a: &[u8], b: &[u8]) -> Vec<u8> {
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

    /// `composite(32, false)` loaded, with [`composite_d`], and its public
    /// key.
    pub(crate) fn composite_key() -> (PrivateKey, PublicKey) {
        let [n, p, q, dp, dq, qinv] = composite(32, false);
        (
            PrivateKey::from_crt_bytes(&n, &[3], &composite_d(32), &p, &q, &dp, &dq, &qinv)
                .unwrap(),
            PublicKey::from_bytes(&n, &[3]).unwrap(),
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

    #[test]
    fn backends() {
        assert_eq!(Backend::select(Features(0)), Backend::Baseline);
    }

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
    #[test]
    fn backends_arm() {
        assert_eq!(
            Backend::select(VG_RSA_PKCS1_SIGN_UMAAL_FEATURES),
            Backend::Umaal
        );
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn backends_x86_64() {
        assert_eq!(
            Backend::select(Features(verified_garbage_cpu::feature::BMI2)),
            Backend::Baseline
        );
        // `VG_RSA_PKCS1_SIGN_ADX_FEATURES` names AVX2 too.
        assert_eq!(
            Backend::select(VG_RSA_PKCS1_VERIFY_PRECOMPUTED_ADX_FEATURES),
            Backend::Baseline
        );
        assert_eq!(
            Backend::select(Features::all(&[
                VG_RSA_PKCS1_VERIFY_PRECOMPUTED_ADX_FEATURES,
                Features(verified_garbage_cpu::feature::AVX | verified_garbage_cpu::feature::AVX2),
            ])),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(VG_RSA_PKCS1_SIGN_ADX_FEATURES),
            Backend::Adx
        );
        assert_eq!(
            Backend::select(Features::all(&[
                VG_RSA_PKCS1_SIGN_IFMA_FEATURES,
                Features(verified_garbage_cpu::feature::AVX2),
            ])),
            Backend::Ifma
        );
        assert_eq!(
            Backend::select(Features(
                verified_garbage_cpu::feature::AVX
                    | verified_garbage_cpu::feature::AVX512F
                    | verified_garbage_cpu::feature::AVX512IFMA
                    | verified_garbage_cpu::feature::AVX512VL
            )),
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

    #[test]
    fn invalid() {
        let n = modulus(64);
        assert_eq!(PublicKey::from_bytes(&n, &[3]).unwrap().modulus_len(), 64);
        let mut half = n.clone();
        half[0] = 0x7f;
        let mut zero = modulus(65);
        zero[0] = 0;
        let mut even = n.clone();
        *even.last_mut().unwrap() ^= 1;
        let mut ok = modulus(65);
        ok[0] = 1;
        assert!(PublicKey::from_bytes(&ok, &[3]).is_ok());
        let bad: [&[u8]; 6] = [&modulus(63), &half, &zero, &even, &modulus(1025), &[]];
        for bad in bad {
            assert_eq!(PublicKey::from_bytes(bad, &[3]), Err(Error::InvalidModulus));
        }
        for e in [&[][..], &[1], &[2], &[1; 64]] {
            assert_eq!(PublicKey::from_bytes(&n, e), Err(Error::InvalidExponent));
        }
        let key = PublicKey::from_bytes(&n, &[3]).unwrap();
        // `new` is `from_bytes` of the integers' bytes, as they are.
        let big = BigUint::from_be_bytes;
        assert_eq!(PublicKey::new(big(&n), big(&[0, 3])), Ok(key));
        assert_eq!(
            PublicKey::new(big(&zero), big(&[3])),
            Err(Error::InvalidModulus)
        );
        assert_eq!(
            PublicKey::new(big(&n), big(&[2])),
            Err(Error::InvalidExponent)
        );
    }

    #[test]
    fn errors_display() {
        for e in [
            Error::InvalidModulus,
            Error::InvalidExponent,
            Error::InvalidPrivateKey,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
