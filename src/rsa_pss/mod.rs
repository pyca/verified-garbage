//! RSASSA-PSS (RFC 8017 §8.1) of a hash value, with the keys of
//! [`crate::rsa`], with MGF1 over the same hash function.
//!
//! [`sign`] is the verified `vg_rsa_pss_<H>_mgf1_<H>_sign` (contract
//! `VG.Spec.RsaPss.signContract`): EMSA-PSS's encoding of the hash value
//! with a salt of random bytes (RFC 8017 §9.1.1), then the private-key
//! operation of `vg_rsa_private_checked`, which releases the signature only if
//! it passes the check against the public exponent, as BoringSSL's
//! `RSA_sign_pss_mgf1` does. Its timing may depend on the public key, the hash
//! function and the lengths, but not on the hash value, the salt or the
//! private key.
//!
//! [`verify`] is the verified `vg_rsa_pss_<H>_mgf1_<H>_verify` (contract
//! `VG.Spec.RsaPss.verifyContract`): RSAVP1, then EMSA-PSS-VERIFY (RFC 8017
//! §9.1.2), expecting a salt of a given length or of any length
//! ([`SaltLength::Any`], BoringSSL's `RSA_PSS_SALTLEN_AUTO`), as BoringSSL's
//! `RSA_verify_pss_mgf1` does. Its timing may depend on the public key, the
//! hash function, the lengths and the expected salt length, but not on the
//! signature, the hash value or anything computed from them but the result.
//!
//! Each function runs the implementation of the hash function's compression
//! function that the CPU is best at (as [`crate::hashes`] does), and for
//! signing, the private-key operation's (see [`crate::rsa`]): the verified
//! functions are emitted for each pair, all with the same contracts.
//!
//! MGF1 over another hash function than the hash value's is not supported.
//! This module only checks the lengths, draws the salt and allocates the
//! memory the functions work in.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

mod md5;
mod sha1;
mod sha224;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::cpu::detected;
use crate::rsa::{PrivateKey, PublicKey};
use crate::zeroize::zeroize;

/// A hash function RSASSA-PSS can use (`VG.Spec.Mgf1.Hash`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hash {
    /// MD5.
    Md5,
    /// SHA-1.
    Sha1,
    /// SHA-224.
    Sha224,
    /// SHA-256.
    Sha256,
    /// SHA-384.
    Sha384,
    /// SHA-512.
    Sha512,
    /// SHA-512/224.
    Sha512_224,
    /// SHA-512/256.
    Sha512_256,
}

impl Hash {
    /// The length of the hash function's values, in bytes
    /// (`VG.Spec.Mgf1.Hash.len`).
    pub fn digest_len(self) -> usize {
        match self {
            Hash::Md5 => 16,
            Hash::Sha1 => 20,
            Hash::Sha224 | Hash::Sha512_224 => 28,
            Hash::Sha256 | Hash::Sha512_256 => 32,
            Hash::Sha384 => 48,
            Hash::Sha512 => 64,
        }
    }
}

/// The salt length a signature must have to verify.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SaltLength {
    /// Exactly this many bytes.
    Len(usize),
    /// Any length the encoding's padding gives (BoringSSL's
    /// `RSA_PSS_SALTLEN_AUTO`).
    Any,
}

/// Why a signature was not made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The hash value is not as long as the hash function's values.
    InvalidDigestLength,
    /// MGF1's hash function is not the hash value's.
    UnsupportedMgf1Hash,
    /// The encoding does not fit the modulus: the hash value, the salt and
    /// two bytes are longer than `⌈(bits of n - 1) / 8⌉`.
    SaltTooLong,
    /// The signature failed the private-key operation's check against the
    /// public exponent (see [`crate::rsa::Error::Fault`]) and is not
    /// released.
    Fault,
    /// The random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidDigestLength => "hash value length is not the hash function's",
            Error::UnsupportedMgf1Hash => "MGF1 over another hash function is not supported",
            Error::SaltTooLong => "RSA modulus is too short for the hash value and the salt",
            Error::Fault => "RSA signature failed its check against the public exponent",
            Error::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// `vg_rsa_pss_<H>_mgf1_<H>_sign`'s signature, for `N`-byte hash values.
type SignFn<const N: usize> = unsafe extern "sysv64" fn(
    *mut u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const u8,
    usize,
    *const [u8; N],
    *const u8,
    usize,
    *mut u64,
    usize,
) -> u32;

/// `vg_rsa_pss_<H>_mgf1_<H>_verify`'s signature, for `N`-byte hash values.
type VerifyFn<const N: usize> = unsafe extern "sysv64" fn(
    *const u8,
    usize,
    *const u8,
    usize,
    *const [u8; N],
    *const u8,
    usize,
    usize,
    u32,
    *mut u64,
    usize,
) -> u32;

/// `$body` with `$fns` the verified functions of the hash function `$hash`
/// (`(sign, verify)`) for the implementations this CPU runs best.
macro_rules! with_functions {
    ($hash:expr, |$fns:ident| $body:expr) => {{
        let f = detected();
        match $hash {
            Hash::Md5 => {
                let $fns = md5::functions(f);
                $body
            }
            Hash::Sha1 => {
                let $fns = sha1::functions(f);
                $body
            }
            Hash::Sha224 => {
                let $fns = sha224::functions(f);
                $body
            }
            Hash::Sha256 => {
                let $fns = sha256::functions(f);
                $body
            }
            Hash::Sha384 => {
                let $fns = sha384::functions(f);
                $body
            }
            Hash::Sha512 => {
                let $fns = sha512::functions(f);
                $body
            }
            Hash::Sha512_224 => {
                let $fns = sha512_224::functions(f);
                $body
            }
            Hash::Sha512_256 => {
                let $fns = sha512_256::functions(f);
                $body
            }
        }
    }};
}

/// The words of working space the functions need for an `n_len`-byte
/// modulus (`VG.Spec.RsaPss.scratchWords`).
fn scratch_words(n_len: usize) -> usize {
    crate::rsa::scratch_words(n_len) + 1024
}

/// RSASSA-PSS-SIGN (RFC 8017 §8.1.1) of the hash value `digest` of the hash
/// function `hash`, with MGF1 over `mgf1_hash` (which must be `hash`) and a
/// salt of `salt_len` random bytes: the signature, as long as the modulus.
pub fn sign(
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_len: usize,
) -> Result<Vec<u8>, Error> {
    if mgf1_hash != hash {
        return Err(Error::UnsupportedMgf1Hash);
    }
    if digest.len() != hash.digest_len() {
        return Err(Error::InvalidDigestLength);
    }
    if salt_len > key.n.len() {
        return Err(Error::SaltTooLong);
    }
    let mut salt = vec![0u8; salt_len];
    getrandom::fill(&mut salt).map_err(|_| Error::Randomness)?;
    let r = sign_with(key, digest, hash, &salt);
    zeroize(&mut salt);
    r
}

/// The signature of `digest` with the salt `salt`.
fn sign_with(key: &PrivateKey, digest: &[u8], hash: Hash, salt: &[u8]) -> Result<Vec<u8>, Error> {
    let k = key.n.len();
    let mut out = vec![0; k];
    let mut scratch = vec![0u64; scratch_words(k)];
    let r = with_functions!(hash, |fns| call_sign(
        fns.0,
        &mut out,
        key,
        digest,
        salt,
        &mut scratch
    ));
    // The working space holds the private key, the encoding and its powers.
    zeroize(&mut scratch);
    // `PrivateKey::from_crt` checked the key, so a refusal means the encoding
    // does not fit.
    match r {
        1 => Ok(out),
        2 => Err(Error::Fault),
        _ => Err(Error::SaltTooLong),
    }
}

/// RSASSA-PSS-VERIFY (RFC 8017 §8.1.2): whether `signature` is a valid
/// signature of the hash value `digest` of the hash function `hash`, with
/// MGF1 over `mgf1_hash` (false unless it is `hash`) and a salt of
/// `salt_length`.
pub fn verify(
    key: &PublicKey,
    signature: &[u8],
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt_length: SaltLength,
) -> bool {
    let k = key.n.len();
    if mgf1_hash != hash || digest.len() != hash.digest_len() || signature.len() != k {
        return false;
    }
    let (salt_len, any) = match salt_length {
        SaltLength::Len(l) => (l, 0),
        SaltLength::Any => (0, 1),
    };
    let mut scratch = vec![0u64; scratch_words(k)];
    let r = with_functions!(hash, |fns| call_verify(
        fns.1,
        key,
        signature,
        digest,
        salt_len,
        any,
        &mut scratch
    ));
    // The working space holds the encoding, which is as secret as the
    // signature's validity.
    zeroize(&mut scratch);
    r == 1
}

/// `f`, a `vg_rsa_pss_<H>_mgf1_<H>_sign` that this CPU can run, on the
/// key, the hash value (as long as `H`'s values), the salt, the
/// modulus-long `out` and the working space.
fn call_sign<const N: usize>(
    f: SignFn<N>,
    out: &mut [u8],
    key: &PrivateKey,
    digest: &[u8],
    salt: &[u8],
    scratch: &mut [u64],
) -> u32 {
    let digest: &[u8; N] = digest.try_into().unwrap();
    assert!(out.len() == key.n.len() && scratch.len() == scratch_words(key.n.len()));
    // SAFETY: each pointer is valid for its length (`out` for writes,
    // `scratch` too, `digest` for the hash function's values), and none
    // overlaps another or wraps around, as they are distinct Rust
    // allocations; `PrivateKey::from_crt` gives `64 ≤ n_len ≤ 1024`,
    // `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`, `1 ≤ q_len < n_len`,
    // `dp_len = qinv_len = p_len` and `dq_len = q_len`; `out_len = n_len` and
    // `scratch_len = 16 n_len + 1024`; and the CPU has the features of the
    // function `functions` chose.
    unsafe {
        f(
            out.as_mut_ptr(),
            out.len(),
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            key.p.as_ptr(),
            key.p.len(),
            key.q.as_ptr(),
            key.q.len(),
            key.dp.as_ptr(),
            key.dp.len(),
            key.dq.as_ptr(),
            key.dq.len(),
            key.qinv.as_ptr(),
            key.qinv.len(),
            digest,
            salt.as_ptr(),
            salt.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    }
}

/// `f`, a `vg_rsa_pss_<H>_mgf1_<H>_verify` that this CPU can run, on the
/// key, the modulus-long signature, the hash value (as long as `H`'s
/// values), the salt length and whether any is allowed, and the working
/// space.
fn call_verify<const N: usize>(
    f: VerifyFn<N>,
    key: &PublicKey,
    signature: &[u8],
    digest: &[u8],
    salt_len: usize,
    any: u32,
    scratch: &mut [u64],
) -> u32 {
    let digest: &[u8; N] = digest.try_into().unwrap();
    assert!(signature.len() == key.n.len() && scratch.len() == scratch_words(key.n.len()));
    // SAFETY: each pointer is valid for its length (`scratch` for writes,
    // `digest` for the hash function's values), and none overlaps another or
    // wraps around, as they are distinct Rust allocations; `PublicKey::new`
    // gives `64 ≤ n_len ≤ 1024` and `1 ≤ e_len ≤ 5 ≤ n_len`; `sig_len = n_len`
    // and `scratch_len = 16 n_len + 1024`; and the CPU has the features of
    // the function `functions` chose.
    unsafe {
        f(
            key.n.as_ptr(),
            key.n.len(),
            key.e.as_ptr(),
            key.e.len(),
            digest,
            signature.as_ptr(),
            signature.len(),
            salt_len,
            any,
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    }
}

/// The verified functions of one hash function: for each implementation of
/// its compression function (a variant of its streaming backend), `verify`
/// and `sign` calling each implementation of the private-key operation
/// (`crate::rsa::Backend`), with the CPU features each needs.
macro_rules! pss_hash {
    (
        $n:literal, $backend:ident {
            $(
                $(#[$attr:meta])* $variant:ident => {
                    verify: $verify:path [$($vreq:path),*],
                    sign: $sign:path [$($sreq:path),*],
                    adx: $adx:path [$($areq:path),*],
                    ifma: $ifma:path [$($ireq:path),*] $(,)?
                }
            ),* $(,)?
        }
    ) => {
        /// The length of the hash function's values.
        const N: usize = $n;

        // The features are checked by the test below.
        $(
            $(#[$attr])*
            const _: &[$crate::cpu::Features] = &[$($vreq,)* $($sreq,)* $($areq,)* $($ireq,)*];
        )*

        /// The functions for the implementations that a CPU with the
        /// features `f` runs best.
        pub(super) fn functions(f: $crate::cpu::Features) -> (super::SignFn<N>, super::VerifyFn<N>) {
            let crt = $crate::rsa::Backend::select(f);
            match $backend::select(f) {
                $(
                    $(#[$attr])*
                    $backend::$variant => (
                        match crt {
                            $crate::rsa::Backend::Baseline => $sign,
                            $crate::rsa::Backend::Adx => $adx,
                            $crate::rsa::Backend::Ifma => $ifma,
                        },
                        $verify,
                    ),
                )*
            }
        }

        #[cfg(test)]
        mod tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each function needs no CPU feature that the implementations
            /// it calls are not selected for: on every set of features.
            #[test]
            fn backend_features() {
                use $crate::cpu::Features;
                for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                    let f = Features(bits);
                    let crt = $crate::rsa::Backend::select(f);
                    $(
                        $(#[$attr])*
                        if $backend::select(f) == $backend::$variant {
                            assert!(f.contains(Features::all(&[$($vreq),*])));
                            let s: Features = match crt {
                                $crate::rsa::Backend::Baseline => Features::all(&[$($sreq),*]),
                                $crate::rsa::Backend::Adx => Features::all(&[$($areq),*]),
                                $crate::rsa::Backend::Ifma => Features::all(&[$($ireq),*]),
                            };
                            assert!(f.contains(s));
                        }
                    )*
                }
            }
        }
    };
}

use pss_hash;

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;

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

    /// A 64-byte key `p q = n` of two odd numbers with `e = 3`,
    /// `dP = dQ = 1` and `qInv = 0`, which `PrivateKey::from_crt` accepts
    /// (its result for 0 passes the check) but whose result for an encoding
    /// fails the check.
    fn key() -> (PrivateKey, PublicKey) {
        let p = vec![0xff; 32];
        let mut q = vec![0xff; 32];
        q[31] = 0xfd;
        let n = mul(&p, &q);
        let private = PrivateKey::from_crt(&n, &[3], &[1], &p, &q, &[1], &[1], &[0]).unwrap();
        (private, PublicKey::new(&n, &[3]).unwrap())
    }

    /// With `key`'s 64-byte modulus (`emLen = 64`): MGF1 over another hash
    /// function, a hash value of the wrong length, salts longer than the
    /// modulus and than the encoding has room for, and a signature that
    /// fails the check.
    #[test]
    fn sign_refused() {
        let (private, _) = key();
        let s = |d: &[u8], h, g, l| sign(&private, d, h, g, l);
        assert_eq!(
            s(&[0; 20], Hash::Sha1, Hash::Sha256, 0),
            Err(Error::UnsupportedMgf1Hash)
        );
        assert_eq!(
            s(&[0; 19], Hash::Sha1, Hash::Sha1, 0),
            Err(Error::InvalidDigestLength)
        );
        assert_eq!(
            s(&[0; 20], Hash::Sha1, Hash::Sha1, 65),
            Err(Error::SaltTooLong)
        );
        assert_eq!(
            s(&[0; 20], Hash::Sha1, Hash::Sha1, 43),
            Err(Error::SaltTooLong)
        );
        assert_eq!(s(&[0; 20], Hash::Sha1, Hash::Sha1, 0), Err(Error::Fault));
    }

    /// Arguments `verify` refuses before calling the verified function.
    #[test]
    fn verify_refused() {
        let (_, public) = key();
        let sig = [1; 64];
        let v = |s: &[u8], d: &[u8], h, g| verify(&public, s, d, h, g, SaltLength::Any);
        assert!(!v(&sig, &[0; 20], Hash::Sha1, Hash::Sha256));
        assert!(!v(&sig, &[0; 19], Hash::Sha1, Hash::Sha1));
        assert!(!v(&sig[..63], &[0; 20], Hash::Sha1, Hash::Sha1));
        assert!(!v(&sig, &[0; 20], Hash::Sha1, Hash::Sha1));
    }

    #[test]
    fn errors() {
        for e in [
            Error::InvalidDigestLength,
            Error::UnsupportedMgf1Hash,
            Error::SaltTooLong,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
