//! RSASSA-PKCS1-v1_5 (RFC 8017 §8.2) of a hash value, with the keys of
//! [`crate::rsa`].
//!
//! [`sign`] is the verified `vg_rsa_pkcs1_sign` (contract
//! `VG.Spec.RsaPkcs1Sig.signContract`): EMSA-PKCS1-v1_5's encoding of the hash
//! value (RFC 8017 §9.2) to the modulus' length, then the private-key
//! operation of `vg_rsa_private_checked`, which releases the signature only if
//! it passes the check against the public exponent, as BoringSSL's `RSA_sign`
//! does. Its timing may depend on the public key, the hash function and the
//! lengths, but not on the hash value or the private key. On a CPU with BMI2
//! and ADX, `vg_rsa_pkcs1_sign_adx` does the same with the faster Montgomery
//! multiplication; on one with AVX512_IFMA and AVX512VL too,
//! `vg_rsa_pkcs1_sign_ifma` (see [`crate::rsa`]).
//!
//! [`verify`] is the verified `vg_rsa_pkcs1_verify_precomputed` (contract
//! `VG.Spec.RsaPkcs1Sig.verifyPrecomputedContract`), which accepts a signature exactly
//! when `s^e mod n` is the encoding of the hash value, as BoringSSL's
//! `RSA_verify` does. It reuses the public key's precomputed modulus values
//! and selects ADX multiplication when available. [`recover`] is `vg_rsa_pkcs1_recover` (contract
//! `VG.Spec.RsaPkcs1Sig.recoverContract`), which returns the hash value a
//! signature signs, as BoringSSL's `EVP_PKEY_verify_recover` does. Everything
//! they read is public and their timing may depend on it.
//!
//! This module only checks the lengths and allocates the memory the
//! functions work in.

#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::arch::rsa_pkcs1_sig::{
    vg_rsa_pkcs1_recover, vg_rsa_pkcs1_sign, vg_rsa_pkcs1_verify_precomputed,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pkcs1_sig::{
    vg_rsa_pkcs1_sign_adx, vg_rsa_pkcs1_sign_ifma, vg_rsa_pkcs1_verify_precomputed_adx,
};
use crate::cpu::detected;
use crate::rsa::{Backend, PrivateKey, PublicKey, scratch_words};

/// The hash function of a hash value (`VG.Spec.RsaPkcs1Sig.Hash`), each with
/// the number the verified functions take (`VG.Spec.RsaPkcs1Sig.Hash.ofId`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Hash {
    /// MD5.
    Md5 = 0,
    /// SHA-1.
    Sha1 = 1,
    /// SHA-224.
    Sha224 = 2,
    /// SHA-256.
    Sha256 = 3,
    /// SHA-384.
    Sha384 = 4,
    /// SHA-512.
    Sha512 = 5,
    /// SHA-512/224.
    Sha512_224 = 6,
    /// SHA-512/256.
    Sha512_256 = 7,
    /// SHA3-224.
    Sha3_224 = 8,
    /// SHA3-256.
    Sha3_256 = 9,
    /// SHA3-384.
    Sha3_384 = 10,
    /// SHA3-512.
    Sha3_512 = 11,
}

impl Hash {
    /// The length of the hash function's values, in bytes
    /// (`VG.Spec.RsaPkcs1Sig.Hash.len`).
    pub fn digest_len(self) -> usize {
        match self {
            Hash::Md5 => 16,
            Hash::Sha1 => 20,
            Hash::Sha224 | Hash::Sha512_224 | Hash::Sha3_224 => 28,
            Hash::Sha256 | Hash::Sha512_256 | Hash::Sha3_256 => 32,
            Hash::Sha384 | Hash::Sha3_384 => 48,
            Hash::Sha512 | Hash::Sha3_512 => 64,
        }
    }
}

/// Why a signature was not made or not recovered.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The hash value is not as long as the hash function's values.
    InvalidDigestLength,
    /// The modulus is shorter than the encoding: 11 bytes more than the
    /// `DigestInfo` of the hash value.
    ModulusTooShort,
    /// The signature failed the private-key operation's check against the
    /// public exponent (see [`crate::rsa::Error::Fault`]) and is not
    /// released.
    Fault,
    /// The signature is not a valid signature of a hash value of the hash
    /// function with the key.
    InvalidSignature,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidDigestLength => "hash value length is not the hash function's",
            Error::ModulusTooShort => "RSA modulus is too short for the hash function",
            Error::Fault => "RSA signature failed its check against the public exponent",
            Error::InvalidSignature => "invalid RSA PKCS #1 v1.5 signature",
        })
    }
}

impl core::error::Error for Error {}

/// RSASSA-PKCS1-V1_5-SIGN (RFC 8017 §8.2.1) of the hash value `digest` of
/// the hash function `hash`: the signature, as long as the modulus.
pub fn sign(key: &PrivateKey, digest: &[u8], hash: Hash) -> Result<Vec<u8>, Error> {
    if digest.len() != hash.digest_len() {
        return Err(Error::InvalidDigestLength);
    }
    let k = key.n.len();
    let mut out = vec![0; k];
    let mut scratch = vec![0u64; scratch_words(k)];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_pkcs1_sign,
        // `select` chose them because the CPU has the features they need.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx => vg_rsa_pkcs1_sign_adx,
        #[cfg(target_arch = "x86_64")]
        Backend::Ifma => vg_rsa_pkcs1_sign_ifma,
    };
    // SAFETY: each pointer is valid for its length (`out` for writes,
    // `scratch` too), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `PrivateKey::from_crt` gives
    // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len` and `dq_len = q_len`;
    // `out_len = n_len` and `scratch_len = 16 n_len`; and the CPU has the
    // features of the function `select` chose.
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            hash as u32,
            digest.as_ptr(),
            digest.len(),
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
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    // The working space holds the private key and powers of the encoding.
    crate::zeroize::zeroize(&mut scratch);
    // `PrivateKey::from_crt` checked the key and the length of `digest` is
    // checked above, so a refusal means the encoding does not fit.
    match r {
        1 => Ok(out),
        2 => Err(Error::Fault),
        _ => Err(Error::ModulusTooShort),
    }
}

/// RSASSA-PKCS1-V1_5-VERIFY (RFC 8017 §8.2.2): whether `signature` is a
/// valid signature of the hash value `digest` of the hash function `hash`.
pub fn verify(key: &PublicKey, signature: &[u8], digest: &[u8], hash: Hash) -> bool {
    let k = key.n.len();
    let mut scratch = vec![0u64; scratch_words(k)];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_pkcs1_verify_precomputed,
        #[cfg(target_arch = "x86_64")]
        Backend::Adx | Backend::Ifma => vg_rsa_pkcs1_verify_precomputed_adx,
    };
    // SAFETY: each pointer is valid for its length (`scratch` for writes),
    // and none overlaps another or wraps around, as they are distinct Rust
    // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024` and
    // `1 ≤ e_len ≤ 5 ≤ n_len`; `scratch_len = 16 n_len`; and `key.pre`
    // holds the verified precomputation for `key.n`, with `2 * ceil(n_len / 8)`
    // words. The CPU supports the selected function's features.
    let r = unsafe {
        f(
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            hash as u32,
            digest.as_ptr(),
            digest.len(),
            signature.as_ptr(),
            signature.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            key.pre.as_ptr(),
            key.pre.len(),
        )
    };
    // The working space holds only public values.
    r == 1
}

/// The hash value of the hash function `hash` that `signature` signs with
/// the key, if it is a valid signature of one.
pub fn recover(key: &PublicKey, signature: &[u8], hash: Hash) -> Result<Vec<u8>, Error> {
    let k = key.n.len();
    let mut out = vec![0; hash.digest_len()];
    let mut scratch = vec![0u64; scratch_words(k)];
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024`
    // and `1 ≤ e_len ≤ 5 ≤ n_len`; `hash` is in `0..=11` and `out_len` is the
    // length of its values; and `scratch_len = 16 n_len`.
    let r = unsafe {
        vg_rsa_pkcs1_recover(
            out.as_mut_ptr(),
            out.len(),
            key.n.as_ptr(),
            k,
            key.e.as_ptr(),
            key.e.len(),
            hash as u32,
            signature.as_ptr(),
            signature.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    // The working space holds only public values.
    if r == 1 {
        Ok(out)
    } else {
        Err(Error::InvalidSignature)
    }
}

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

    const HASHES: [Hash; 12] = [
        Hash::Md5,
        Hash::Sha1,
        Hash::Sha224,
        Hash::Sha256,
        Hash::Sha384,
        Hash::Sha512,
        Hash::Sha512_224,
        Hash::Sha512_256,
        Hash::Sha3_224,
        Hash::Sha3_256,
        Hash::Sha3_384,
        Hash::Sha3_512,
    ];

    #[test]
    fn hashes() {
        let lens = [16, 20, 28, 32, 48, 64, 28, 32, 28, 32, 48, 64];
        for (i, (h, len)) in HASHES.iter().zip(lens).enumerate() {
            assert_eq!(*h as usize, i);
            assert_eq!(h.digest_len(), len);
        }
    }

    /// With `key`'s 64-byte modulus: a hash value of the wrong length, an
    /// encoding longer than the modulus (SHA-512's `DigestInfo` is 83
    /// bytes), and a signature that fails the check.
    #[test]
    fn sign_refused() {
        let (private, public) = key();
        assert_eq!(
            sign(&private, &[0; 31], Hash::Sha256),
            Err(Error::InvalidDigestLength)
        );
        assert_eq!(
            sign(&private, &[0; 64], Hash::Sha512),
            Err(Error::ModulusTooShort)
        );
        assert_eq!(sign(&private, &[0; 20], Hash::Sha1), Err(Error::Fault));
        // Nothing is a valid signature of the zero hash value with this key
        // but its encoding's cube root, which is not 0 or 1.
        for s in [vec![0; 64], {
            let mut one = vec![0; 64];
            one[63] = 1;
            one
        }] {
            assert!(!verify(&public, &s, &[0; 20], Hash::Sha1));
            assert_eq!(
                recover(&public, &s, Hash::Sha1),
                Err(Error::InvalidSignature)
            );
        }
        assert!(!verify(&public, &[], &[0; 20], Hash::Sha1));
    }

    #[test]
    fn errors() {
        for e in [
            Error::InvalidDigestLength,
            Error::ModulusTooShort,
            Error::Fault,
            Error::InvalidSignature,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
