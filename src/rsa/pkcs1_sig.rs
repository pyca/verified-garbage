//! RSASSA-PKCS1-v1_5 (RFC 8017 §8.2) of a hash value, as methods of the keys of
//! [`crate::rsa`].
//!
//! [`PrivateKey::sign_pkcs1v15`] releases a signature only if it verifies with
//! the public exponent, and its timing may depend on the public key, the hash
//! function and the lengths, but not on the hash value or the private key.
//! [`PublicKey::verify_pkcs1v15`] and [`PublicKey::recover_pkcs1v15`] (which
//! returns the hash value a signature signs, as BoringSSL's
//! `EVP_PKEY_verify_recover` does) read only public values, and their timing
//! may depend on them.

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

use crate::arch::rsa_pkcs1_sig::{
    vg_rsa_pkcs1_recover_precomputed, vg_rsa_pkcs1_sign, vg_rsa_pkcs1_verify_precomputed,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa_pkcs1_sig::{
    vg_rsa_pkcs1_recover_precomputed_adx, vg_rsa_pkcs1_recover_precomputed_ifma,
    vg_rsa_pkcs1_sign_adx, vg_rsa_pkcs1_sign_ifma, vg_rsa_pkcs1_verify_precomputed_adx,
    vg_rsa_pkcs1_verify_precomputed_ifma,
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
use crate::arch::rsa_pkcs1_sig::{
    vg_rsa_pkcs1_recover_precomputed_umaal, vg_rsa_pkcs1_sign_umaal,
    vg_rsa_pkcs1_verify_precomputed_umaal,
};
use crate::cpu::detected;
use crate::error::InvalidSignature;
use crate::rsa::{Backend, PrivateKey, PublicKey, public_scratch_words, scratch_words};

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

/// Why a signature was not made.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The hash value is not as long as the hash function's values.
    InvalidDigestLength,
    /// The modulus is shorter than the encoding: 11 bytes more than the
    /// `DigestInfo` of the hash value.
    ModulusTooShort,
    /// The signature failed the private-key operation's check against the
    /// public exponent (a factor of the key is not prime, or the computation
    /// was faulted) and is not released.
    Fault,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidDigestLength => "hash value length is not the hash function's",
            Error::ModulusTooShort => "RSA modulus is too short for the hash function",
            Error::Fault => "RSA signature failed its check against the public exponent",
        })
    }
}

impl core::error::Error for Error {}

impl PrivateKey {
    /// RSASSA-PKCS1-V1_5-SIGN (RFC 8017 §8.2.1) of the hash value `digest` of
    /// the hash function `hash`: the signature, as long as the modulus.
    pub fn sign_pkcs1v15(&self, digest: &[u8], hash: Hash) -> Result<Vec<u8>, Error> {
        crate::dit::enter!(dit);
        if digest.len() != hash.digest_len() {
            return Err(Error::InvalidDigestLength);
        }
        let k = self.n.len();
        let mut out = vec![0; k];
        let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_pkcs1_sign,
            // `select` chose them because the CPU has the features they need.
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_rsa_pkcs1_sign_adx,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_rsa_pkcs1_sign_ifma,
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
            Backend::Umaal => vg_rsa_pkcs1_sign_umaal,
        };
        // SAFETY: each pointer is valid for its length (`out` for writes,
        // `scratch` too), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; `PrivateKey::from_crt` gives
        // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
        // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len` and `dq_len = q_len`;
        // `out_len = n_len` and `scratch_len = 16 n_len + 32`; and the CPU has the
        // features of the function `select` chose.
        let r = unsafe {
            f(
                dit,
                out.as_mut_ptr(),
                k,
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                hash as u32,
                digest.as_ptr(),
                digest.len(),
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
        // `PrivateKey::from_crt` checked the key and the length of `digest` is
        // checked above, so a refusal means the encoding does not fit.
        match r {
            1 => Ok(out),
            2 => Err(Error::Fault),
            _ => Err(Error::ModulusTooShort),
        }
    }
}

impl PublicKey {
    /// RSASSA-PKCS1-V1_5-VERIFY (RFC 8017 §8.2.2): checks that `signature`
    /// is a valid signature of the hash value `digest` of the hash function
    /// `hash`.
    ///
    /// Reuses the public key's verification buffer, which holds only public
    /// values and is not wiped.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if it is not.
    pub fn verify_pkcs1v15(
        &self,
        signature: &[u8],
        digest: &[u8],
        hash: Hash,
    ) -> Result<(), InvalidSignature> {
        let dit = crate::dit::public(crate::dit::Why::Verify);
        let k = self.n.len();
        let mut scratch = self.verify_scratch.take(public_scratch_words(k), false);
        let pre = self.pre(dit, &mut scratch);
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_pkcs1_verify_precomputed,
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_rsa_pkcs1_verify_precomputed_adx,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_rsa_pkcs1_verify_precomputed_ifma,
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
            Backend::Umaal => vg_rsa_pkcs1_verify_precomputed_umaal,
        };
        // SAFETY: each pointer is valid for its length (`scratch` for writes),
        // and none overlaps another or wraps around, as they are distinct Rust
        // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024` and
        // `1 ≤ e_len ≤ 5 ≤ n_len`; `scratch_len = 8 ⌈n_len / 8⌉ + 48`; and `pre`
        // holds the verified precomputation for `self.n`, with `2 * ceil(n_len / 8)`
        // words. The CPU supports the selected function's features.
        let r = unsafe {
            f(
                dit,
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                hash as u32,
                digest.as_ptr(),
                digest.len(),
                signature.as_ptr(),
                signature.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
                pre.as_ptr(),
                pre.len(),
            )
        };
        // ScratchLease wipes the working space before returning it to the self.
        if r == 1 {
            Ok(())
        } else {
            Err(InvalidSignature)
        }
    }

    /// The hash value of the hash function `hash` that `signature` signs with
    /// the key.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if `signature` is not a valid signature of a hash
    /// value of `hash` with the key.
    pub fn recover_pkcs1v15(
        &self,
        signature: &[u8],
        hash: Hash,
    ) -> Result<Vec<u8>, InvalidSignature> {
        crate::dit::enter!(dit);
        let k = self.n.len();
        let mut out = vec![0; hash.digest_len()];
        let mut scratch = vec![0u64; public_scratch_words(k)];
        let pre = self.pre(dit, &mut scratch);
        let f = match Backend::select(detected()) {
            Backend::Baseline => vg_rsa_pkcs1_recover_precomputed,
            // `select` chose it because the CPU has the features it needs.
            #[cfg(target_arch = "x86_64")]
            Backend::Adx => vg_rsa_pkcs1_recover_precomputed_adx,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_rsa_pkcs1_recover_precomputed_ifma,
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
            Backend::Umaal => vg_rsa_pkcs1_recover_precomputed_umaal,
        };
        // SAFETY: each pointer is valid for its length (`out` and `scratch` for
        // writes), and none overlaps another or wraps around, as they are
        // distinct Rust allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024`
        // and `1 ≤ e_len ≤ 5 ≤ n_len`; `hash` is in `0..=11` and `out_len` is the
        // length of its values; `scratch_len = 8 ⌈n_len / 8⌉ + 48`; `pre` holds the
        // verified precomputation for `self.n`, with `2 * ceil(n_len / 8)` words;
        // and the CPU supports the selected function's features.
        let r = unsafe {
            f(
                dit,
                out.as_mut_ptr(),
                out.len(),
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                hash as u32,
                signature.as_ptr(),
                signature.len(),
                scratch.as_mut_ptr(),
                scratch.len(),
                pre.as_ptr(),
                pre.len(),
            )
        };
        // The working space holds only public values.
        if r == 1 {
            Ok(out)
        } else {
            Err(InvalidSignature)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, Hash, InvalidSignature, vec};
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

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

    /// With `composite_key`'s 64-byte modulus: a hash value of the wrong length, an
    /// encoding longer than the modulus (SHA-512's `DigestInfo` is 83
    /// bytes), and a signature that fails the check.
    #[test]
    fn sign_refused() {
        let (private, public) = composite_key();
        assert_eq!(
            private.sign_pkcs1v15(&[0; 31], Hash::Sha256),
            Err(Error::InvalidDigestLength)
        );
        assert_eq!(
            private.sign_pkcs1v15(&[0; 64], Hash::Sha512),
            Err(Error::ModulusTooShort)
        );
        assert_eq!(
            private.sign_pkcs1v15(&[0; 20], Hash::Sha1),
            Err(Error::Fault)
        );
        // Nothing is a valid signature of the zero hash value with this key
        // but its encoding's cube root, which is not 0 or 1.
        for s in [vec![0; 64], {
            let mut one = vec![0; 64];
            one[63] = 1;
            one
        }] {
            assert_eq!(
                public.verify_pkcs1v15(&s, &[0; 20], Hash::Sha1),
                Err(InvalidSignature)
            );
            assert_eq!(
                public.recover_pkcs1v15(&s, Hash::Sha1),
                Err(InvalidSignature)
            );
        }
        assert_eq!(
            public.verify_pkcs1v15(&[], &[0; 20], Hash::Sha1),
            Err(InvalidSignature)
        );
    }

    #[test]
    fn errors() {
        for e in [
            Error::InvalidDigestLength,
            Error::ModulusTooShort,
            Error::Fault,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
