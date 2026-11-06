//! RSASSA-PSS (RFC 8017 §8.1) of a hash value, as methods of the keys of
//! [`crate::rsa`], and with MD5, SHA-1 or a SHA-2 hash function for the
//! message and for MGF1.
//!
//! [`PrivateKey::sign_pss`] releases a signature only if it verifies with the
//! public exponent. [`PublicKey::verify_pss`] expects a salt of a given length
//! or of any length ([`SaltLength::Any`]). The timing may depend on the public
//! key, the hash functions, the lengths and the expected salt length, but not
//! on the hash value, the salt, the signature or the private key.

#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "powerpc64",
        target_arch = "riscv64"
    ),
    feature = "alloc"
))]

mod aarch64;
mod arm;
mod powerpc64;
mod riscv64;
mod table;
mod x86;
mod x86_64;

// The verified functions and tables of the target's architecture.
#[cfg(target_arch = "aarch64")]
use aarch64 as arch;
#[cfg(target_arch = "arm")]
use arm as arch;
#[cfg(target_arch = "powerpc64")]
use powerpc64 as arch;
#[cfg(target_arch = "riscv64")]
use riscv64 as arch;
#[cfg(target_arch = "x86")]
use x86 as arch;
#[cfg(target_arch = "x86_64")]
use x86_64 as arch;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::cpu::detected;
use crate::error::InvalidSignature;
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
    /// The encoding does not fit the modulus: the hash value, the salt and
    /// two bytes are longer than `⌈(bits of n - 1) / 8⌉`.
    SaltTooLong,
    /// The signature failed the private-key operation's check against the
    /// public exponent (a factor of the key is not prime, or the computation
    /// was faulted) and is not released.
    Fault,
    /// The random number generator failed.
    Randomness,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidDigestLength => "hash value length is not the hash function's",
            Error::SaltTooLong => "RSA modulus is too short for the hash value and the salt",
            Error::Fault => "RSA signature failed its check against the public exponent",
            Error::Randomness => "the random number generator failed",
        })
    }
}

impl core::error::Error for Error {}

/// A hash function, as the verified functions take it: the words of one of
/// the tables of `MdHash` (`crate::arch::fn_tables`), their argument `hash`.
type MdTable = *const [usize; 11];

/// MGF1's hash function, as the verified functions take it: the words of
/// one of the tables of `Hash`, their last argument, `mgf1`.
type Table = *const [usize; 5];

/// Declares the types of verified functions, in the calling convention the
/// emitter generates on each target: `sysv64` on x86-64 (on Windows too),
/// and C's elsewhere; the tables of the hash function and of MGF1's are
/// their last arguments.
macro_rules! verified_fn_types {
    ($(
        $(#[$doc:meta])*
        type $name:ident = fn($($arg:ty),* $(,)?) -> $ret:ty;
    )*) => {$(
        $(#[$doc])*
        #[cfg(target_arch = "x86_64")]
        type $name = unsafe extern "sysv64" fn($($arg,)* MdTable, Table) -> $ret;
        $(#[$doc])*
        #[cfg(not(target_arch = "x86_64"))]
        type $name = unsafe extern "C" fn($($arg,)* MdTable, Table) -> $ret;
    )*};
}

verified_fn_types! {
    /// The type of the implementations of `vg_rsa_pss_sign`.
    type SignFn = fn(
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
        *const u8,
        usize,
        *const u8,
        usize,
        *mut u64,
        usize,
    ) -> u32;

    /// The type of the implementations of `vg_rsa_pss_verify_precomputed`.
    type VerifyFn = fn(
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        *const u8,
        usize,
        usize,
        u32,
        *mut u64,
        usize,
        *const u64,
        usize,
    ) -> u32;
}

/// The verified functions for the implementations this CPU runs best,
/// `(sign, verify)`, with the tables of the hash function `hash` and of
/// MGF1's `mgf1_hash` (`table::md_table`, `table::table`).
fn with_tables(hash: Hash, mgf1_hash: Hash) -> (SignFn, VerifyFn, MdTable, Table) {
    let f = detected();
    let (sign, verify) = arch::functions(f);
    (
        sign,
        verify,
        table::md_table(hash, f),
        table::table(mgf1_hash, f),
    )
}

/// The words of working space the functions need for an `n_len`-byte
/// modulus (`VG.Spec.RsaPss.scratchWords`).
pub(crate) fn scratch_words(n_len: usize) -> usize {
    crate::rsa::scratch_words(n_len) + 1024
}

/// The words of working space verification needs for an `n_len`-byte
/// modulus (`VG.Spec.RsaPss.publicScratchWords`).
pub(crate) fn public_scratch_words(n_len: usize) -> usize {
    crate::rsa::public_scratch_words(n_len) + 1024
}

impl PrivateKey {
    /// RSASSA-PSS-SIGN (RFC 8017 §8.1.1) of the hash value `digest` of the hash
    /// function `hash`, with MGF1 over `mgf1_hash` and a salt of `salt_len`
    /// random bytes: the signature, as long as the modulus.
    pub fn sign_pss(
        &self,
        digest: &[u8],
        hash: Hash,
        mgf1_hash: Hash,
        salt_len: usize,
    ) -> Result<Vec<u8>, Error> {
        if digest.len() != hash.digest_len() {
            return Err(Error::InvalidDigestLength);
        }
        if salt_len > self.n.len() {
            return Err(Error::SaltTooLong);
        }
        let mut salt = vec![0u8; salt_len];
        getrandom::fill(&mut salt).map_err(|_| Error::Randomness)?;
        let r = sign_with(self, digest, hash, mgf1_hash, &salt);
        zeroize(&mut salt);
        r
    }
}

/// The signature of `digest` with the salt `salt`.
fn sign_with(
    key: &PrivateKey,
    digest: &[u8],
    hash: Hash,
    mgf1_hash: Hash,
    salt: &[u8],
) -> Result<Vec<u8>, Error> {
    let k = key.n.len();
    let mut out = vec![0; k];
    let mut scratch = crate::rsa::Scratch::new(scratch_words(k));
    let (f, _, h, m) = with_tables(hash, mgf1_hash);
    // SAFETY: each pointer is valid for its length (`out` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations; `PrivateKey::from_crt` gives
    // `64 ≤ n_len ≤ 1024`, `1 ≤ e_len ≤ 5 ≤ n_len`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len`, `dp_len = qinv_len = p_len` and `dq_len = q_len`;
    // `out_len = n_len` and `scratch_len = 16 n_len + 1056`; `hash` is the
    // words of a table of the crate's of `MdHash` and `mgf1` of one of
    // `Hash`, and `digest_len` is the digest length of `hash`'s, its word 6
    // (`hashes::tables::tests::table_words` checks it, and `sign_pss`
    // the length); and the
    // CPU has the features of `f` and of the tables' functions, which
    // `functions`, `table::md_table` and `table::table` chose for the
    // features detected (which fails to compile if they need
    // others).
    let r = unsafe {
        f(
            out.as_mut_ptr(),
            k,
            key.n.as_ptr(),
            k,
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
            digest.as_ptr(),
            digest.len(),
            salt.as_ptr(),
            salt.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
            h,
            m,
        )
    };
    // `PrivateKey::from_crt` checked the key, so a refusal means the encoding
    // does not fit.
    match r {
        1 => Ok(out),
        2 => Err(Error::Fault),
        _ => Err(Error::SaltTooLong),
    }
}

impl PublicKey {
    /// RSASSA-PSS-VERIFY (RFC 8017 §8.1.2): checks that `signature` is a
    /// valid signature of the hash value `digest` of the hash function
    /// `hash`, with MGF1 over `mgf1_hash` and a salt of `salt_length`.
    ///
    /// # Errors
    ///
    /// [`InvalidSignature`] if it is not, including if `digest` is not as
    /// long as `hash`'s values or `signature` not as long as the modulus.
    pub fn verify_pss(
        &self,
        signature: &[u8],
        digest: &[u8],
        hash: Hash,
        mgf1_hash: Hash,
        salt_length: SaltLength,
    ) -> Result<(), InvalidSignature> {
        let k = self.n.len();
        if digest.len() != hash.digest_len() || signature.len() != k {
            return Err(InvalidSignature);
        }
        let (salt_len, any) = match salt_length {
            SaltLength::Len(l) => (l, 0),
            SaltLength::Any => (0, 1),
        };
        let (_, f, h, m) = with_tables(hash, mgf1_hash);
        let mut scratch = self.verify_scratch.take(public_scratch_words(k), false);
        let pre = self.pre(&mut scratch);
        // SAFETY: each pointer is valid for its length (`scratch` for writes),
        // and none overlaps another or wraps around, as they are distinct Rust
        // allocations; `PublicKey::new` gives `64 ≤ n_len ≤ 1024` and
        // `1 ≤ e_len ≤ 5 ≤ n_len`; `sig_len = n_len` and
        // `scratch_len = 8 ⌈n_len / 8⌉ + 1072`; `pre` holds the verified
        // precomputed values for `self.n`, with their required length; `hash` is
        // the words of a table of the crate's of `MdHash` and `mgf1` of one of
        // `Hash`, and `digest_len` is the digest length of `hash`'s, its word 6
        // (`hashes::tables::tests::table_words` checks it); and the CPU has the
        // features of `f` and of the tables' functions, which `functions`,
        // `table::md_table` and `table::table` chose for the features detected
        // (which fails to compile if they need others).
        let r = unsafe {
            f(
                self.n.as_ptr(),
                k,
                self.e.as_ptr(),
                self.e.len(),
                digest.as_ptr(),
                digest.len(),
                signature.as_ptr(),
                k,
                salt_len,
                any,
                scratch.as_mut_ptr(),
                scratch.len(),
                pre.as_ptr(),
                pre.len(),
                h,
                m,
            )
        };
        // The encoding is public: ScratchLease returns the buffer to the key unwiped.
        if r == 1 {
            Ok(())
        } else {
            Err(InvalidSignature)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, Hash, InvalidSignature, SaltLength};
    use crate::rsa::tests::composite_key;
    use alloc::string::ToString;

    /// With `composite_key`'s 64-byte modulus (`emLen = 64`): a hash value of
    /// the wrong length, salts longer than the modulus and than the encoding
    /// has room for, and a signature that fails the check, with MGF1 over the
    /// hash function and over another.
    #[test]
    fn sign_refused() {
        let (private, _) = composite_key();
        let s = |d: &[u8], h, g, l| private.sign_pss(d, h, g, l);
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
        assert_eq!(s(&[0; 20], Hash::Sha1, Hash::Sha256, 0), Err(Error::Fault));
    }

    /// Arguments `verify` refuses before calling the verified function.
    #[test]
    fn verify_refused() {
        let (_, public) = composite_key();
        let sig = [1; 64];
        let v = |s: &[u8], d: &[u8], h, g| public.verify_pss(s, d, h, g, SaltLength::Any);
        let bad = Err(InvalidSignature);
        assert_eq!(v(&sig, &[0; 19], Hash::Sha1, Hash::Sha1), bad);
        assert_eq!(v(&sig[..63], &[0; 20], Hash::Sha1, Hash::Sha1), bad);
        assert_eq!(v(&sig, &[0; 20], Hash::Sha1, Hash::Sha1), bad);
        assert_eq!(v(&sig, &[0; 20], Hash::Sha1, Hash::Sha256), bad);
    }

    #[test]
    fn errors() {
        for e in [
            Error::InvalidDigestLength,
            Error::SaltTooLong,
            Error::Fault,
            Error::Randomness,
        ] {
            assert!(!e.to_string().is_empty());
        }
    }
}
