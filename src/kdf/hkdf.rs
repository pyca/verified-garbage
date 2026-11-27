//! HKDF (RFC 5869): the HMAC-based extract-and-expand key derivation
//! function, with HMAC over SHA-1 or a SHA-2 hash function ([`HkdfHash`]).
//!
//! HKDF-Extract takes input keying material, and an optional salt, to a
//! pseudorandom key `PRK` ([`Hkdf::new`], or [`Hkdf::extract`] for `PRK`
//! itself); HKDF-Expand expands `PRK` into output keying material of up to
//! 255 digests for each context ([`Hkdf::expand`]). An [`Hkdf`] holds `PRK`
//! as HMAC keyed with it, so that each expansion starts from the keyed
//! states rather than keying HMAC again; [`Hkdf::from_prk`] makes one from a
//! pseudorandom key derived elsewhere (as TLS 1.3's key schedule does with
//! each of its secrets).

#![cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64",
    target_arch = "x86",
    target_arch = "x86_64"
))]

use core::marker::PhantomData;

use crate::align::CacheAligned;
use crate::arch::dispatch::hkdf::{vg_hkdf_expand_auto, vg_hkdf_extract_auto, vg_hkdf_key_auto};
use crate::error::InvalidKeyLength;
use crate::hashes::HashFunction;
use crate::hashes::sha1::Sha1;
use crate::hashes::sha256::Sha256;
use crate::hashes::sha384::Sha384;
use crate::hashes::sha512::Sha512;
use crate::hashes::tables::TableHash;
use crate::zeroize::zeroize;

mod sealed {
    pub trait Sealed: crate::hashes::HashFunction {
        /// The best of its tables of `Hmac` that this CPU runs, as the
        /// verified functions take it (`TableHash::hmac_table`).
        fn hmac_table() -> *const [usize; 6];
        /// A digest of zeros, for `PRK`.
        fn zero_output() -> Self::Output;
    }
}

/// A hash function that HKDF takes HMAC over.
pub trait HkdfHash: HashFunction + sealed::Sealed {}

/// Makes each hash function `$hash`, whose table is `TableHash::$table`, an
/// [`HkdfHash`].
macro_rules! hkdf_hash {
    ($($hash:ident => $table:ident,)+) => {
        $(
            impl sealed::Sealed for $hash {
                fn hmac_table() -> *const [usize; 6] {
                    TableHash::$table.hmac_table()
                }

                fn zero_output() -> Self::Output {
                    [0; <$hash as HashFunction>::OUTPUT_SIZE]
                }
            }

            impl HkdfHash for $hash {}
        )+
    };
}

hkdf_hash! {
    Sha1 => Sha1,
    Sha256 => Sha256,
    Sha384 => Sha384,
    Sha512 => Sha512,
}

/// The output keying material asked of [`Hkdf::expand`] is longer than
/// HKDF-Expand gives: 255 times the hash function's digest size.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OutputTooLong;

impl core::fmt::Display for OutputTooLong {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("output is longer than 255 digests")
    }
}

impl core::error::Error for OutputTooLong {}

/// HKDF's pseudorandom key `PRK` with the hash function `H`, held as HMAC
/// keyed with it: the inner and the outer streaming states, which
/// HKDF-Expand starts each block from. It is wiped when dropped.
pub struct Hkdf<H: HkdfHash> {
    /// The states as `vg_hkdf_key` writes them: the inner one first, the
    /// outer one from the 192nd byte.
    key: CacheAligned<[u8; 384]>,
    hash: PhantomData<H>,
}

impl<H: HkdfHash> Hkdf<H> {
    /// HKDF-Extract (RFC 5869 §2.2) of the input keying material `ikm` with
    /// `salt`, keyed for HKDF-Expand. No salt (`None`) is the same as a salt
    /// of `H::OUTPUT_SIZE` zeros, or an empty one.
    pub fn new(salt: Option<&[u8]>, ikm: &[u8]) -> Self {
        Self::extract(salt, ikm).1
    }

    /// HKDF-Extract, as [`new`](Self::new) does, with the pseudorandom key
    /// `PRK = HMAC-Hash(salt, IKM)` itself.
    pub fn extract(salt: Option<&[u8]>, ikm: &[u8]) -> (H::Output, Self) {
        crate::dit::enter!(dit);
        let salt = salt.unwrap_or(&[]);
        let mut prk = H::zero_output();
        let p = prk.as_mut();
        // SAFETY: `salt` and `ikm` are valid for reads of their lengths and
        // `prk` for reads and writes of its, `H::OUTPUT_SIZE`, the digest
        // length of the hash function `H::hmac_table()` names; `prk` is a
        // distinct object from them and from the table, which are only read,
        // so it overlaps none of them nor the call's stack frame, and, as
        // Rust objects, none wraps around the address space. The table is
        // one of the crate's tables of `Hmac`, the best one this CPU runs.
        unsafe {
            vg_hkdf_extract_auto(
                dit,
                salt.as_ptr(),
                salt.len(),
                ikm.as_ptr(),
                ikm.len(),
                p.as_mut_ptr(),
                p.len(),
                H::hmac_table(),
            );
        }
        let hkdf = Self::keyed(dit, prk.as_ref());
        (prk, hkdf)
    }

    /// From a pseudorandom key `prk` of at least `H::OUTPUT_SIZE` bytes, as
    /// HKDF-Extract gives (RFC 5869 §2.3): it skips HKDF-Extract.
    ///
    /// # Errors
    ///
    /// [`InvalidKeyLength`] if `prk` is shorter than `H::OUTPUT_SIZE`.
    pub fn from_prk(prk: &[u8]) -> Result<Self, InvalidKeyLength> {
        if prk.len() < H::OUTPUT_SIZE {
            return Err(InvalidKeyLength);
        }
        crate::dit::enter!(dit);
        Ok(Self::keyed(dit, prk))
    }

    /// HMAC keyed with `prk`.
    fn keyed(dit: crate::dit::Dit<'_>, prk: &[u8]) -> Self {
        let mut key = CacheAligned([0; 384]);
        // SAFETY: `prk` is valid for reads of its length and `key` for reads
        // and writes of its 384 bytes; `key` is a distinct object from `prk`
        // and the table, which are only read, so it overlaps neither of them
        // nor the call's stack frame, and, as Rust objects, none wraps
        // around the address space. The table is one of the crate's tables
        // of `Hmac`, the best one this CPU runs.
        unsafe { vg_hkdf_key_auto(dit, prk.as_ptr(), prk.len(), &mut key.0, H::hmac_table()) };
        Hkdf {
            key,
            hash: PhantomData,
        }
    }

    /// HKDF-Expand (RFC 5869 §2.3): fills `okm` with the output keying
    /// material of `okm.len()` bytes for the context `info`.
    ///
    /// # Errors
    ///
    /// [`OutputTooLong`] if `okm` is longer than `255 * H::OUTPUT_SIZE`
    /// bytes, which HKDF-Expand does not give; `okm` is then unchanged.
    pub fn expand(&self, info: &[u8], okm: &mut [u8]) -> Result<(), OutputTooLong> {
        if okm.len() > 255 * H::OUTPUT_SIZE {
            return Err(OutputTooLong);
        }
        crate::dit::enter!(dit);
        // SAFETY: `self.key` holds HMAC's states keyed with a pseudorandom
        // key for `H` (`keyed` wrote them with the same table) and is valid
        // for reads of its 384 bytes, `info` for reads of its length and
        // `okm` for reads and writes of its, at most 255 digests of `H`;
        // `okm` is a distinct object from the others, which are only read,
        // so it overlaps none of them nor the call's stack frame, and, as
        // Rust objects, none wraps around the address space. The table is
        // one of the crate's tables of `Hmac`, the best one this CPU runs.
        unsafe {
            vg_hkdf_expand_auto(
                dit,
                &self.key.0,
                info.as_ptr(),
                info.len(),
                okm.as_mut_ptr(),
                okm.len(),
                H::hmac_table(),
            );
        }
        Ok(())
    }
}

impl<H: HkdfHash> Clone for Hkdf<H> {
    fn clone(&self) -> Self {
        Hkdf {
            key: self.key,
            hash: PhantomData,
        }
    }
}

impl<H: HkdfHash> core::fmt::Debug for Hkdf<H> {
    /// Leaves out the keyed states, which are secret.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Hkdf").finish_non_exhaustive()
    }
}

impl<H: HkdfHash> Drop for Hkdf<H> {
    /// Wipes the keyed states.
    fn drop(&mut self) {
        zeroize(&mut self.key.0);
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use std::format;
    use std::string::ToString;

    use super::{Hkdf, OutputTooLong};
    use crate::hashes::sha256::Sha256;

    /// A clone expands as the original does, after the original is dropped
    /// (which wipes only its own states); the debug output leaves out the
    /// states; and the error has a message.
    #[test]
    fn clone_debug_error() {
        let hkdf = Hkdf::<Sha256>::new(Some(b"salt"), b"input keying material");
        let clone = hkdf.clone();
        let (mut a, mut b) = ([0; 40], [0; 40]);
        hkdf.expand(b"info", &mut a).unwrap();
        drop(hkdf);
        clone.expand(b"info", &mut b).unwrap();
        assert_eq!(a, b);
        assert_eq!(format!("{clone:?}"), "Hkdf { .. }");
        assert!(!OutputTooLong.to_string().is_empty());
    }
}
