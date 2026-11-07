//! PBKDF2-HMAC (RFC 8018 §5.2): PBKDF2 with HMAC over MD5, SHA-1 or a SHA-2
//! hash function ([`Pbkdf2Hash`]) as its pseudorandom function.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use core::num::NonZeroU32;

use crate::hmac::HmacHash;

mod md5;
mod sha1;
mod sha224;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

/// A hash function with a verified PBKDF2-HMAC implementation.
pub trait Pbkdf2Hash: HmacHash {
    /// Fills `out` with the key derived from `password` and `salt` with
    /// `iterations` iterations (see [`derive()`]).
    #[doc(hidden)]
    fn pbkdf2_derive(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]);
}

/// Fills `out` with the key derived from `password` and `salt` with
/// `iterations` iterations of PBKDF2 with HMAC over the hash function `H`.
///
/// # Panics
///
/// If `out` is longer than (2³² − 1) times the digest size ("derived key too
/// long" in RFC 8018).
pub fn derive<H: Pbkdf2Hash>(password: &[u8], salt: &[u8], iterations: NonZeroU32, out: &mut [u8]) {
    H::pbkdf2_derive(password, salt, iterations, out);
}

/// The key derived from a password did not match the expected one: the
/// password (or the salt or iteration count) is not the one it was derived
/// from. Returned by [`verify`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyMismatch;

impl core::fmt::Display for KeyMismatch {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PBKDF2 derived key does not match")
    }
}

impl core::error::Error for KeyMismatch {}

/// Checks a password against a stored derived key: derives a key of `N`
/// bytes from `password` and `salt` with `iterations` iterations of PBKDF2
/// with HMAC over the hash function `H` (as [`derive()`] does), and
/// compares it with `expected`.
///
/// The comparison is constant time: the time taken does not depend on
/// where, or whether, the keys differ. The derivation is
/// [`derive()`]'s, whose verified implementation leaks only the lengths
/// of the password and the salt and the iteration count. `N` is public too.
/// The derived key is wiped before returning.
///
/// `N` is a type parameter, at least 16 (a smaller one is an error when the
/// call is compiled), so that the length checked is fixed in the caller's
/// code: PBKDF2's keys of different lengths share their prefixes, so a key
/// checked at a length taken from a slice (a truncated stored key, or one an
/// attacker sent) would match a password on as few bytes as it has. A caller
/// with the stored key in a slice converts it (`stored.try_into()`), which
/// fails if it does not have the length the code expects.
///
/// # Errors
///
/// [`KeyMismatch`] if the derived key is not `expected`.
///
/// # Panics
///
/// If `N` is more than (2³² − 1) times the digest size ("derived key too
/// long" in RFC 8018), as [`derive()`] does.
pub fn verify<H: Pbkdf2Hash, const N: usize>(
    password: &[u8],
    salt: &[u8],
    iterations: NonZeroU32,
    expected: &[u8; N],
) -> Result<(), KeyMismatch> {
    crate::ct::assert_verify_len!(N);
    let mut key = [0u8; N];
    H::pbkdf2_derive(password, salt, iterations, &mut key);
    let matches = crate::ct::eq(&key, expected);
    crate::zeroize::zeroize(&mut key);
    if matches { Ok(()) } else { Err(KeyMismatch) }
}

/// Checks that PBKDF2 can derive `len` bytes from blocks of `block` bytes:
/// at most 2³² − 1 blocks ("derived key too long" in RFC 8018).
fn check_len(len: usize, block: usize) {
    u32::try_from(len.div_ceil(block)).expect("PBKDF2 derived key too long");
}

/// Makes a hash function a [`Pbkdf2Hash`] with the dispatcher of its
/// verified `vg_pbkdf2_hmac_<hash>` (contract
/// `VG.Spec.Hmac.Instance.pbkdf2Contract` of the hash's `Instance`),
/// `vg_pbkdf2_hmac_<hash>_auto`, which derives the whole key with the best
/// implementation this CPU runs, given the digest size.
macro_rules! whole_pbkdf2 {
    ($hash:ident, pbkdf2: $pbkdf2:path, output: $output:literal $(,)?) => {
        impl super::Pbkdf2Hash for $hash {
            fn pbkdf2_derive(
                password: &[u8],
                salt: &[u8],
                iterations: core::num::NonZeroU32,
                out: &mut [u8],
            ) {
                super::check_len(out.len(), $output);
                // SAFETY: `iterations` is positive and `out.len()` at most
                // (2³² − 1) times the digest size; `password` and `salt` are
                // valid for reads of their lengths and `out` for reads and
                // writes of its length; `out` is a distinct object from the
                // others (`password` and `salt` are only read), so it
                // overlaps neither of them nor the call's stack frame, and,
                // as Rust objects, none wraps around the address space. The
                // dispatcher calls only an implementation the CPU has the
                // features of.
                unsafe {
                    $pbkdf2(
                        password.as_ptr(),
                        password.len(),
                        salt.as_ptr(),
                        salt.len(),
                        iterations.get(),
                        out.as_mut_ptr(),
                        out.len(),
                    )
                };
            }
        }

        #[cfg(test)]
        mod tests {
            use super::$hash;

            /// With no expected value computed here, for the hash
            /// functions without published PBKDF2 vectors too: a key of
            /// three blocks less a byte begins with the key of one block
            /// derived from the same inputs (block `i` of a derived key
            /// depends on `i` alone), and `verify` accepts it and rejects
            /// it with a byte changed. The vectors are in
            /// `tests/wycheproof/pbkdf2_<hash>.rs`, where there are any.
            #[test]
            fn prefix_and_verify() {
                let iterations = core::num::NonZeroU32::new(3).unwrap();
                let mut long = [0; 3 * $output - 1];
                super::super::derive::<$hash>(b"password", b"salt", iterations, &mut long);
                let mut short = [0; $output];
                super::super::derive::<$hash>(b"password", b"salt", iterations, &mut short);
                assert_eq!(long[..$output], short);
                let verify = super::super::verify::<$hash, { 3 * $output - 1 }>;
                assert_eq!(verify(b"password", b"salt", iterations, &long), Ok(()));
                long[$output] ^= 1;
                assert_eq!(
                    verify(b"password", b"salt", iterations, &long),
                    Err(super::super::KeyMismatch)
                );
            }
        }
    };
}

use whole_pbkdf2;
