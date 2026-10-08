//! CAST5 (CAST-128, RFC 2144) ECB, in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Keys contain 5 to 16 bytes (40 to 128 bits, RFC 2144 §2.5); a key of up
//! to 10 bytes is used with 12 rounds, a longer one with 16. Each operation
//! accepts complete eight-byte blocks, including empty input. The S-box
//! lookups scan whole tables in vector registers (SSE2 on x86-64, AdvSIMD on
//! AArch64), so their timing depends on neither the key nor the data; one
//! block at a time.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::cast5::{vg_cast5_ecb_decrypt, vg_cast5_ecb_encrypt, vg_cast5_expand_key};
use crate::zeroize::zeroize;

/// Why a CAST5 ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 5 to 16 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// An expanded CAST5 key for ECB encryption and decryption.
pub struct Cast5Ecb {
    schedule: [u8; 128],
    rounds: usize,
}

impl Cast5Ecb {
    /// Expands a key of 5 to 16 bytes for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !(5..=16).contains(&key.len()) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 128];
        let mut scratch = [0; 32];
        // SAFETY: the key has a validated length; the key, schedule and
        // scratch space are separate valid objects of the sizes of the
        // signature.
        unsafe {
            vg_cast5_expand_key(key.as_ptr(), key.len(), &mut schedule, &mut scratch);
        }
        // The scratch space holds the intermediate values of key expansion.
        zeroize(&mut scratch);
        Ok(Self {
            schedule,
            rounds: if key.len() <= 10 { 12 } else { 16 },
        })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, vg_cast5_ecb_encrypt)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, vg_cast5_ecb_decrypt)
    }

    fn crypt(&self, buffer: &mut [u8], f: Ecb) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        let mut scratch = [0; 32];
        // SAFETY: `rounds` is 12 or 16, as `new` chose for the key the
        // schedule was expanded from; the buffer holds `len / 8` whole
        // blocks, and it, the schedule and the scratch space are separate
        // valid objects of the sizes of the signature.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
                &mut scratch,
            );
        }
        // The scratch space may hold the subkeys, the data and our caller's
        // registers.
        zeroize(&mut scratch);
        Ok(())
    }
}

/// The signature of `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt`.
#[cfg(target_arch = "x86_64")]
type Ecb = unsafe extern "sysv64" fn(*const [u8; 128], usize, *mut [u8; 8], usize, *mut [u64; 32]);
/// The signature of `vg_cast5_ecb_encrypt` and `vg_cast5_ecb_decrypt`.
#[cfg(target_arch = "aarch64")]
type Ecb = unsafe extern "C" fn(*const [u8; 128], usize, *mut [u8; 8], usize, *mut [u64; 32]);

impl Drop for Cast5Ecb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
