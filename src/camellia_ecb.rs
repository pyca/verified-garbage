//! Camellia ECB (RFC 3713), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Each operation accepts complete 16-byte blocks, including empty input.
//! On x86-64, ECB is bitsliced, eight blocks at a time in general-purpose
//! registers, with the S-boxes as Boolean circuits: no table lookups.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::camellia::{
    vg_camellia_ecb_decrypt, vg_camellia_ecb_encrypt, vg_camellia_expand_key,
};
use crate::zeroize::zeroize;

/// Why a Camellia ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16, 24 or 32 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded Camellia key for ECB encryption and decryption.
///
/// Keys of 16 bytes use 18 rounds; keys of 24 or 32 bytes, 24. No padding
/// is added or removed.
pub struct CamelliaEcb {
    schedule: [u8; 272],
    rounds: usize,
}

impl CamelliaEcb {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(Error::InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
        unsafe {
            vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule, rounds })
    }

    /// Encrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, true)
    }

    /// Decrypts complete 16-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        self.crypt(buffer, false)
    }

    fn crypt(&self, buffer: &mut [u8], encrypt: bool) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let f = if encrypt {
            vg_camellia_ecb_encrypt
        } else {
            vg_camellia_ecb_decrypt
        };
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer contains complete
        // 16-byte blocks, including zero blocks. The buffer and schedule are
        // separate valid objects and do not overlap the callee's stack. The
        // function zeroes its working space on its own stack before
        // returning.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for CamelliaEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
