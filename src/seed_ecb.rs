//! SEED ECB (RFC 4269, SP 800-38A §6.1), in place and without padding.
//!
//! Key expansion and ECB encryption/decryption use verified primitives.
//! Each operation accepts complete 16-byte blocks, including empty input.
//! On x86-64, ECB runs sixteen blocks at a time, computing each round's `G`
//! functions bitsliced in general-purpose registers, with no table lookups.

#![cfg(target_arch = "x86_64")]

use crate::arch::seed::{vg_seed_ecb_decrypt, vg_seed_ecb_encrypt, vg_seed_expand_key};
use crate::zeroize::zeroize;

/// Why a SEED ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded SEED key for ECB encryption and decryption.
///
/// No padding is added or removed.
pub struct SeedEcb {
    schedule: [u8; 128],
}

impl SeedEcb {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_seed_expand_key(key, &mut schedule);
        }
        Self { schedule }
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
            vg_seed_ecb_encrypt
        } else {
            vg_seed_ecb_decrypt
        };
        // SAFETY: buffer contains complete 16-byte blocks, including zero
        // blocks. The buffer and schedule are separate valid objects and do
        // not overlap the callee's stack. The function zeroes its working
        // space on its own stack before returning.
        unsafe {
            f(
                &self.schedule,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for SeedEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
