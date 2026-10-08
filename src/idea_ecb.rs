//! IDEA in ECB mode (Lai, 1992), in place and without padding.
//!
//! Key expansion, the decryption subkeys and ECB use verified primitives:
//! IDEA decrypts with the encryption function under the decryption
//! subkeys, so both directions run the same ECB primitive. Each operation
//! accepts complete eight-byte blocks, including empty input. On x86-64 and
//! AArch64, ECB runs a block at a time in general-purpose registers.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::idea::{vg_idea_ecb, vg_idea_expand_key, vg_idea_invert_key};
use crate::zeroize::zeroize;

/// Why an IDEA ECB operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

/// An expanded IDEA key for ECB encryption and decryption: its encryption
/// and decryption subkeys. No padding is added or removed.
pub struct IdeaEcb {
    encrypt: [u8; 104],
    decrypt: [u8; 104],
}

impl IdeaEcb {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let key: &[u8; 16] = key.try_into().map_err(|_| Error::InvalidKeyLength)?;
        let mut encrypt = [0; 104];
        let mut decrypt = [0; 104];
        // SAFETY: the key and both schedules are separate valid buffers of
        // the required sizes.
        unsafe {
            vg_idea_expand_key(key, &mut encrypt);
            vg_idea_invert_key(&encrypt, &mut decrypt);
        }
        Ok(Self { encrypt, decrypt })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        crypt(&self.encrypt, buffer)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), Error> {
        crypt(&self.decrypt, buffer)
    }
}

fn crypt(schedule: &[u8; 104], buffer: &mut [u8]) -> Result<(), Error> {
    if !buffer.len().is_multiple_of(8) {
        return Err(Error::IncompleteBlock);
    }
    // SAFETY: buffer contains complete eight-byte blocks, including zero
    // blocks. The buffer and schedule are separate valid objects and do not
    // overlap the callee's stack.
    unsafe {
        vg_idea_ecb(schedule, buffer.as_mut_ptr().cast(), buffer.len() / 8);
    }
    Ok(())
}

impl Drop for IdeaEcb {
    fn drop(&mut self) {
        zeroize(&mut self.encrypt);
        zeroize(&mut self.decrypt);
    }
}
