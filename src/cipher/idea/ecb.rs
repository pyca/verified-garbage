//! IDEA-ECB (Lai, 1992), in place and without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::idea::{vg_idea_ecb, vg_idea_expand_key, vg_idea_invert_key};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded IDEA key for ECB encryption and decryption: its encryption
/// and decryption subkeys. No padding is added or removed.
///
/// ECB encrypts equal blocks to equal blocks, so it reveals patterns in the
/// data.
pub struct IdeaEcb {
    encrypt: [u8; 104],
    decrypt: [u8; 104],
}

impl IdeaEcb {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut encrypt = [0; 104];
        let mut decrypt = [0; 104];
        // SAFETY: the key and both schedules are separate valid buffers of
        // the required sizes.
        unsafe {
            vg_idea_expand_key(dit, key, &mut encrypt);
            vg_idea_invert_key(dit, &encrypt, &mut decrypt);
        }
        Ok(Self { encrypt, decrypt })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        crypt(&self.encrypt, buffer)
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        crypt(&self.decrypt, buffer)
    }
}

fn crypt(schedule: &[u8; 104], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
    crate::dit::enter!(dit);
    if !buffer.len().is_multiple_of(8) {
        return Err(IncompleteBlock);
    }
    // SAFETY: buffer contains complete eight-byte blocks, including zero
    // blocks. The buffer and schedule are separate valid objects and do not
    // overlap the callee's stack.
    unsafe {
        vg_idea_ecb(dit, schedule, buffer.as_mut_ptr().cast(), buffer.len() / 8);
    }
    Ok(())
}

impl Drop for IdeaEcb {
    fn drop(&mut self) {
        zeroize(&mut self.encrypt);
        zeroize(&mut self.decrypt);
    }
}
