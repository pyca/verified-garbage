//! Blowfish-ECB (Schneier, FSE 1994), in place and without padding.
//!
//! Key expansion and encryption/decryption use verified primitives
//! (`VG.Spec.Blowfish.expandKeyContract`, `ecbEncryptContract` and
//! `ecbDecryptContract`). Each operation accepts complete eight-byte blocks,
//! including empty input.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::blowfish::{
    vg_blowfish_ecb_decrypt_auto, vg_blowfish_ecb_encrypt_auto, vg_blowfish_expand_key_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Blowfish key for ECB encryption and decryption.
pub struct BlowfishEcb {
    schedule: CacheAligned<[u8; 4168]>,
}

impl BlowfishEcb {
    /// Expands a key of 4..=56 bytes (32 to 448 bits) for use in either
    /// direction. Weak keys are accepted.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !(4..=56).contains(&key.len()) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 4168]);
        crate::dit::enter!(dit);
        // SAFETY: the key has a length in 4..=56; the key and the schedule
        // are separate valid objects of the lengths passed.
        unsafe { vg_blowfish_expand_key_auto(dit, key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self { schedule })
    }

    /// Encrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn encrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: the buffer holds `len / 8` complete eight-byte blocks;
        // it and the expanded schedule are separate valid objects of the
        // lengths passed, neither on the callee's stack.
        unsafe {
            vg_blowfish_ecb_encrypt_auto(
                dit,
                &self.schedule.0,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }

    /// Decrypts complete eight-byte blocks in place. Empty input is valid.
    /// Returns an error without changing the buffer if its length is invalid.
    pub fn decrypt(&self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: the buffer holds `len / 8` complete eight-byte blocks;
        // it and the expanded schedule are separate valid objects of the
        // lengths passed, neither on the callee's stack.
        unsafe {
            vg_blowfish_ecb_decrypt_auto(
                dit,
                &self.schedule.0,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for BlowfishEcb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
