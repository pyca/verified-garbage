//! SEED-CBC (SP 800-38A §6.2, with SEED as in RFC 4269), in place and without
//! padding.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::seed::vg_seed_expand_key_auto;
use crate::arch::dispatch::seed_cbc::{
    vg_seed_cbc_decrypt_chained_auto, vg_seed_cbc_encrypt_chained_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded SEED key, which serves both directions.
struct Key {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: CacheAligned<[u8; 128]>,
}

/// A SEED-CBC encryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct SeedCbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCbcEncryptor {
    /// Expands a 16-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.encrypt(&mut self.iv, buffer)
    }
}

/// A SEED-CBC decryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct SeedCbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl SeedCbcDecryptor {
    /// Expands a 16-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.decrypt(&mut self.iv, buffer)
    }
}

impl Key {
    /// Expands a 16-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut schedule = CacheAligned([0; 128]);
        crate::dit::enter!(dit);
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key_auto(dit, key, &mut schedule.0) };
        Ok(Self { schedule })
    }

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: the buffer holds `len / 16` whole blocks, and it, the
        // chaining value (which the function reads and replaces) and the
        // schedule are separate valid objects of the sizes of the signature,
        // none of them on the callee's stack.
        unsafe {
            vg_seed_cbc_encrypt_chained_auto(
                dit,
                &self.schedule.0,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }

    /// Decrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_seed_cbc_decrypt_chained_auto(
                dit,
                &self.schedule.0,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        Ok(())
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
