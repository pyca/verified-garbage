//! CAST5-CBC (SP 800-38A §6.2, with CAST5 as in RFC 2144), in place and without
//! padding.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::Cast5Ecb;
use crate::arch::dispatch::cast5_cbc::{
    vg_cast5_cbc_decrypt_chained_auto, vg_cast5_cbc_encrypt_chained_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};

/// An expanded CAST5 key, which serves both directions.
struct Key {
    key: Cast5Ecb,
}

/// A CAST5-CBC encryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Cast5CbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5CbcEncryptor {
    /// Expands a key of 5 to 16 bytes, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.encrypt(&mut self.iv, buffer)
    }
}

/// A CAST5-CBC decryption of one message, without padding.
///
/// Each call takes whole 8-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Cast5CbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5CbcDecryptor {
    /// Expands a key of 5 to 16 bytes, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.decrypt(&mut self.iv, buffer)
    }
}

impl Key {
    /// Expands a key of 5 to 16 bytes.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Cast5Ecb::new(key)?,
        })
    }

    /// Encrypts whole 8-byte blocks in place, chained from `iv`, and replaces
    /// `iv` with the last ciphertext block (leaving it unchanged for empty
    /// input). Returns an
    /// error without changing anything if the buffer's length is not a
    /// multiple of 8.
    fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; the buffer holds `len / 8` whole
        // blocks, and it, the chaining value (which the function reads and
        // replaces) and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack.
        unsafe {
            vg_cast5_cbc_encrypt_chained_auto(
                dit,
                self.key.schedule(),
                self.key.rounds(),
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }

    /// Decrypts whole 8-byte blocks in place, chained from `iv`, and replaces
    /// `iv` with the last ciphertext block (leaving it unchanged for empty
    /// input). Returns an
    /// error without changing anything if the buffer's length is not a
    /// multiple of 8.
    fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        crate::dit::enter!(dit);
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_cast5_cbc_decrypt_chained_auto(
                dit,
                self.key.schedule(),
                self.key.rounds(),
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}
