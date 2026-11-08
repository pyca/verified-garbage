//! SM4-CBC (SP 800-38A §6.2, with SM4 as in GB/T 32907-2016, transcribed in
//! draft-ribose-cfrg-sm4-10), in place and without padding.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::sm4::vg_sm4_expand_key_auto;
use crate::arch::dispatch::sm4_cbc::{
    vg_sm4_cbc_decrypt_chained_auto, vg_sm4_cbc_encrypt_chained_auto,
};
use crate::error::IncompleteBlock;
use crate::zeroize::zeroize;

/// An expanded SM4 key, which serves both directions.
struct Key {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: CacheAligned<[u8; 128]>,
}

/// An SM4-CBC encryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Sm4CbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl Sm4CbcEncryptor {
    /// Expands a 16-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8; 16], iv: &[u8; 16]) -> Self {
        Self {
            key: Key::new(key),
            iv: *iv,
        }
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.key.encrypt(&mut self.iv, buffer)
    }
}

/// An SM4-CBC decryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Sm4CbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl Sm4CbcDecryptor {
    /// Expands a 16-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8; 16], iv: &[u8; 16]) -> Self {
        Self {
            key: Key::new(key),
            iv: *iv,
        }
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
    fn new(key: &[u8; 16]) -> Self {
        let mut schedule = CacheAligned([0; 128]);
        crate::dit::enter!(dit);
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe {
            vg_sm4_expand_key_auto(dit, key, &mut schedule.0);
        }
        Self { schedule }
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
            vg_sm4_cbc_encrypt_chained_auto(
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
            vg_sm4_cbc_decrypt_chained_auto(
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
