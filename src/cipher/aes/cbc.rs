//! AES-CBC (SP 800-38A §6.2) with 128-, 192- and 256-bit keys, in place and
//! without padding.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_cbc::{vg_aes_cbc_decrypt_auto, vg_aes_cbc_encrypt_auto};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded AES key, which serves both directions.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

/// An AES-CBC encryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCbcEncryptor {
    /// Expands a 16-, 24- or 32-byte key, to encrypt a message from `iv`.
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

/// An AES-CBC decryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCbcDecryptor {
    /// Expands a 16-, 24- or 32-byte key, to decrypt a message from `iv`.
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
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature. The
        // dispatcher calls only an implementation the CPU has the features of.
        unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
        })
    }

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, |data, n, scratch| {
            // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
            // schedule; `crypt` passes `n` whole blocks at `data` and the
            // scratch space, which, the chaining value and the schedule are
            // separate valid objects of the sizes of the signature. The
            // dispatcher calls only an implementation the CPU has the
            // features of.
            unsafe { vg_aes_cbc_encrypt_auto(&self.schedule, self.rounds, iv, data, n, scratch) }
        })
    }

    /// Decrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        self.crypt(buffer, |data, n, scratch| {
            // SAFETY: as in `encrypt`.
            unsafe { vg_aes_cbc_decrypt_auto(&self.schedule, self.rounds, iv, data, n, scratch) }
        })
    }

    /// Calls `f` with the whole blocks of `buffer` (their address and
    /// number) and a scratch space, which it then wipes, or returns an error
    /// without calling it if the buffer's length is not a multiple of 16.
    fn crypt(
        &self,
        buffer: &mut [u8],
        f: impl FnOnce(*mut [u8; 16], usize, &mut [u64; 272]),
    ) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        let mut scratch = [0; 272];
        f(buffer.as_mut_ptr().cast(), buffer.len() / 16, &mut scratch);
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
