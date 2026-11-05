//! Camellia-CBC (SP 800-38A §6.2, with Camellia as in RFC 3713) with 128-, 192-
//! and 256-bit keys, in place and without padding.
//!
//! The IV must be unpredictable (SP 800-38A Appendix C).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_cbc::{vg_camellia_cbc_decrypt_chained, vg_camellia_cbc_encrypt_chained};
use crate::zeroize::zeroize;

/// Why a Camellia-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16, 24 or 32 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid Camellia key length",
        IncompleteBlock => "Camellia-CBC input is not a whole number of blocks",
    }
}

/// An expanded Camellia key, which serves both directions.
struct Key {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    rounds: usize,
}

/// A Camellia-CBC encryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// encrypted in pieces.
pub struct CamelliaCbcEncryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl CamelliaCbcEncryptor {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), Error> {
        self.key.encrypt(&mut self.iv, buffer)
    }
}

/// A Camellia-CBC decryption of one message, without padding.
///
/// Each call takes whole 16-byte blocks and continues the message from the
/// last ciphertext block of the call before, so that a message may be
/// decrypted in pieces.
pub struct CamelliaCbcDecryptor {
    key: Key,
    /// The chaining value: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl CamelliaCbcDecryptor {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, Error> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), Error> {
        self.key.decrypt(&mut self.iv, buffer)
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, Error> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(Error::InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule, rounds })
    }

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input).
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer holds `len / 16` whole
        // blocks, and it, the chaining value (which the function reads and
        // replaces) and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack.
        unsafe {
            vg_camellia_cbc_encrypt_chained(
                &self.schedule,
                self.rounds,
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
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_camellia_cbc_decrypt_chained(
                &self.schedule,
                self.rounds,
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
        zeroize(&mut self.schedule);
    }
}
