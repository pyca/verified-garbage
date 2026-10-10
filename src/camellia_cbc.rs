//! Camellia-CBC (SP 800-38A §6.2, with Camellia as in RFC 3713) with 128-,
//! 192- and 256-bit keys, in place and without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_camellia_expand_key` (contract `VG.Spec.Camellia.expandKeyContract`)
//! writes the subkeys, and `vg_camellia_cbc_encrypt` and
//! `vg_camellia_cbc_decrypt` (`VG.Spec.Camellia.cbcEncryptContract`,
//! `cbcDecryptContract`) replace each block with its CBC encryption or
//! decryption from the chaining value at `iv`, in constant time: their
//! timing depends on none of the key, the chaining value and the data. Both
//! are the modes' generic CBC over Camellia's bitsliced ECB code, with the
//! S-boxes as Boolean circuits: decryption transforms eight blocks at a
//! time, and encryption, in which each block needs the one before, one block
//! at a time (in a batch of eight, so about eight times ECB's cost). This
//! module checks the lengths, holds the subkeys and keeps the chaining value
//! to continue from: the last ciphertext block.

#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_cbc::{vg_camellia_cbc_decrypt, vg_camellia_cbc_encrypt};
use crate::zeroize::zeroize;

/// Why a Camellia-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16, 24 or 32 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded Camellia key for CBC encryption and decryption.
///
/// Keys of 16 bytes use 18 rounds; keys of 24 or 32 bytes, 24. No padding is
/// added or removed: each operation takes whole 16-byte blocks. The chaining
/// value is updated in place, so that a message may be processed in pieces,
/// each continuing from the last.
pub struct CamelliaCbc {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    rounds: usize,
}

impl CamelliaCbc {
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

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. The buffer holds `len / 16` whole
        // blocks, and it, the chaining value and the schedule are separate
        // valid objects of the sizes of the signature, none of them on the
        // callee's stack. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_camellia_cbc_encrypt(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        if let Some(last) = buffer.rchunks_exact(16).next() {
            iv.copy_from_slice(last);
        }
        Ok(())
    }

    /// Decrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let mut next = *iv;
        if let Some(last) = buffer.rchunks_exact(16).next() {
            next.copy_from_slice(last);
        }
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_camellia_cbc_decrypt(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        *iv = next;
        Ok(())
    }
}

impl Drop for CamelliaCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
