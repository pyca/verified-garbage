//! SEED-CBC (SP 800-38A §6.2, with SEED as in RFC 4269), in place and
//! without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_seed_expand_key` (contract `VG.Spec.Seed.expandKeyContract`) writes
//! the key schedule, and `vg_seed_cbc_encrypt` and `vg_seed_cbc_decrypt`
//! (`VG.Spec.Seed.cbcEncryptContract`, `cbcDecryptContract`) replace each
//! block with its CBC encryption or decryption from the chaining value at
//! `iv`, in constant time: their timing depends on none of the key, the
//! chaining value and the data. Both are the modes' generic CBC over the
//! batch of sixteen blocks of `vg_seed_ecb_encrypt` and `vg_seed_ecb_decrypt`:
//! decryption deciphers sixteen blocks at a time, encryption one. This module
//! checks the lengths, holds the key schedule and keeps the chaining value to
//! continue from: the last ciphertext block.

#![cfg(target_arch = "x86_64")]

use crate::arch::seed::vg_seed_expand_key;
use crate::arch::seed_cbc::{vg_seed_cbc_decrypt, vg_seed_cbc_encrypt};
use crate::zeroize::zeroize;

/// Why a SEED-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

/// An expanded SEED key for CBC encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct SeedCbc {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: [u8; 128],
}

impl SeedCbc {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let key: &[u8; 16] = key.try_into().map_err(|_| Error::InvalidKeyLength)?;
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe { vg_seed_expand_key(key, &mut schedule) };
        Ok(Self { schedule })
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
        // SAFETY: the buffer holds `len / 16` whole blocks, and it, the
        // chaining value and the schedule are separate valid objects of the
        // sizes of the signature, none of them on the callee's stack. The
        // function zeroes its working space on its own stack before
        // returning.
        unsafe {
            vg_seed_cbc_encrypt(
                &self.schedule,
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
            vg_seed_cbc_decrypt(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
            );
        }
        *iv = next;
        Ok(())
    }
}

impl Drop for SeedCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
