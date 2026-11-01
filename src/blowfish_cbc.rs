//! Blowfish-CBC (SP 800-38A §6.2, with Blowfish as in Schneier, FSE 1994),
//! in place and without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_blowfish_expand_key` (contract `VG.Spec.Blowfish.expandKeyContract`)
//! writes the schedule, which serves both directions, and
//! `vg_blowfish_cbc_encrypt_chained` and `vg_blowfish_cbc_decrypt_chained`
//! (`VG.Spec.Blowfish.cbcEncryptChainedContract`, `cbcDecryptChainedContract`)
//! replace each block with its CBC encryption or decryption from the chaining
//! value at `iv`, and the chaining value with the one to continue from, the
//! last ciphertext block, in constant time: their timing depends on none of the
//! key, the chaining value and the data. This module checks the lengths and
//! holds the schedule.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::blowfish::vg_blowfish_expand_key;
use crate::arch::blowfish_cbc::{vg_blowfish_cbc_decrypt_chained, vg_blowfish_cbc_encrypt_chained};
use crate::zeroize::zeroize;

/// Why a Blowfish-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key length is outside 4..=56 bytes (32 to 448 bits).
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid Blowfish key length",
        IncompleteBlock => "Blowfish-CBC input is not a whole number of blocks",
    }
}

/// An expanded Blowfish key for CBC encryption and decryption, which use the
/// same schedule.
///
/// No padding is added or removed: each operation takes whole eight-byte
/// blocks. The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct BlowfishCbc {
    /// The schedule `vg_blowfish_expand_key` writes.
    schedule: [u8; 4168],
}

impl BlowfishCbc {
    /// Expands a key of 4..=56 bytes (32 to 448 bits) for use in either
    /// direction. Weak keys are accepted.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !(4..=56).contains(&key.len()) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 4168];
        // SAFETY: the key has a length in 4..=56; the key and the schedule
        // are separate valid objects of the lengths passed.
        unsafe { vg_blowfish_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts whole eight-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of eight.
    pub fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: the buffer holds `len / 8` whole blocks, and it, the chaining
        // value (which the function reads and replaces) and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_blowfish_cbc_encrypt_chained(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }

    /// Decrypts whole eight-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of eight.
    pub fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_blowfish_cbc_decrypt_chained(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for BlowfishCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
