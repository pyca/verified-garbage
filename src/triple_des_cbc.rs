//! Triple DES-CBC (SP 800-38A §6.2, with Triple DES as in FIPS 46-3), in
//! place and without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_triple_des_expand_key` (contract `VG.Spec.TripleDes.expandKeyContract`)
//! writes the key schedule, and `vg_triple_des_cbc_encrypt_chained` and
//! `vg_triple_des_cbc_decrypt_chained`
//! (`VG.Spec.TripleDes.cbcEncryptChainedContract`, `cbcDecryptChainedContract`)
//! replace each block with its CBC encryption or decryption from the chaining
//! value at `iv`, and the chaining value with the one to continue from, the
//! last ciphertext block, in constant time: their timing depends on none of the
//! key, the chaining value and the data. This module checks the lengths and
//! holds the key schedule.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_cbc::{
    vg_triple_des_cbc_decrypt_chained, vg_triple_des_cbc_encrypt_chained,
};
use crate::zeroize::zeroize;

/// Why a Triple DES-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 or 24 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid Triple DES key length",
        IncompleteBlock => "Triple DES-CBC input is not a whole number of blocks",
    }
}

/// An expanded Triple DES key for CBC encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored. No padding is
/// added or removed: each operation takes whole eight-byte blocks. The
/// chaining value is updated in place, so that a message may be processed
/// in pieces, each continuing from the last.
pub struct TripleDesCbc {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

impl TripleDesCbc {
    /// Expands a 16- or 24-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24) {
            return Err(Error::InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
        unsafe {
            vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
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
            vg_triple_des_cbc_encrypt_chained(
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
            vg_triple_des_cbc_decrypt_chained(
                &self.schedule,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for TripleDesCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
