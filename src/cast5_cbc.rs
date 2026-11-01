//! CAST5-CBC (SP 800-38A §6.2, with CAST5 as in RFC 2144), in place and
//! without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_cast5_expand_key` (contract `VG.Spec.Cast5.expandKeyContract`) writes
//! the subkeys, and `vg_cast5_cbc_encrypt_chained` and
//! `vg_cast5_cbc_decrypt_chained` (`VG.Spec.Cast5.cbcEncryptChainedContract`,
//! `cbcDecryptChainedContract`) replace each block with its CBC encryption or
//! decryption from the chaining value at `iv`, and the chaining value with the
//! one to continue from, the last ciphertext block, in constant time: their
//! timing depends on none of the key, the chaining value and the data. This
//! module checks the lengths and holds the subkeys.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::cast5_cbc::{vg_cast5_cbc_decrypt_chained, vg_cast5_cbc_encrypt_chained};
use crate::cast5_ecb::Cast5Ecb;
pub use crate::cast5_ecb::Error;

/// An expanded CAST5 key for CBC encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 8-byte blocks.
/// The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct Cast5Cbc {
    key: Cast5Ecb,
}

impl Cast5Cbc {
    /// Expands a key of 5 to 16 bytes for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: Cast5Ecb::new(key)?,
        })
    }

    /// Encrypts whole 8-byte blocks in place, chained from `iv`, and replaces
    /// `iv` with the last ciphertext block (leaving it unchanged for empty
    /// input), so that a further call continues the message. Returns an
    /// error without changing anything if the buffer's length is not a
    /// multiple of 8.
    pub fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; the buffer holds `len / 8` whole
        // blocks, and it, the chaining value (which the function reads and
        // replaces) and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack. The function
        // zeroes its working space on its own stack before returning.
        unsafe {
            vg_cast5_cbc_encrypt_chained(
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
    /// input), so that a further call continues the message. Returns an
    /// error without changing anything if the buffer's length is not a
    /// multiple of 8.
    pub fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(8) {
            return Err(Error::IncompleteBlock);
        }
        // SAFETY: as in `encrypt`.
        unsafe {
            vg_cast5_cbc_decrypt_chained(
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
