//! IDEA-CBC (SP 800-38A §6.2, with IDEA as in Lai, 1992), in place and
//! without padding.
//!
//! The block cipher work and the chaining are verified assembly:
//! `vg_idea_expand_key` and `vg_idea_invert_key` (contracts
//! `VG.Spec.Idea.expandKeyContract`, `invertKeyContract`) write the encryption
//! and decryption subkeys, and `vg_idea_cbc_encrypt_chained` and
//! `vg_idea_cbc_decrypt_chained` (`VG.Spec.Idea.cbcEncryptChainedContract`,
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

use crate::arch::idea::{vg_idea_expand_key, vg_idea_invert_key};
use crate::arch::idea_cbc::{vg_idea_cbc_decrypt_chained, vg_idea_cbc_encrypt_chained};
use crate::zeroize::zeroize;

/// Why an IDEA-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key does not contain 16 bytes.
    InvalidKeyLength,
    /// The input length is not a multiple of eight bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid IDEA key length",
        IncompleteBlock => "IDEA-CBC input is not a whole number of blocks",
    }
}

/// An expanded IDEA key for CBC encryption and decryption: its encryption
/// and decryption subkeys.
///
/// No padding is added or removed: each operation takes whole eight-byte
/// blocks. The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct IdeaCbc {
    encrypt: [u8; 104],
    decrypt: [u8; 104],
}

impl IdeaCbc {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        let key: &[u8; 16] = key.try_into().map_err(|_| Error::InvalidKeyLength)?;
        let mut encrypt = [0; 104];
        let mut decrypt = [0; 104];
        // SAFETY: the key and both schedules are separate valid buffers of
        // the required sizes.
        unsafe {
            vg_idea_expand_key(key, &mut encrypt);
            vg_idea_invert_key(&encrypt, &mut decrypt);
        }
        Ok(Self { encrypt, decrypt })
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
        // the callee's stack.
        unsafe {
            vg_idea_cbc_encrypt_chained(
                &self.encrypt,
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
            vg_idea_cbc_decrypt_chained(
                &self.decrypt,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 8,
            );
        }
        Ok(())
    }
}

impl Drop for IdeaCbc {
    fn drop(&mut self) {
        zeroize(&mut self.encrypt);
        zeroize(&mut self.decrypt);
    }
}
