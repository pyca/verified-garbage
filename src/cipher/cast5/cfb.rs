//! CAST5-CFB64 (SP 800-38A §6.3 with 64-bit segments, with CAST5 as in RFC
//! 2144), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use super::Cast5Ecb;
use crate::arch::dispatch::cast5_cfb::{
    vg_cast5_cfb64_decrypt_auto, vg_cast5_cfb64_decrypt_final_auto, vg_cast5_cfb64_encrypt_auto,
    vg_cast5_cfb64_encrypt_final_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded CAST5 key.
struct Key {
    key: Cast5Ecb,
}

/// A CAST5-CFB64 encryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Cast5Cfb64Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5Cfb64Encryptor {
    /// Expands a key of 5 to 16 bytes, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        self.key.encrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn encrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(&mut self.iv, buffer, true);
    }
}

impl Drop for Cast5Cfb64Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A CAST5-CFB64 decryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct Cast5Cfb64Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl Cast5Cfb64Decryptor {
    /// Expands a key of 5 to 16 bytes, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 8-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 8: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
            return Err(IncompleteBlock);
        }
        self.key.decrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Decrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Pₙ* = Cₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn decrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(&mut self.iv, buffer, false);
    }
}

impl Drop for Cast5Cfb64Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a key of 5 to 16 bytes.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Cast5Ecb::new(key).map_err(|_| InvalidKeyLength)?,
        })
    }

    /// Encrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.blocks(iv, buffer, true);
    }

    /// Decrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.blocks(iv, buffer, false);
    }

    /// Encrypts (`encrypt`) or decrypts whole blocks.
    fn blocks(&self, iv: &mut [u8; 8], blocks: &mut [u8], encrypt: bool) {
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; `blocks` holds `len / 8` whole
        // blocks, and it, the block at `iv` and the schedule are separate valid
        // objects of the sizes of the signature, none of them on the callee's
        // stack.
        unsafe {
            if encrypt {
                vg_cast5_cfb64_encrypt_auto(
                    self.key.schedule(),
                    self.key.rounds(),
                    iv,
                    blocks.as_mut_ptr().cast(),
                    blocks.len() / 8,
                )
            } else {
                vg_cast5_cfb64_decrypt_auto(
                    self.key.schedule(),
                    self.key.rounds(),
                    iv,
                    blocks.as_mut_ptr().cast(),
                    blocks.len() / 8,
                )
            }
        };
    }

    /// Encrypts (`encrypt`) or decrypts the rest of a message, of any
    /// length, in place: its whole blocks (which, decrypting, may be
    /// decrypted several at once), then the bytes after them, fewer than 8,
    /// with the final function, from the IV the whole blocks leave.
    fn last(&self, iv: &mut [u8; 8], buffer: &mut [u8], encrypt: bool) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 8 * 8);
        self.blocks(iv, blocks, encrypt);
        if !rest.is_empty() {
            self.final_(iv, rest, encrypt);
        }
    }

    /// The final function that encrypts (`encrypt`) or decrypts, on the rest
    /// of a message, of any length: it replaces `iv` with the last ciphertext
    /// block, or, after a partial last segment, with keystream, which the
    /// caller wipes.
    fn final_(&self, iv: &mut [u8; 8], buffer: &mut [u8], encrypt: bool) {
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; `buffer` is valid for `len` bytes,
        // and it, the block at `iv` and the schedule are separate valid
        // objects of the sizes of the signature, none of them on the callee's
        // stack.
        unsafe {
            if encrypt {
                vg_cast5_cfb64_encrypt_final_auto(
                    self.key.schedule(),
                    self.key.rounds(),
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                )
            } else {
                vg_cast5_cfb64_decrypt_final_auto(
                    self.key.schedule(),
                    self.key.rounds(),
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                )
            }
        };
    }
}
