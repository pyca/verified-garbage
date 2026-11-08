//! AES-CFB128 (SP 800-38A §6.3, with 128-bit segments) with 128-, 192- and
//! 256-bit keys, in place.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::aes::vg_aes_expand_key_auto;
use crate::arch::dispatch::aes_cfb::{
    vg_aes_cfb128_decrypt_auto, vg_aes_cfb128_decrypt_final_auto, vg_aes_cfb128_encrypt_auto,
    vg_aes_cfb128_encrypt_final_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded AES key.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: CacheAligned<[u8; 240]>,
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

/// An AES-CFB128 encryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb128Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCfb128Encryptor {
    /// Expands a 16-, 24- or 32-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
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
        self.key.encrypt_final(&mut self.iv, buffer);
    }
}

impl Drop for AesCfb128Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// An AES-CFB128 decryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb128Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCfb128Decryptor {
    /// Expands a 16-, 24- or 32-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
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
        self.key.decrypt_final(&mut self.iv, buffer);
    }
}

impl Drop for AesCfb128Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 240]);
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature. The
        // dispatcher calls only an implementation the CPU has the features of.
        unsafe { vg_aes_expand_key_auto(key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
        })
    }

    /// Encrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, true);
    }

    /// Decrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.blocks(iv, buffer, false);
    }

    /// Encrypts the rest of a message, of any length, in place: its whole
    /// blocks with `encrypt`, then the bytes after them, fewer than 16, with
    /// the final function, from the IV the whole blocks leave.
    fn encrypt_final(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.encrypt(iv, blocks);
        if !rest.is_empty() {
            self.final_(iv, rest, true);
        }
    }

    /// Decrypts the rest of a message, of any length, in place: its whole
    /// blocks with `decrypt` (which may decrypt several at once), then the
    /// bytes after them, fewer than 16, with the final function, from the IV
    /// the whole blocks leave.
    fn decrypt_final(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.decrypt(iv, blocks);
        if !rest.is_empty() {
            self.final_(iv, rest, false);
        }
    }

    /// The final function that encrypts (`encrypt`) or decrypts, on the rest
    /// of a message, of any length: it
    /// replaces `iv` with the last ciphertext block, or, after a partial last
    /// segment, with keystream, which the caller wipes.
    fn final_(&self, iv: &mut [u8; 16], buffer: &mut [u8], encrypt: bool) {
        let mut scratch = CacheAligned([0; 272]);
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `buffer` is valid for `len` bytes, and it, the block at
        // `iv`, the schedule and the scratch space are separate valid objects
        // of the sizes of the signature. The dispatcher calls only an
        // implementation the CPU has the features of.
        unsafe {
            if encrypt {
                vg_aes_cfb128_encrypt_final_auto(
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch.0,
                );
            } else {
                vg_aes_cfb128_decrypt_final_auto(
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    buffer.as_mut_ptr(),
                    buffer.len(),
                    &mut scratch.0,
                );
            }
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch.0);
    }

    /// Encrypts (`encrypt`) or decrypts whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], encrypt: bool) {
        let mut scratch = CacheAligned([0; 272]);
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. The dispatcher calls only an implementation the CPU has
        // the features of.
        unsafe {
            if encrypt {
                vg_aes_cfb128_encrypt_auto(
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    blocks.as_mut_ptr().cast(),
                    blocks.len() / 16,
                    &mut scratch.0,
                );
            } else {
                vg_aes_cfb128_decrypt_auto(
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    blocks.as_mut_ptr().cast(),
                    blocks.len() / 16,
                    &mut scratch.0,
                );
            }
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch.0);
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
