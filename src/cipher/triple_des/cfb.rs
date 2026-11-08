//! Triple DES-CFB64 (SP 800-38A §6.3 with 64-bit segments, with Triple DES as
//! in FIPS 46-3), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::triple_des::vg_triple_des_expand_key_auto;
use crate::arch::dispatch::triple_des_cfb::vg_triple_des_cfb64_decrypt_auto;
use crate::arch::dispatch::triple_des_cfb::{
    vg_triple_des_cfb64_decrypt_final_auto, vg_triple_des_cfb64_encrypt_auto,
    vg_triple_des_cfb64_encrypt_final_auto,
};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Triple DES key.
struct Key {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: CacheAligned<[u8; 384]>,
}

/// A Triple DES-CFB64 encryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCfb64Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl TripleDesCfb64Encryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit
    /// is ignored), to encrypt a message from `iv`.
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
        self.key.blocks(&mut self.iv, buffer, false);
        Ok(())
    }

    /// Encrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn encrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(&mut self.iv, buffer, false);
    }
}

impl Drop for TripleDesCfb64Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// A Triple DES-CFB64 decryption of one message.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct TripleDesCfb64Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 8],
}

impl TripleDesCfb64Decryptor {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit
    /// is ignored), to decrypt a message from `iv`.
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
        self.key.blocks(&mut self.iv, buffer, true);
        Ok(())
    }

    /// Decrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Pₙ* = Cₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn decrypt_final(mut self, buffer: &mut [u8]) {
        self.key.last(&mut self.iv, buffer, true);
    }
}

impl Drop for TripleDesCfb64Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16- or 24-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = CacheAligned([0; 384]);
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe { vg_triple_des_expand_key_auto(key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self { schedule })
    }

    /// Decrypts (if `decrypt`) or encrypts the whole blocks of `blocks` in
    /// place, from the block `iv`, which it replaces with the last ciphertext
    /// block (unchanged for empty input).
    fn blocks(&self, iv: &mut [u8; 8], blocks: &mut [u8], decrypt: bool) {
        let n = blocks.len() / 8;
        let data = blocks.as_mut_ptr().cast();
        // SAFETY: `blocks` holds `n` whole blocks (its length is a multiple
        // of 8), and it, the block at `iv` and the schedule are separate valid
        // objects of the sizes of the signature, none of them on the callee's
        // stack. The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe {
            if decrypt {
                vg_triple_des_cfb64_decrypt_auto(&self.schedule.0, iv, data, n)
            } else {
                vg_triple_des_cfb64_encrypt_auto(&self.schedule.0, iv, data, n)
            }
        };
    }

    /// The rest of a message, of any length, decrypted (if `decrypt`) or
    /// encrypted: its whole blocks (which, decrypting, may decrypt several at
    /// once), then the bytes after them, fewer than 8, with the final function
    /// of the same direction, from the IV the whole blocks leave. It replaces
    /// `iv` with the last ciphertext block, or, after a partial last segment,
    /// with keystream, which the caller wipes.
    fn last(&self, iv: &mut [u8; 8], buffer: &mut [u8], decrypt: bool) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 8 * 8);
        self.blocks(iv, blocks, decrypt);
        if !rest.is_empty() {
            let f = if decrypt {
                vg_triple_des_cfb64_decrypt_final_auto
            } else {
                vg_triple_des_cfb64_encrypt_final_auto
            };
            // SAFETY: `rest` is valid for `len` bytes, and it, the block at
            // `iv` and the schedule are separate valid objects of the sizes of
            // the signature, none of them on the callee's stack.
            unsafe { f(&self.schedule.0, iv, rest.as_mut_ptr(), rest.len()) };
        }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
