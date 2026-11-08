//! AES-CTR (SP 800-38A §6.5) with 128-, 192- and 256-bit keys, in place,
//! incrementing the whole counter block as a 128-bit big-endian number modulo
//! `2¹²⁸` (Appendix B.1, as OpenSSL's and aws-lc's AES-CTR do).

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
use crate::arch::dispatch::aes_ctr::{vg_aes_ctr_auto, vg_aes_ctr_final_auto};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded AES key.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: CacheAligned<[u8; 240]>,
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
}

/// AES-CTR of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the next counter block; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The whole counter block is incremented, as a 128-bit big-endian number
/// modulo `2¹²⁸` (SP 800-38A Appendix B.1, as OpenSSL's and aws-lc's AES-CTR
/// do). A counter block must never be used twice with the same key (Appendix
/// B.2). The timing may depend on the counter block's last four bytes (the
/// 32-bit counter, which OpenSSL, BoringSSL and aws-lc also treat as public),
/// but not on the rest of it, the key or the data.
pub struct AesCtr {
    key: Key,
    /// The counter block to continue from.
    counter: [u8; 16],
}

impl AesCtr {
    /// Expands a 16-, 24- or 32-byte key, to process a message from the
    /// counter block `ctr`.
    pub fn new(key: &[u8], ctr: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            counter: *ctr,
        })
    }

    /// Encrypts or decrypts (the same operation) whole 16-byte blocks in
    /// place, continuing the message. Returns an error without changing
    /// anything if the buffer's length is not a multiple of 16: only
    /// [`apply_keystream_final`](Self::apply_keystream_final) takes a partial
    /// last block.
    pub fn apply_keystream(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.apply_keystream(&mut self.counter, buffer);
        Ok(())
    }

    /// Encrypts or decrypts (the same operation) the rest of the message in
    /// place, of any length: its whole blocks, then a partial last block if
    /// there is one (§6.5, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`).
    pub fn apply_keystream_final(mut self, buffer: &mut [u8]) {
        self.key.apply_keystream_final(&mut self.counter, buffer);
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

    /// Encrypts or decrypts (the same operation) the whole blocks of
    /// `buffer` in place, from the counter block `ctr`, which it replaces
    /// with the counter block after the last one used: `ctr` plus the number
    /// of blocks, modulo `2¹²⁸` (unchanged for empty input).
    fn apply_keystream(&self, ctr: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(ctr, buffer);
    }

    /// Encrypts or decrypts (the same operation) the rest of a message, of
    /// any length, in place: its whole blocks with `crypt`, then the bytes
    /// after them, fewer than 16, with the final function, from the counter
    /// block the whole blocks leave in `ctr`, which it replaces with the
    /// next one.
    fn apply_keystream_final(&self, ctr: &mut [u8; 16], buffer: &mut [u8]) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.crypt(ctr, blocks);
        if !rest.is_empty() {
            let mut scratch = CacheAligned([0; 272]);
            // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
            // schedule; `rest` is valid for `len` bytes, and it, the block at
            // `ctr`, the schedule and the scratch space are separate valid
            // objects of the sizes of the signature. The dispatcher calls only
            // an implementation the CPU has the features of.
            unsafe {
                vg_aes_ctr_final_auto(
                    &self.schedule.0,
                    self.rounds,
                    ctr,
                    rest.as_mut_ptr(),
                    rest.len(),
                    &mut scratch.0,
                );
            }
            // The scratch space may hold the key schedule, the data and our
            // caller's registers.
            zeroize(&mut scratch.0);
        }
    }

    /// CTR of whole blocks.
    fn crypt(&self, ctr: &mut [u8; 16], blocks: &mut [u8]) {
        let mut scratch = CacheAligned([0; 272]);
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `ctr`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. The dispatcher calls only an implementation the CPU has
        // the features of.
        unsafe {
            vg_aes_ctr_auto(
                &self.schedule.0,
                self.rounds,
                ctr,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
                &mut scratch.0,
            );
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
