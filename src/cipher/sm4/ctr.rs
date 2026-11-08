//! SM4-CTR (SP 800-38A §6.5, with SM4 as in GB/T 32907-2016, transcribed in
//! draft-ribose-cfrg-sm4-10), in place, incrementing the whole counter block as
//! a 128-bit big-endian number modulo `2¹²⁸` (Appendix B.1, as OpenSSL's
//! SM4-CTR does).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::sm4::vg_sm4_expand_key_auto;
use crate::arch::dispatch::sm4_ctr::{vg_sm4_ctr_auto, vg_sm4_ctr_final_auto};
use crate::error::IncompleteBlock;
use crate::zeroize::zeroize;

/// An expanded SM4 key.
struct Key {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: CacheAligned<[u8; 128]>,
}

/// SM4-CTR of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the next counter block; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The whole counter block is incremented, as a 128-bit big-endian number
/// modulo `2¹²⁸` (SP 800-38A Appendix B.1, as OpenSSL's SM4-CTR does). A
/// counter block must never be used twice with the same key (Appendix B.2).
pub struct Sm4Ctr {
    key: Key,
    /// The counter block to continue from.
    counter: [u8; 16],
}

impl Sm4Ctr {
    /// Expands a 16-byte key, to process a message from the counter block
    /// `ctr`.
    pub fn new(key: &[u8; 16], ctr: &[u8; 16]) -> Self {
        Self {
            key: Key::new(key),
            counter: *ctr,
        }
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
    /// Expands a 16-byte key.
    fn new(key: &[u8; 16]) -> Self {
        let mut schedule = CacheAligned([0; 128]);
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe {
            vg_sm4_expand_key_auto(key, &mut schedule.0);
        }
        Self { schedule }
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
            // SAFETY: as for `crypt`, with `rest` valid for `len` bytes.
            unsafe { vg_sm4_ctr_final_auto(&self.schedule.0, ctr, rest.as_mut_ptr(), rest.len()) };
        }
    }

    /// CTR of whole blocks.
    fn crypt(&self, ctr: &mut [u8; 16], blocks: &mut [u8]) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `ctr` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_sm4_ctr_auto(
                &self.schedule.0,
                ctr,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            );
        }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
