//! SEED-OFB (SP 800-38A §6.4, with SEED as in RFC 4269), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::seed::vg_seed_expand_key;
use crate::arch::seed_ofb::{vg_seed_ofb, vg_seed_ofb_final};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded SEED key.
struct Key {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: [u8; 128],
}

/// SEED-OFB of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last output block of the call before; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The IV must be unique to each message under a key (SP 800-38A Appendix C).
pub struct SeedOfb {
    key: Key,
    /// The block to continue from: the IV, then the last output block.
    iv: [u8; 16],
}

impl SeedOfb {
    /// Expands a 16-byte key, to process a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
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
        self.key.apply_keystream(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts or decrypts (the same operation) the rest of the message in
    /// place, of any length: its whole blocks, then a partial last block if
    /// there is one (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`).
    pub fn apply_keystream_final(mut self, buffer: &mut [u8]) {
        self.key.apply_keystream_final(&mut self.iv, buffer);
    }
}

impl Drop for SeedOfb {
    /// Wipes the block to continue from, an output block: keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key(dit, key, &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts or decrypts (the same operation) the whole blocks of
    /// `buffer` in place, from the block `iv`, which it replaces with the
    /// last output block (unchanged for empty input).
    fn apply_keystream(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        self.crypt(dit, iv, buffer);
    }

    /// Encrypts or decrypts (the same operation) the rest of a message, of
    /// any length, in place: its whole blocks with `crypt`, then the bytes
    /// after them, fewer than 16, with the final function, from the block
    /// the whole blocks leave in `iv`, which it replaces with the output
    /// block it used.
    fn apply_keystream_final(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.crypt(dit, iv, blocks);
        if !rest.is_empty() {
            // SAFETY: `rest` is valid for `len` bytes, and it, the block at
            // `iv` and the schedule are separate valid objects of the sizes of
            // the signature, none of them on the callee's stack.
            unsafe { vg_seed_ofb_final(dit, &self.schedule, iv, rest.as_mut_ptr(), rest.len()) };
        }
    }

    /// OFB of whole blocks.
    fn crypt(&self, dit: crate::dit::Dit<'_>, iv: &mut [u8; 16], blocks: &mut [u8]) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_seed_ofb(
                dit,
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
