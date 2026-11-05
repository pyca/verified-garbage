//! SM4-OFB (SP 800-38A §6.4, with SM4 as in GB/T 32907-2016, transcribed in
//! draft-ribose-cfrg-sm4-10), in place.
//!
//! The IV must be unique to each message under a key (SP 800-38A Appendix C).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::sm4::vg_sm4_expand_key;
use crate::arch::sm4_ofb::vg_sm4_ofb;
use crate::error::IncompleteBlock;
use crate::zeroize::zeroize;

/// An expanded SM4 key.
struct Key {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: [u8; 128],
}

/// SM4-OFB of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last output block of the call before; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
pub struct Sm4Ofb {
    key: Key,
    /// The block to continue from: the IV, then the last output block.
    iv: [u8; 16],
}

impl Sm4Ofb {
    /// Expands a 16-byte key, to process a message from `iv`.
    pub fn new(key: &[u8; 16], iv: &[u8; 16]) -> Self {
        Self {
            key: Key::new(key),
            iv: *iv,
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
        self.key.apply_keystream(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts or decrypts (the same operation) the rest of the message in
    /// place, of any length: its whole blocks, then a partial last block if
    /// there is one (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`).
    pub fn apply_keystream_final(mut self, buffer: &mut [u8]) {
        self.key.apply_keystream(&mut self.iv, buffer);
    }
}

impl Drop for Sm4Ofb {
    /// Wipes the block to continue from, an output block: keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16-byte key.
    fn new(key: &[u8; 16]) -> Self {
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_sm4_expand_key(key, &mut schedule) };
        Self { schedule }
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of 16 bytes must end the message.
    fn apply_keystream(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(iv, blocks);
        if !rest.is_empty() {
            // The next output block, as OFB of a zero block, XORed into the
            // last bytes.
            let mut last = [0; 16];
            last[..rest.len()].copy_from_slice(rest);
            self.crypt(iv, &mut last);
            rest.copy_from_slice(&last[..rest.len()]);
            zeroize(&mut last);
        }
    }

    /// OFB of whole blocks.
    fn crypt(&self, iv: &mut [u8; 16], blocks: &mut [u8]) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_sm4_ofb(
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
