//! Camellia-CTR (SP 800-38A §6.5, with Camellia as in RFC 3713), in place,
//! incrementing the whole counter block as a 128-bit big-endian number modulo
//! `2¹²⁸` (Appendix B.1, as OpenSSL's Camellia-CTR does; RFC 5528's counter
//! blocks are such blocks for messages of fewer than `2³²` blocks).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_ctr::vg_camellia_ctr;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Camellia key.
struct Key {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    rounds: usize,
}

/// Camellia-CTR of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the next counter block; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The whole counter block is incremented, as a 128-bit big-endian number
/// modulo `2¹²⁸` (SP 800-38A Appendix B.1, as OpenSSL's Camellia-CTR does; RFC
/// 5528's counter blocks are such blocks for messages of fewer than `2³²`
/// blocks). A counter block must never be used twice with the same key
/// (Appendix B.2).
pub struct CamelliaCtr {
    key: Key,
    /// The counter block to continue from.
    counter: [u8; 16],
}

impl CamelliaCtr {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to process a message from the counter block `ctr`.
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
        self.key.apply_keystream(&mut self.counter, buffer);
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe {
            vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule);
        }
        Ok(Self { schedule, rounds })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// counter block `ctr`, which it replaces with the counter block after
    /// the last one used: `ctr` plus the number of blocks (counting a partial
    /// last one), modulo `2¹²⁸` (unchanged for empty input). A message may
    /// be processed in pieces of whole blocks, each continuing from the `ctr`
    /// the last left; a piece whose length is not a multiple of 16 bytes
    /// must end the message.
    fn apply_keystream(&self, ctr: &mut [u8; 16], buffer: &mut [u8]) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(ctr, blocks);
        if !rest.is_empty() {
            // The last bytes, padded to a block: CTR XORs them with the first
            // bytes of the next output block.
            let mut last = [0; 16];
            last[..rest.len()].copy_from_slice(rest);
            self.crypt(ctr, &mut last);
            rest.copy_from_slice(&last[..rest.len()]);
            zeroize(&mut last);
        }
    }

    /// CTR of whole blocks.
    fn crypt(&self, ctr: &mut [u8; 16], blocks: &mut [u8]) {
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. `blocks` holds `len / 16` whole
        // blocks (its length is a multiple of 16), and it, the block at `ctr`
        // and the schedule are separate valid objects of the sizes of the
        // signature, none of them on the callee's stack.
        unsafe {
            vg_camellia_ctr(
                &self.schedule,
                self.rounds,
                ctr,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            );
        }
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
