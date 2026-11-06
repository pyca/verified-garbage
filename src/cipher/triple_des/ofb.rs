//! Triple DES-OFB (SP 800-38A §6.4, with Triple DES as in FIPS 46-3), in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_ofb::vg_triple_des_ofb;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Triple DES key.
struct Key {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

/// Triple DES-OFB of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 8-byte blocks and continues the
/// message from the last output block of the call before; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The IV must be unique to each message under a key (SP 800-38A Appendix C).
pub struct TripleDesOfb {
    key: Key,
    /// The block to continue from: the IV, then the last output block.
    iv: [u8; 8],
}

impl TripleDesOfb {
    /// Expands a 16- or 24-byte key (a 24-byte key encodes K1, K2 and K3; a
    /// 16-byte key, K1 and K2, with K3 repeating K1; each byte's parity bit
    /// is ignored), to process a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts or decrypts (the same operation) whole 8-byte blocks in
    /// place, continuing the message. Returns an error without changing
    /// anything if the buffer's length is not a multiple of 8: only
    /// [`apply_keystream_final`](Self::apply_keystream_final) takes a partial
    /// last block.
    pub fn apply_keystream(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(8) {
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

impl Drop for TripleDesOfb {
    /// Wipes the block to continue from, an output block: keystream.
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
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe { vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of eight bytes must end the message.
    fn apply_keystream(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        let whole = buffer.len() / 8 * 8;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(iv, blocks);
        if !rest.is_empty() {
            // The last bytes, padded to a block: OFB XORs them with the first
            // bytes of the next output block.
            let mut last = [0; 8];
            last[..rest.len()].copy_from_slice(rest);
            self.crypt(iv, &mut last);
            rest.copy_from_slice(&last[..rest.len()]);
            zeroize(&mut last);
        }
    }

    /// OFB of whole blocks.
    fn crypt(&self, iv: &mut [u8; 8], blocks: &mut [u8]) {
        // SAFETY: `blocks` holds `len / 8` whole blocks (its length is a
        // multiple of 8), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_triple_des_ofb(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
