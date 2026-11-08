//! Camellia-OFB (SP 800-38A §6.4, with Camellia as in RFC 3713) with 128-, 192-
//! and 256-bit keys, in place.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::camellia::vg_camellia_expand_key_auto;
use crate::arch::dispatch::camellia_ofb::{vg_camellia_ofb_auto, vg_camellia_ofb_final_auto};
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;

/// An expanded Camellia key.
struct Key {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: CacheAligned<[u8; 272]>,
    /// The number of rounds: 18 or 24.
    rounds: usize,
}

/// Camellia-OFB of one message, whose encryption and decryption are the
/// same operation.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last output block of the call before; the last,
/// [`apply_keystream_final`](Self::apply_keystream_final), takes the rest
/// of the message, of any length.
///
/// The IV must be unique to each message under a key (SP 800-38A Appendix C).
pub struct CamelliaOfb {
    key: Key,
    /// The block to continue from: the IV, then the last output block.
    iv: [u8; 16],
}

impl CamelliaOfb {
    /// Expands a 16-, 24- or 32-byte key (16-byte keys use 18 rounds; 24- and
    /// 32-byte keys, 24), to process a message from `iv`.
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

impl Drop for CamelliaOfb {
    /// Wipes the block to continue from, an output block: keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
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
        let mut schedule = CacheAligned([0; 272]);
        crate::dit::enter!(dit);
        // SAFETY: the key has a validated length; key and schedule are separate
        // valid buffers of the required sizes.
        unsafe { vg_camellia_expand_key_auto(dit, key.as_ptr(), key.len(), &mut schedule.0) };
        Ok(Self { schedule, rounds })
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
            unsafe {
                vg_camellia_ofb_final_auto(
                    dit,
                    &self.schedule.0,
                    self.rounds,
                    iv,
                    rest.as_mut_ptr(),
                    rest.len(),
                )
            };
        }
    }

    /// OFB of whole blocks.
    fn crypt(&self, dit: crate::dit::Dit<'_>, iv: &mut [u8; 16], blocks: &mut [u8]) {
        // SAFETY: `rounds` is 18 or 24 and the schedule holds that many rounds'
        // subkeys; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_camellia_ofb_auto(
                dit,
                &self.schedule.0,
                self.rounds,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule.0);
    }
}
