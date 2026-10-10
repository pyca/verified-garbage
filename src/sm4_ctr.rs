//! SM4-CTR (SP 800-38A §6.5, with SM4 as in draft-ribose-cfrg-sm4-10 §7.1),
//! in place, with the standard incrementing function of Appendix B.1 on the
//! whole counter block (a 128-bit big-endian number, wrapping modulo `2¹²⁸`,
//! as OpenSSL's SM4-CTR).
//!
//! The block cipher work is verified assembly: `vg_sm4_expand_key`
//! (contract `VG.Spec.Sm4.expandKeyContract`) writes the key schedule, and
//! `vg_sm4_ctr` (`VG.Spec.Sm4.ctrContract`) XORs whole blocks with the
//! output blocks `Oⱼ = CIPH_K(Tⱼ)` from the counter block at `ctr`, which it
//! replaces with the counter block to continue from, in constant time: its
//! timing depends on none of the key, the counter block and the data. It
//! encrypts sixteen counter blocks at a time, bitsliced in general-purpose
//! registers, with no table lookups. This module holds the key schedule and
//! handles a partial last block (§6.5, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): CTR of the
//! last bytes padded to a block XORs them with the first bytes of the next
//! output block.
//!
//! The caller chooses the initial counter block, and must never use a
//! counter block twice with the same key (Appendix B.2).

#![cfg(target_arch = "x86_64")]

use crate::arch::sm4::vg_sm4_expand_key;
use crate::arch::sm4_ctr::vg_sm4_ctr;
use crate::zeroize::zeroize;

/// An expanded SM4 key for CTR, whose encryption and decryption are the same
/// operation.
pub struct Sm4Ctr {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: [u8; 128],
}

impl Sm4Ctr {
    /// Expands a 16-byte key.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_sm4_expand_key(key, &mut schedule);
        }
        Self { schedule }
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// counter block `ctr`, which it replaces with the counter block after
    /// the last one used: `ctr` plus the number of blocks (counting a partial
    /// last one), modulo `2¹²⁸` (unchanged for empty input). A message may
    /// be processed in pieces of whole blocks, each continuing from the `ctr`
    /// the last left; a piece whose length is not a multiple of 16 bytes
    /// must end the message.
    pub fn apply_keystream(&self, ctr: &mut [u8; 16], buffer: &mut [u8]) {
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
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `ctr` and the schedule are
        // separate valid objects of the sizes of the signature, none of
        // them on the callee's stack. The function zeroes its working space
        // on its own stack before returning.
        unsafe {
            vg_sm4_ctr(
                &self.schedule,
                ctr,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            );
        }
    }
}

impl Drop for Sm4Ctr {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
