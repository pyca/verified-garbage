//! Camellia-CTR (SP 800-38A §6.5, with Camellia as in RFC 3713), in place,
//! with the standard incrementing function of Appendix B.1 on the whole
//! counter block (a 128-bit big-endian number, wrapping modulo `2¹²⁸`, as
//! OpenSSL's Camellia-CTR; RFC 5528's counter blocks, whose last 32 bits
//! count from 1, are such blocks for messages of fewer than `2³²` blocks).
//!
//! The block cipher work is verified assembly: `vg_camellia_expand_key`
//! (contract `VG.Spec.Camellia.expandKeyContract`) writes the subkeys, and
//! `vg_camellia_ctr` (`VG.Spec.Camellia.ctrContract`) XORs whole blocks with
//! the output blocks `Oⱼ = CIPH_K(Tⱼ)` from the counter block at `ctr`,
//! which it replaces with the counter block to continue from, in constant
//! time: its timing depends on none of the key, the counter block and the
//! data. It encrypts eight counter blocks at a time, bitsliced in
//! general-purpose registers, with the S-boxes as Boolean circuits: no table
//! lookups. This module holds the subkeys and handles a partial last block
//! (§6.5, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): CTR of the last bytes padded to a block
//! XORs them with the first bytes of the next output block.
//!
//! The caller chooses the initial counter block, and must never use a
//! counter block twice with the same key (Appendix B.2).

#![cfg(target_arch = "x86_64")]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_ctr::vg_camellia_ctr;
use crate::zeroize::zeroize;

/// The key does not contain 16, 24 or 32 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Camellia key for CTR, whose encryption and decryption are the
/// same operation.
///
/// Keys of 16 bytes use 18 rounds; keys of 24 or 32 bytes, 24.
pub struct CamelliaCtr {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    rounds: usize,
}

impl CamelliaCtr {
    /// Expands a 16-, 24- or 32-byte key.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let rounds = match key.len() {
            16 => 18,
            24 | 32 => 24,
            _ => return Err(InvalidKeyLength),
        };
        let mut schedule = [0; 272];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
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
        // SAFETY: `rounds` is 18 for a key of 16 bytes and 24 otherwise, as
        // `new` expanded the schedule for. `blocks` holds `len / 16` whole
        // blocks (its length is a multiple of 16), and it, the block at
        // `ctr` and the schedule are separate valid objects of the sizes of
        // the signature, none of them on the callee's stack. The function
        // zeroes its working space on its own stack before returning.
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

impl Drop for CamelliaCtr {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
