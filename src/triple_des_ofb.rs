//! Triple DES-OFB (SP 800-38A §6.4, with Triple DES as in FIPS 46-3), in
//! place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_triple_des_expand_key` (contract `VG.Spec.TripleDes.expandKeyContract`)
//! writes the key schedule, and `vg_triple_des_ofb`
//! (`VG.Spec.TripleDes.ofbContract`) XORs whole blocks with the output blocks
//! `Oⱼ = CIPH_K(Oⱼ₋₁)` from the block at `iv`, which it replaces with the
//! last output block, in constant time: its timing depends on none of the
//! key, the chaining value and the data. It is the modes' generic OFB over
//! the scalar block function. This module holds the key schedule and handles
//! a partial last block (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): OFB of a zero block
//! is the next output block, whose first bytes it XORs into the rest of the
//! input.

#![cfg(target_arch = "x86_64")]

use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_ofb::vg_triple_des_ofb;
use crate::zeroize::zeroize;

/// The key does not contain 16 or 24 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Triple DES key for OFB, whose encryption and decryption are
/// the same operation.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored.
pub struct TripleDesOfb {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

impl TripleDesOfb {
    /// Expands a 16- or 24-byte key.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 384];
        // SAFETY: the key has a validated length; key and schedule are
        // separate valid buffers of the required sizes. The function zeroes
        // its working space on its own stack before returning.
        unsafe { vg_triple_des_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of eight bytes must end the message.
    pub fn apply_keystream(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        let whole = buffer.len() / 8 * 8;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.crypt(iv, blocks);
        if !rest.is_empty() {
            // The next output block, as OFB of a zero block, XORed into the
            // last bytes.
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
        // separate valid objects of the sizes of the signature, none of them
        // on the callee's stack. The function zeroes its working space on its
        // own stack before returning.
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

impl Drop for TripleDesOfb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
