//! Camellia-OFB (SP 800-38A §6.4, with Camellia as in RFC 3713) with 128-,
//! 192- and 256-bit keys, in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_camellia_expand_key` (contract `VG.Spec.Camellia.expandKeyContract`)
//! writes the subkeys, and `vg_camellia_ofb` (`VG.Spec.Camellia.ofbContract`)
//! XORs whole blocks with the output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)` from the
//! block at `iv`, which it replaces with the last output block, in constant
//! time: its timing depends on none of the key, the chaining value and the
//! data. It is the modes' generic OFB over Camellia's bitsliced ECB code, one
//! block at a time (in a batch of eight). This module holds the subkeys and
//! handles a partial last block (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): OFB of a zero
//! block is the next output block, whose first bytes it XORs into the rest of
//! the input.

#![cfg(target_arch = "x86_64")]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_ofb::vg_camellia_ofb;
use crate::zeroize::zeroize;

/// The key is not 16, 24 or 32 bytes long.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Camellia key for OFB, whose encryption and decryption are the
/// same operation.
pub struct CamelliaOfb {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    /// The number of rounds: 18 or 24.
    rounds: usize,
}

impl CamelliaOfb {
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
        unsafe { vg_camellia_expand_key(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self { schedule, rounds })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of 16 bytes must end the message.
    pub fn apply_keystream(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
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
        // SAFETY: `rounds` is 18 or 24 and the schedule holds that many
        // rounds' subkeys; `blocks` holds `len / 16` whole blocks (its length
        // is a multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them
        // on the callee's stack. The function zeroes its working space on its
        // own stack before returning.
        unsafe {
            vg_camellia_ofb(
                &self.schedule,
                self.rounds,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for CamelliaOfb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
