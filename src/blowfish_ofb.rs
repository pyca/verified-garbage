//! Blowfish-OFB (SP 800-38A §6.4, with Blowfish as in Schneier, FSE 1994),
//! in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_blowfish_expand_key` (contract `VG.Spec.Blowfish.expandKeyContract`)
//! writes the schedule, and `vg_blowfish_ofb` (`VG.Spec.Blowfish.ofbContract`)
//! XORs whole blocks with the output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)` from the block
//! at `iv`, which it replaces with the last output block, in constant time: its
//! timing depends on none of the key, the chaining value and the data. This
//! module holds the schedule and handles a partial last block
//! (§6.4, `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): OFB of a zero block is the next output
//! block, whose first bytes it XORs into the rest of the input.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::blowfish::vg_blowfish_expand_key;
use crate::arch::blowfish_ofb::vg_blowfish_ofb;
use crate::zeroize::zeroize;

/// The key length is outside 4..=56 bytes (32 to 448 bits).
pub use crate::error::InvalidKeyLength;

/// An expanded Blowfish key for OFB, whose encryption and decryption are the
/// same operation.
pub struct BlowfishOfb {
    /// The schedule `vg_blowfish_expand_key` writes.
    schedule: [u8; 4168],
}

impl BlowfishOfb {
    /// Expands a key of 4..=56 bytes (32 to 448 bits). Weak keys are
    /// accepted.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !(4..=56).contains(&key.len()) {
            return Err(InvalidKeyLength);
        }
        let mut schedule = [0; 4168];
        // SAFETY: the key has a length in 4..=56; the key and the schedule
        // are separate valid objects of the lengths passed.
        unsafe { vg_blowfish_expand_key(key.as_ptr(), key.len(), &mut schedule) };
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
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_blowfish_ofb(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}

impl Drop for BlowfishOfb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
