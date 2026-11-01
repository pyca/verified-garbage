//! SEED-OFB (SP 800-38A §6.4, with SEED as in RFC 4269), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_seed_expand_key` (contract `VG.Spec.Seed.expandKeyContract`) writes
//! the key schedule, and `vg_seed_ofb` (`VG.Spec.Seed.ofbContract`) XORs
//! whole blocks with the output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)` from the block at
//! `iv`, which it replaces with the last output block, in constant time: its
//! timing depends on none of the key, the chaining value and the data. This
//! module holds the key schedule and handles a partial last block (§6.4,
//! `Cₙ* = Pₙ* ⊕ MSB_u(Oₙ)`): OFB of a zero block is the next output block,
//! whose first bytes it XORs into the rest of the input.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::seed::vg_seed_expand_key;
use crate::arch::seed_ofb::vg_seed_ofb;
use crate::zeroize::zeroize;

/// The key does not contain 16 bytes.
pub use crate::error::InvalidKeyLength;

/// An expanded SEED key for OFB, whose encryption and decryption are the
/// same operation.
pub struct SeedOfb {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: [u8; 128],
}

impl SeedOfb {
    /// Expands a 16-byte key.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key(key, &mut schedule) };
        Ok(Self { schedule })
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
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
        unsafe {
            vg_seed_ofb(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for SeedOfb {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
