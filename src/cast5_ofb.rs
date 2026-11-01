//! CAST5-OFB (SP 800-38A §6.4, with CAST5 as in RFC 2144), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_cast5_expand_key` (contract `VG.Spec.Cast5.expandKeyContract`) writes
//! the subkeys, and `vg_cast5_ofb` (`VG.Spec.Cast5.ofbContract`) XORs whole
//! blocks with the output blocks `Oⱼ = CIPH_K(Oⱼ₋₁)` from the block at `iv`,
//! which it replaces with the last output block, in constant time: its
//! timing depends on none of the key, the chaining value and the data. This
//! module holds the subkeys and handles a partial last block
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

use crate::arch::cast5_ofb::vg_cast5_ofb;
use crate::cast5_ecb::Cast5Ecb;
use crate::zeroize::zeroize;

/// The key does not contain 5 to 16 bytes.
pub use crate::error::InvalidKeyLength;

/// An expanded CAST5 key for OFB, whose encryption and decryption are the
/// same operation.
pub struct Cast5Ofb {
    key: Cast5Ecb,
}

impl Cast5Ofb {
    /// Expands a key of 5 to 16 bytes.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Cast5Ecb::new(key).map_err(|_| InvalidKeyLength)?,
        })
    }

    /// Encrypts or decrypts (the same operation) `buffer` in place, from the
    /// block `iv`, which it replaces with the last output block used
    /// (unchanged for empty input). A message may be processed in pieces of
    /// whole blocks, each continuing from the `iv` the last left; a piece
    /// whose length is not a multiple of 8 bytes must end the message.
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
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; `blocks` holds `len / 8` whole
        // blocks, and it, the block at `iv` and the schedule are separate
        // valid objects of the sizes of the signature, none of them on the
        // callee's stack. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            vg_cast5_ofb(
                self.key.schedule(),
                self.key.rounds(),
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}
