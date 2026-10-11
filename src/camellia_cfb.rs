//! Camellia-CFB128 (SP 800-38A §6.3 with 128-bit segments, with Camellia as
//! in RFC 3713) with 128-, 192- and 256-bit keys, in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_camellia_expand_key` (contract `VG.Spec.Camellia.expandKeyContract`)
//! writes the subkeys, and `vg_camellia_cfb128_encrypt` and
//! `vg_camellia_cfb128_decrypt` (`VG.Spec.Camellia.cfbEncryptContract`,
//! `cfbDecryptContract`) replace whole blocks with `Pⱼ ⊕ CIPH_K(Cⱼ₋₁)` or
//! `Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` from the block at `iv`, which they replace with the last
//! ciphertext block, in constant time: their timing depends on none of the
//! key, the chaining value and the data. Both are the modes' generic CFB over
//! Camellia's bitsliced ECB code, one block at a time (in a batch of eight).
//! This module holds the subkeys and handles a partial last segment: CFB
//! encryption of a zero block is `CIPH_K` of the block to continue from,
//! whose first bytes it XORs into the rest of the input.

#![cfg(target_arch = "x86_64")]

use crate::arch::camellia::vg_camellia_expand_key;
use crate::arch::camellia_cfb::{vg_camellia_cfb128_decrypt, vg_camellia_cfb128_encrypt};
use crate::zeroize::zeroize;

/// The key is not 16, 24 or 32 bytes long.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Camellia key for CFB128 encryption and decryption.
pub struct CamelliaCfb128 {
    /// The subkeys `vg_camellia_expand_key` writes.
    schedule: [u8; 272],
    /// The number of rounds: 18 or 24.
    rounds: usize,
}

/// The signature of `vg_camellia_cfb128_encrypt` and `vg_camellia_cfb128_decrypt`.
type Cfb = unsafe extern "sysv64" fn(*const [u8; 272], usize, *mut [u8; 16], *mut [u8; 16], usize);

impl CamelliaCfb128 {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
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

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_camellia_cfb128_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_camellia_cfb128_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 16];
            self.blocks(iv, &mut last, vg_camellia_cfb128_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `rounds` is 18 or 24 and the schedule holds that many
        // rounds' subkeys; `blocks` holds `len / 16` whole blocks (its length
        // is a multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them
        // on the callee's stack. The function zeroes its working space on its
        // own stack before returning.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for CamelliaCfb128 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
