//! Triple DES-CFB64 (SP 800-38A §6.3 with 64-bit segments, with Triple DES
//! as in FIPS 46-3), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_triple_des_expand_key` (contract `VG.Spec.TripleDes.expandKeyContract`)
//! writes the key schedule, and `vg_triple_des_cfb64_encrypt` and
//! `vg_triple_des_cfb64_decrypt` (`VG.Spec.TripleDes.cfbEncryptContract`,
//! `cfbDecryptContract`) replace whole blocks with `Pⱼ ⊕ CIPH_K(Cⱼ₋₁)` or
//! `Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` from the block at `iv`, which they replace with the
//! last ciphertext block, in constant time: their timing depends on none of
//! the key, the chaining value and the data. Both are the modes' generic CFB
//! over the scalar block function. This module holds the key schedule and
//! handles a partial last segment: CFB encryption of a zero block is
//! `CIPH_K` of the block to continue from, whose first bytes it XORs into the
//! rest of the input.

#![cfg(target_arch = "x86_64")]

use crate::arch::triple_des::vg_triple_des_expand_key;
use crate::arch::triple_des_cfb::{vg_triple_des_cfb64_decrypt, vg_triple_des_cfb64_encrypt};
use crate::zeroize::zeroize;

/// The key does not contain 16 or 24 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded Triple DES key for CFB64 encryption and decryption.
///
/// A 24-byte key encodes K1, K2 and K3. A 16-byte key encodes K1 and K2,
/// with K3 repeating K1. Each byte's parity bit is ignored.
pub struct TripleDesCfb64 {
    /// The key schedule `vg_triple_des_expand_key` writes.
    schedule: [u8; 384],
}

/// The signature of `vg_triple_des_cfb64_encrypt` and `vg_triple_des_cfb64_decrypt`.
type Cfb = unsafe extern "sysv64" fn(*const [u8; 384], *mut [u8; 8], *mut [u8; 8], usize);

impl TripleDesCfb64 {
    /// Expands a 16- or 24-byte key for use in either direction.
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

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of eight
    /// bytes must end the message.
    pub fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_triple_des_cfb64_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of eight
    /// bytes must end the message.
    pub fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_triple_des_cfb64_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 8], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 8 * 8;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 8];
            self.blocks(iv, &mut last, vg_triple_des_cfb64_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 8], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `blocks` holds `len / 8` whole blocks (its length is a
        // multiple of 8), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them
        // on the callee's stack. The function zeroes its working space on its
        // own stack before returning.
        unsafe {
            f(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}

impl Drop for TripleDesCfb64 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
