//! SM4-CFB128 (SP 800-38A §6.3 with 128-bit segments, with SM4 as in GB/T
//! 32907-2016, transcribed in the Internet-Draft draft-ribose-cfrg-sm4-10),
//! in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_sm4_expand_key` (contract `VG.Spec.Sm4.expandKeyContract`) writes the
//! key schedule, and `vg_sm4_cfb128_encrypt` and `vg_sm4_cfb128_decrypt`
//! (`VG.Spec.Sm4.cfbEncryptContract`, `cfbDecryptContract`) replace whole
//! blocks with `Pⱼ ⊕ CIPH_K(Cⱼ₋₁)` or `Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` from the block at
//! `iv`, which they replace with the last ciphertext block, in constant time:
//! their timing depends on none of the key, the chaining value and the data.
//! Both are the modes' generic CFB over SM4's bitsliced ECB code, one block
//! at a time (in a batch of sixteen). This module holds the key schedule and
//! handles a partial last segment: CFB encryption of a zero block is
//! `CIPH_K` of the block to continue from, whose first bytes it XORs into the
//! rest of the input.

#![cfg(target_arch = "x86_64")]

use crate::arch::sm4::vg_sm4_expand_key;
use crate::arch::sm4_cfb::{vg_sm4_cfb128_decrypt, vg_sm4_cfb128_encrypt};
use crate::zeroize::zeroize;

/// An expanded SM4 key for CFB128 encryption and decryption.
pub struct Sm4Cfb128 {
    /// The key schedule `vg_sm4_expand_key` writes.
    schedule: [u8; 128],
}

/// The signature of `vg_sm4_cfb128_encrypt` and `vg_sm4_cfb128_decrypt`.
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);

impl Sm4Cfb128 {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8; 16]) -> Self {
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the
        // required sizes. The function zeroes its working space on its own
        // stack before returning.
        unsafe { vg_sm4_expand_key(key, &mut schedule) };
        Self { schedule }
    }

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_sm4_cfb128_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_sm4_cfb128_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 16];
            self.blocks(iv, &mut last, vg_sm4_cfb128_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv` and the schedule are
        // separate valid objects of the sizes of the signature, none of them
        // on the callee's stack. The function zeroes its working space on its
        // own stack before returning.
        unsafe {
            f(
                &self.schedule,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
            )
        };
    }
}

impl Drop for Sm4Cfb128 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
