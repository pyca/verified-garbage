//! SEED-CFB128 (SP 800-38A §6.3 with 128-bit segments, with SEED as in RFC
//! 4269), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_seed_expand_key` (contract `VG.Spec.Seed.expandKeyContract`) writes
//! the key schedule, and `vg_seed_cfb128_encrypt` and
//! `vg_seed_cfb128_decrypt` (`VG.Spec.Seed.cfbEncryptContract`,
//! `cfbDecryptContract`) replace whole blocks with their CFB encryption or
//! decryption from the block at `iv`, which they replace with the last
//! ciphertext block, in constant time: their timing depends on none of the
//! key, the chaining value and the data. This module holds the key schedule
//! and handles a partial last segment (§6.3,
//! `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))`): CFB encryption of a zero block gives
//! `CIPH_K` of the block to continue from, whose first bytes it XORs into
//! the rest of the input.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::seed::vg_seed_expand_key;
use crate::arch::seed_cfb::{vg_seed_cfb128_decrypt, vg_seed_cfb128_encrypt};
use crate::zeroize::zeroize;

/// The key does not contain 16 bytes.
pub use crate::error::InvalidKeyLength;

/// An expanded SEED key for CFB128 encryption and decryption.
pub struct SeedCfb128 {
    /// The key schedule `vg_seed_expand_key` writes.
    schedule: [u8; 128],
}

/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);
/// The signature of `vg_seed_cfb128_encrypt` and `vg_seed_cfb128_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 128], *mut [u8; 16], *mut [u8; 16], usize);

impl SeedCfb128 {
    /// Expands a 16-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        let key: &[u8; 16] = key.try_into().map_err(|_| InvalidKeyLength)?;
        let mut schedule = [0; 128];
        // SAFETY: key and schedule are separate valid buffers of the required
        // sizes.
        unsafe { vg_seed_expand_key(key, &mut schedule) };
        Ok(Self { schedule })
    }

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_seed_cfb128_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 16
    /// bytes must end the message.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_seed_cfb128_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 16 * 16;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 16];
            self.blocks(iv, &mut last, vg_seed_cfb128_encrypt);
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
        // separate valid objects of the sizes of the signature, none of them on
        // the callee's stack.
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

impl Drop for SeedCfb128 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}
