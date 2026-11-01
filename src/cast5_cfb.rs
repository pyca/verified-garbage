//! CAST5-CFB64 (SP 800-38A §6.3 with 64-bit segments, with CAST5 as in
//! RFC 2144), in place.
//!
//! The block cipher work and the feedback are verified assembly:
//! `vg_cast5_expand_key` (contract `VG.Spec.Cast5.expandKeyContract`) writes
//! the subkeys, and `vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt`
//! (`VG.Spec.Cast5.cfbEncryptContract`, `cfbDecryptContract`) replace whole
//! blocks with `Pⱼ ⊕ CIPH_K(Cⱼ₋₁)` or `Cⱼ ⊕ CIPH_K(Cⱼ₋₁)` from the block at
//! `iv`, which they replace with the last ciphertext block, in constant time:
//! their timing depends on none of the key, the chaining value and the data.
//! This module holds the subkeys and handles a partial
//! last segment: CFB encryption of a zero block is `CIPH_K` of the block to
//! continue from, whose first bytes it XORs into the rest of the input.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::cast5_cfb::{vg_cast5_cfb64_decrypt, vg_cast5_cfb64_encrypt};
use crate::cast5_ecb::Cast5Ecb;
use crate::zeroize::zeroize;

/// The key does not contain 5 to 16 bytes.
pub use crate::error::InvalidKeyLength;

/// An expanded CAST5 key for CFB64 encryption and decryption.
pub struct Cast5Cfb64 {
    key: Cast5Ecb,
}

/// The signature of `vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(*const [u8; 128], usize, *mut [u8; 8], *mut [u8; 8], usize);
/// The signature of `vg_cast5_cfb64_encrypt` and `vg_cast5_cfb64_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(*const [u8; 128], usize, *mut [u8; 8], *mut [u8; 8], usize);

impl Cast5Cfb64 {
    /// Expands a key of 5 to 16 bytes for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Cast5Ecb::new(key).map_err(|_| InvalidKeyLength)?,
        })
    }

    /// Encrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be encrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 8 bytes
    /// must end the message.
    pub fn encrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_cast5_cfb64_encrypt);
    }

    /// Decrypts `buffer` in place, from the block `iv`, which it replaces
    /// with the last ciphertext block (unchanged for empty input; after a
    /// partial last segment, the cipher of the last whole one). A message
    /// may be decrypted in pieces of whole blocks, each continuing from the
    /// `iv` the last left; a piece whose length is not a multiple of 8 bytes
    /// must end the message.
    pub fn decrypt(&self, iv: &mut [u8; 8], buffer: &mut [u8]) {
        self.crypt(iv, buffer, vg_cast5_cfb64_decrypt);
    }

    fn crypt(&self, iv: &mut [u8; 8], buffer: &mut [u8], f: Cfb) {
        let whole = buffer.len() / 8 * 8;
        let (blocks, rest) = buffer.split_at_mut(whole);
        self.blocks(iv, blocks, f);
        if !rest.is_empty() {
            // `CIPH_K` of the block to continue from, as CFB encryption of a
            // zero block, XORed into the last bytes.
            let mut last = [0; 8];
            self.blocks(iv, &mut last, vg_cast5_cfb64_encrypt);
            for (b, o) in rest.iter_mut().zip(last) {
                *b ^= o;
            }
            zeroize(&mut last);
        }
    }

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 8], blocks: &mut [u8], f: Cfb) {
        // SAFETY: `rounds` is 12 or 16, as `Cast5Ecb::new` chose for the key
        // the schedule was expanded from; `blocks` holds `len / 8` whole
        // blocks, and it, the block at `iv` and the schedule are separate
        // valid objects of the sizes of the signature, none of them on the
        // callee's stack. The function zeroes its working space on its own
        // stack before returning.
        unsafe {
            f(
                self.key.schedule(),
                self.key.rounds(),
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 8,
            )
        };
    }
}
