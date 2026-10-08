//! AES-CFB8 (SP 800-38A §6.3, with 8-bit segments) with 128-, 192- and
//! 256-bit keys, in place.
//!
//! The block cipher work is verified assembly: `vg_aes_expand_key`
//! (contract `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`
//! (`VG.Spec.Cfb8.aesEncryptContract`, `aesDecryptContract`) replace each
//! byte with `C#ⱼ = P#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))` or `P#ⱼ = C#ⱼ ⊕ MSB₈(CIPH_K(Iⱼ))`
//! from the input block at `iv`, which they replace with the one to
//! continue from, in constant time. They call `vg_aes_encrypt_blocks` on
//! one block for each byte.
//!
//! On x86-64 and x86, CPUs with AES-NI run the `_aesni` functions
//! (`crate::aes::Backend`; there is no VAES implementation of whole blocks
//! yet, so its CPUs run them too); on AArch64, CPUs with the AES
//! instructions run the `_aes` ones. Elsewhere, and on other CPUs, the
//! constant-time bitsliced implementation runs.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::aes::Backend;
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_cfb8::{
    VG_AES_CFB8_DECRYPT_AES_FEATURES, VG_AES_CFB8_ENCRYPT_AES_FEATURES, vg_aes_cfb8_decrypt_aes,
    vg_aes_cfb8_encrypt_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_cfb8::{
    VG_AES_CFB8_DECRYPT_AESNI_FEATURES, VG_AES_CFB8_ENCRYPT_AESNI_FEATURES,
    vg_aes_cfb8_decrypt_aesni, vg_aes_cfb8_encrypt_aesni,
};
use crate::arch::aes_cfb8::{vg_aes_cfb8_decrypt, vg_aes_cfb8_encrypt};
use crate::cpu::{Features, detected};
use crate::zeroize::zeroize;

/// The instance of a function for `backend`: the scalar one, x86-64's or
/// x86's for AES-NI, or AArch64's for the AES instructions.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            // No VAES implementation of CFB8 yet.
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi | Backend::Vaes => $aesni,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB8 functions.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CFB8_ENCRYPT_AESNI_FEATURES,
        VG_AES_CFB8_DECRYPT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB8 functions.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CFB8_ENCRYPT_AESNI_FEATURES,
        VG_AES_CFB8_DECRYPT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB8 functions.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_CFB8_ENCRYPT_AES_FEATURES,
        VG_AES_CFB8_DECRYPT_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7.
#[cfg(target_arch = "arm")]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// The key is not 16, 24 or 32 bytes long.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidKeyLength;

/// An expanded AES key for CFB8 encryption and decryption.
pub struct AesCfb8 {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

impl AesCfb8 {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the
        // schedule are separate valid buffers of the sizes of the signature,
        // and `select` chose `expand` for the CPU's features. The function
        // zeroes its working space on its own stack before returning.
        unsafe { expand(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes. A message may
    /// be encrypted in pieces of any length, each continuing from the `iv`
    /// the last left.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_cfb8_encrypt,
            vg_aes_cfb8_encrypt_aesni,
            vg_aes_cfb8_encrypt_aes
        );
        self.crypt(iv, buffer, f);
    }

    /// Decrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes. A message may
    /// be decrypted in pieces of any length, each continuing from the `iv`
    /// the last left.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_cfb8_decrypt,
            vg_aes_cfb8_decrypt_aesni,
            vg_aes_cfb8_decrypt_aes
        );
        self.crypt(iv, buffer, f);
    }

    fn crypt(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb8) {
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `buffer`, the block at `iv`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr(),
                buffer.len(),
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
    }
}

/// The signature of `vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb8 = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`.
#[cfg(any(target_arch = "x86", target_arch = "aarch64", target_arch = "arm"))]
type Cfb8 =
    unsafe extern "C" fn(*const [u8; 240], usize, *mut [u8; 16], *mut u8, usize, *mut [u64; 272]);

impl Drop for AesCfb8 {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCfb8, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesCfb8::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
        use crate::cpu::Features;
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(select(Features::of(&["aes", "ssse3"])), Backend::AesNi);
            let vaes = Features::of(&["aes", "avx", "avx2", "ssse3", "vaes"]);
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features::of(&["aes"])), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features::of(&["aes"])), Backend::Aes);
    }
}
