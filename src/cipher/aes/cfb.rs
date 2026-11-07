//! AES-CFB128 (SP 800-38A §6.3, with 128-bit segments) with 128-, 192- and
//! 256-bit keys, in place.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_cfb::{
    VG_AES_CFB128_DECRYPT_AES_FEATURES, VG_AES_CFB128_DECRYPT_FINAL_AES_FEATURES,
    VG_AES_CFB128_ENCRYPT_AES_FEATURES, VG_AES_CFB128_ENCRYPT_FINAL_AES_FEATURES,
    vg_aes_cfb128_decrypt_aes, vg_aes_cfb128_decrypt_final_aes, vg_aes_cfb128_encrypt_aes,
    vg_aes_cfb128_encrypt_final_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_cfb::{
    VG_AES_CFB128_DECRYPT_AESNI_FEATURES, VG_AES_CFB128_DECRYPT_FINAL_AESNI_FEATURES,
    VG_AES_CFB128_ENCRYPT_AESNI_FEATURES, VG_AES_CFB128_ENCRYPT_FINAL_AESNI_FEATURES,
    vg_aes_cfb128_decrypt_aesni, vg_aes_cfb128_decrypt_final_aesni, vg_aes_cfb128_encrypt_aesni,
    vg_aes_cfb128_encrypt_final_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_cfb::{
    VG_AES_CFB128_DECRYPT_FINAL_VAES_FEATURES, VG_AES_CFB128_DECRYPT_VAES_FEATURES,
    VG_AES_CFB128_ENCRYPT_FINAL_VAES_FEATURES, VG_AES_CFB128_ENCRYPT_VAES_FEATURES,
    vg_aes_cfb128_decrypt_final_vaes, vg_aes_cfb128_decrypt_vaes, vg_aes_cfb128_encrypt_final_vaes,
    vg_aes_cfb128_encrypt_vaes,
};
use crate::arch::aes_cfb::{
    vg_aes_cfb128_decrypt, vg_aes_cfb128_decrypt_final, vg_aes_cfb128_encrypt,
    vg_aes_cfb128_encrypt_final,
};
use crate::cipher::aes::Backend;
use crate::cpu::detected;
use crate::error::{IncompleteBlock, InvalidKeyLength};
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

/// The variant of a function for `backend`: the baseline one, or its
/// `_aesni`, `_vaes` or `_aes` one.
macro_rules! instance {
    ($backend:expr, $scalar:ident, $aesni:ident, $vaes:ident, $aes:ident) => {
        match $backend {
            Backend::Scalar => $scalar,
            #[cfg(target_arch = "x86_64")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "x86_64")]
            Backend::Vaes => $vaes,
            #[cfg(target_arch = "x86")]
            Backend::AesNi => $aesni,
            #[cfg(target_arch = "aarch64")]
            Backend::Aes => $aes,
        }
    };
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB functions.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CFB128_ENCRYPT_AESNI_FEATURES,
        VG_AES_CFB128_DECRYPT_AESNI_FEATURES,
        VG_AES_CFB128_ENCRYPT_FINAL_AESNI_FEATURES,
        VG_AES_CFB128_DECRYPT_FINAL_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_CFB128_ENCRYPT_VAES_FEATURES,
        VG_AES_CFB128_DECRYPT_VAES_FEATURES,
        VG_AES_CFB128_ENCRYPT_FINAL_VAES_FEATURES,
        VG_AES_CFB128_DECRYPT_FINAL_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB functions.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CFB128_ENCRYPT_AESNI_FEATURES,
        VG_AES_CFB128_DECRYPT_AESNI_FEATURES,
        VG_AES_CFB128_ENCRYPT_FINAL_AESNI_FEATURES,
        VG_AES_CFB128_DECRYPT_FINAL_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CFB functions.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_CFB128_ENCRYPT_AES_FEATURES,
        VG_AES_CFB128_DECRYPT_AES_FEATURES,
        VG_AES_CFB128_ENCRYPT_FINAL_AES_FEATURES,
        VG_AES_CFB128_DECRYPT_FINAL_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7, PPC64LE and RISC-V.
#[cfg(any(
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// An expanded AES key.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

/// An AES-CFB128 encryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`encrypt_final`](Self::encrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb128Encryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCfb128Encryptor {
    /// Expands a 16-, 24- or 32-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`encrypt_final`](Self::encrypt_final) takes
    /// a partial last segment.
    pub fn encrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.encrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Encrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Cₙ* = Pₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn encrypt_final(mut self, buffer: &mut [u8]) {
        self.key.encrypt_final(&mut self.iv, buffer);
    }
}

impl Drop for AesCfb128Encryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

/// An AES-CFB128 decryption of one message.
///
/// Each call but the last takes whole 16-byte blocks and continues the
/// message from the last ciphertext block of the call before; the last,
/// [`decrypt_final`](Self::decrypt_final), takes the rest of the message, of
/// any length.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb128Decryptor {
    key: Key,
    /// The block to continue from: the IV, then the last ciphertext block.
    iv: [u8; 16],
}

impl AesCfb128Decryptor {
    /// Expands a 16-, 24- or 32-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts whole 16-byte blocks in place, continuing the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16: only [`decrypt_final`](Self::decrypt_final) takes
    /// a partial last segment.
    pub fn decrypt(&mut self, buffer: &mut [u8]) -> Result<(), IncompleteBlock> {
        if !buffer.len().is_multiple_of(16) {
            return Err(IncompleteBlock);
        }
        self.key.decrypt(&mut self.iv, buffer);
        Ok(())
    }

    /// Decrypts the rest of the message in place, of any length: its whole
    /// blocks, then a partial last segment if there is one,
    /// `Pₙ* = Cₙ* ⊕ MSB_u(CIPH_K(Cₙ₋₁))` (SP 800-38A defines CFB only for
    /// whole segments; this is the rule of its §6.4 and §6.5 for a partial
    /// last block, as other implementations extend CFB).
    pub fn decrypt_final(mut self, buffer: &mut [u8]) {
        self.key.decrypt_final(&mut self.iv, buffer);
    }
}

impl Drop for AesCfb128Decryptor {
    /// Wipes the block to continue from, which after a partial last segment
    /// is keystream.
    fn drop(&mut self) {
        zeroize(&mut self.iv);
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(InvalidKeyLength);
        }
        let backend = select(detected());
        let expand = instance!(
            backend,
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut schedule = [0; 240];
        // SAFETY: the key is 16, 24 or 32 bytes long; the key and the schedule
        // are separate valid buffers of the sizes of the signature, and
        // `select` chose `expand` for the CPU's features.
        unsafe { expand(key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_cfb128_encrypt,
            vg_aes_cfb128_encrypt_aesni,
            vg_aes_cfb128_encrypt_vaes,
            vg_aes_cfb128_encrypt_aes
        );
        self.blocks(iv, buffer, f);
    }

    /// Decrypts the whole blocks of `buffer` in place, from the block `iv`,
    /// which it replaces with the last ciphertext block (unchanged for empty
    /// input).
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let f = instance!(
            self.backend,
            vg_aes_cfb128_decrypt,
            vg_aes_cfb128_decrypt_aesni,
            vg_aes_cfb128_decrypt_vaes,
            vg_aes_cfb128_decrypt_aes
        );
        self.blocks(iv, buffer, f);
    }

    /// Encrypts the rest of a message, of any length, in place: its whole
    /// blocks with `encrypt`, then the bytes after them, fewer than 16, with
    /// the final function, from the IV the whole blocks leave.
    fn encrypt_final(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.encrypt(iv, blocks);
        if !rest.is_empty() {
            let f = instance!(
                self.backend,
                vg_aes_cfb128_encrypt_final,
                vg_aes_cfb128_encrypt_final_aesni,
                vg_aes_cfb128_encrypt_final_vaes,
                vg_aes_cfb128_encrypt_final_aes
            );
            self.final_(iv, rest, f);
        }
    }

    /// Decrypts the rest of a message, of any length, in place: its whole
    /// blocks with `decrypt` (which may decrypt several at once), then the
    /// bytes after them, fewer than 16, with the final function, from the IV
    /// the whole blocks leave.
    fn decrypt_final(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        let (blocks, rest) = buffer.split_at_mut(buffer.len() / 16 * 16);
        self.decrypt(iv, blocks);
        if !rest.is_empty() {
            let f = instance!(
                self.backend,
                vg_aes_cfb128_decrypt_final,
                vg_aes_cfb128_decrypt_final_aesni,
                vg_aes_cfb128_decrypt_final_vaes,
                vg_aes_cfb128_decrypt_final_aes
            );
            self.final_(iv, rest, f);
        }
    }

    /// `f`, a final function, on the rest of a message, of any length: it
    /// replaces `iv` with the last ciphertext block, or, after a partial last
    /// segment, with keystream, which the caller wipes.
    fn final_(&self, iv: &mut [u8; 16], buffer: &mut [u8], f: CfbFinal) {
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `buffer` is valid for `len` bytes, and it, the block at
        // `iv`, the schedule and the scratch space are separate valid objects
        // of the sizes of the signature. `select` chose `f` for the CPU's
        // features.
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

    /// `f` on whole blocks.
    fn blocks(&self, iv: &mut [u8; 16], blocks: &mut [u8], f: Cfb) {
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `blocks` holds `len / 16` whole blocks (its length is a
        // multiple of 16), and it, the block at `iv`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                blocks.as_mut_ptr().cast(),
                blocks.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers.
        zeroize(&mut scratch);
    }
}

/// The signature of `vg_aes_cfb128_encrypt` and `vg_aes_cfb128_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cfb = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cfb128_encrypt` and `vg_aes_cfb128_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type Cfb = unsafe extern "C" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);

/// The signature of `vg_aes_cfb128_encrypt_final` and
/// `vg_aes_cfb128_decrypt_final`.
#[cfg(target_arch = "x86_64")]
type CfbFinal = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cfb128_encrypt_final` and
/// `vg_aes_cfb128_decrypt_final`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type CfbFinal =
    unsafe extern "C" fn(*const [u8; 240], usize, *mut [u8; 16], *mut u8, usize, *mut [u64; 272]);

impl Drop for Key {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{Key, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                Key::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::cipher::aes::Backend;
        use verified_garbage_cpu::{Features, feature};
        assert_eq!(select(Features(0)), Backend::Scalar);
        #[cfg(target_arch = "x86_64")]
        {
            assert_eq!(
                select(Features(feature::AES | feature::SSSE3)),
                Backend::AesNi
            );
            let vaes = Features(
                feature::AES | feature::AVX | feature::AVX2 | feature::SSSE3 | feature::VAES,
            );
            assert_eq!(select(vaes), Backend::Vaes);
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features(feature::AES)), Backend::AesNi);
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features(feature::AES)), Backend::Aes);
    }
}
