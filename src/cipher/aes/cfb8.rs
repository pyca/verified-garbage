//! AES-CFB8 (SP 800-38A §6.3, with 8-bit segments) with 128-, 192- and 256-bit
//! keys, in place.

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
use crate::arch::aes_cfb8::{
    VG_AES_CFB8_DECRYPT_AES_FEATURES, VG_AES_CFB8_ENCRYPT_AES_FEATURES, vg_aes_cfb8_decrypt_aes,
    vg_aes_cfb8_encrypt_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_cfb8::{
    VG_AES_CFB8_DECRYPT_AESNI_FEATURES, VG_AES_CFB8_ENCRYPT_AESNI_FEATURES,
    vg_aes_cfb8_decrypt_aesni, vg_aes_cfb8_encrypt_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_cfb8::{
    VG_AES_CFB8_DECRYPT_VAES_FEATURES, VG_AES_CFB8_ENCRYPT_VAES_FEATURES, vg_aes_cfb8_decrypt_vaes,
    vg_aes_cfb8_encrypt_vaes,
};
use crate::arch::aes_cfb8::{vg_aes_cfb8_decrypt, vg_aes_cfb8_encrypt};
use crate::cipher::aes::Backend;
use crate::cpu::detected;
use crate::error::InvalidKeyLength;
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
/// its CFB8 functions.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CFB8_ENCRYPT_AESNI_FEATURES,
        VG_AES_CFB8_DECRYPT_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_CFB8_ENCRYPT_VAES_FEATURES,
        VG_AES_CFB8_DECRYPT_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
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

/// The only implementation of AES on ARMv7, PPC64LE and RISC-V.
#[cfg(any(
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
fn select(f: Features) -> Backend {
    Backend::select(f)
}

/// An expanded AES key, which serves both directions.
struct Key {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

/// An AES-CFB8 encryption of one message.
///
/// A message may be encrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb8Encryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 16],
}

impl AesCfb8Encryptor {
    /// Expands a 16-, 24- or 32-byte key, to encrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Encrypts `buffer` in place, continuing the message.
    pub fn encrypt(&mut self, buffer: &mut [u8]) {
        self.key.encrypt(&mut self.iv, buffer);
    }
}

/// An AES-CFB8 decryption of one message.
///
/// A message may be decrypted in pieces of any lengths, each continuing
/// where the last ended.
///
/// The IV must be unpredictable (SP 800-38A Appendix C).
pub struct AesCfb8Decryptor {
    key: Key,
    /// The input block to continue from: the IV, then its last bytes
    /// followed by the ciphertext so far.
    iv: [u8; 16],
}

impl AesCfb8Decryptor {
    /// Expands a 16-, 24- or 32-byte key, to decrypt a message from `iv`.
    pub fn new(key: &[u8], iv: &[u8; 16]) -> Result<Self, InvalidKeyLength> {
        Ok(Self {
            key: Key::new(key)?,
            iv: *iv,
        })
    }

    /// Decrypts `buffer` in place, continuing the message.
    pub fn decrypt(&mut self, buffer: &mut [u8]) {
        self.key.decrypt(&mut self.iv, buffer);
    }
}

impl Key {
    /// Expands a 16-, 24- or 32-byte key.
    fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        crate::dit::enter!(dit);
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
        unsafe { expand(dit, key.as_ptr(), key.len(), &mut schedule) };
        Ok(Self {
            schedule,
            rounds: key.len() / 4 + 6,
            backend,
        })
    }

    /// Encrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes.
    fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        let f = instance!(
            self.backend,
            vg_aes_cfb8_encrypt,
            vg_aes_cfb8_encrypt_aesni,
            vg_aes_cfb8_encrypt_vaes,
            vg_aes_cfb8_encrypt_aes
        );
        self.crypt(dit, iv, buffer, f);
    }

    /// Decrypts `buffer` in place, from the input block `iv`, which it
    /// replaces with the one to continue from: its last `16 - n` bytes
    /// followed by the last `n` (up to 16) ciphertext bytes.
    fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) {
        crate::dit::enter!(dit);
        let f = instance!(
            self.backend,
            vg_aes_cfb8_decrypt,
            vg_aes_cfb8_decrypt_aesni,
            vg_aes_cfb8_decrypt_vaes,
            vg_aes_cfb8_decrypt_aes
        );
        self.crypt(dit, iv, buffer, f);
    }

    fn crypt(&self, dit: crate::dit::Dit<'_>, iv: &mut [u8; 16], buffer: &mut [u8], f: Cfb8) {
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; `buffer`, the block at `iv`, the schedule and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                dit,
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
type Cfb8 = unsafe fn(
    crate::dit::Dit<'_>,
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cfb8_encrypt` and `vg_aes_cfb8_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type Cfb8 = unsafe fn(
    crate::dit::Dit<'_>,
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 272],
);

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
