//! AES-CBC (SP 800-38A §6.2) with 128-, 192- and 256-bit keys, in place
//! and without padding.
//!
//! The whole mode is verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedule, and
//! `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` (`VG.Spec.Cbc.aesEncryptContract`,
//! `aesDecryptContract`) replace each block with its CBC encryption or
//! decryption and the chaining value with the last ciphertext block, in
//! constant time. This module checks the lengths, which the assembly does
//! not, and holds the key schedule.
//!
//! The variants of these functions, with the same contracts, are chosen
//! with `crate::aes::Backend`, on CPUs with the features their `_FEATURES`
//! constants name (and the key expansion's): on x86-64, the `_vaes` ones,
//! then the `_aesni` ones (both with `vg_aes_expand_key_aesni`); on x86, the
//! `_aesni` ones; on AArch64, the `_aes` ones, and for decryption
//! `vg_aes_cbc_decrypt_aes_sha3` instead of `vg_aes_cbc_decrypt_aes` on CPUs
//! with the features `VG_AES_CBC_DECRYPT_AES_SHA3_FEATURES` names.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::aes::Backend;
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_AES_FEATURES, VG_AES_CBC_DECRYPT_AES_SHA3_FEATURES,
    VG_AES_CBC_DECRYPT_AES_SHA3_SCRATCH_WRITTEN, VG_AES_CBC_ENCRYPT_AES_FEATURES,
    VG_AES_CBC_ENCRYPT_AES_SCRATCH_WRITTEN, vg_aes_cbc_decrypt_aes, vg_aes_cbc_decrypt_aes_sha3,
    vg_aes_cbc_encrypt_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_AESNI_FEATURES, VG_AES_CBC_ENCRYPT_AESNI_FEATURES, vg_aes_cbc_decrypt_aesni,
    vg_aes_cbc_encrypt_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_cbc::{
    VG_AES_CBC_DECRYPT_VAES_FEATURES, VG_AES_CBC_ENCRYPT_VAES_FEATURES, vg_aes_cbc_decrypt_vaes,
    vg_aes_cbc_encrypt_vaes,
};
use crate::arch::aes_cbc::{vg_aes_cbc_decrypt, vg_aes_cbc_encrypt};
use crate::cpu::detected;
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
/// its CBC functions.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AESNI_FEATURES,
        VG_AES_CBC_DECRYPT_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_VAES_FEATURES,
        VG_AES_CBC_DECRYPT_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CBC functions.
#[cfg(target_arch = "x86")]
fn select(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AESNI_FEATURES,
        VG_AES_CBC_DECRYPT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its CBC functions.
#[cfg(target_arch = "aarch64")]
fn select(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_CBC_ENCRYPT_AES_FEATURES,
        VG_AES_CBC_DECRYPT_AES_FEATURES,
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

/// Why an AES-CBC operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 16, 24 or 32 bytes long.
    InvalidKeyLength,
    /// The input length is not a multiple of 16 bytes.
    IncompleteBlock,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid AES key length",
        IncompleteBlock => "AES-CBC input is not a whole number of blocks",
    }
}

/// An expanded AES key for CBC encryption and decryption.
///
/// No padding is added or removed: each operation takes whole 16-byte
/// blocks. The chaining value is updated in place, so that a message may be
/// processed in pieces, each continuing from the last.
pub struct AesCbc {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The implementation of AES the functions called use.
    backend: Backend,
}

impl AesCbc {
    /// Expands a 16-, 24- or 32-byte key for use in either direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 16 | 24 | 32) {
            return Err(Error::InvalidKeyLength);
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

    /// Encrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn encrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f = instance!(
            self.backend,
            vg_aes_cbc_encrypt,
            vg_aes_cbc_encrypt_aesni,
            vg_aes_cbc_encrypt_vaes,
            vg_aes_cbc_encrypt_aes
        );
        #[cfg(target_arch = "aarch64")]
        let scratch_written = match self.backend {
            Backend::Aes => VG_AES_CBC_ENCRYPT_AES_SCRATCH_WRITTEN,
            Backend::Scalar => 2176,
        };
        #[cfg(not(target_arch = "aarch64"))]
        let scratch_written = 2176;
        self.crypt(iv, buffer, f, scratch_written)
    }

    /// Decrypts whole 16-byte blocks in place, chained from `iv`, and
    /// replaces `iv` with the last ciphertext block (leaving it unchanged
    /// for empty input), so that a further call continues the message.
    /// Returns an error without changing anything if the buffer's length is
    /// not a multiple of 16.
    pub fn decrypt(&self, iv: &mut [u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        #[cfg(target_arch = "aarch64")]
        if self.backend == Backend::Aes && detected().contains(VG_AES_CBC_DECRYPT_AES_SHA3_FEATURES)
        {
            return self.crypt(
                iv,
                buffer,
                vg_aes_cbc_decrypt_aes_sha3,
                VG_AES_CBC_DECRYPT_AES_SHA3_SCRATCH_WRITTEN,
            );
        }
        let f = instance!(
            self.backend,
            vg_aes_cbc_decrypt,
            vg_aes_cbc_decrypt_aesni,
            vg_aes_cbc_decrypt_vaes,
            vg_aes_cbc_decrypt_aes
        );
        self.crypt(iv, buffer, f, 2176)
    }

    fn crypt(
        &self,
        iv: &mut [u8; 16],
        buffer: &mut [u8],
        f: Cbc,
        scratch_written: usize,
    ) -> Result<(), Error> {
        if !buffer.len().is_multiple_of(16) {
            return Err(Error::IncompleteBlock);
        }
        let mut scratch = [0; 272];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedule holds its key
        // schedule; the buffer holds `len / 16` whole blocks, and it, the
        // chaining value, the schedule and the scratch space are separate
        // valid objects of the sizes of the signature. `select` chose `f` for
        // the CPU's features.
        unsafe {
            f(
                &self.schedule,
                self.rounds,
                iv,
                buffer.as_mut_ptr().cast(),
                buffer.len() / 16,
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the data and our
        // caller's registers: wipe the bytes the function's proved write
        // bound (`scratch_written`) allows it to write, if any.
        if scratch_written != 0 {
            zeroize(&mut scratch[..scratch_written.div_ceil(8)]);
        }
        Ok(())
    }
}

/// The signature of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`.
#[cfg(target_arch = "x86_64")]
type Cbc = unsafe extern "sysv64" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);
/// The signature of `vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type Cbc = unsafe extern "C" fn(
    *const [u8; 240],
    usize,
    *mut [u8; 16],
    *mut [u8; 16],
    usize,
    *mut [u64; 272],
);

impl Drop for AesCbc {
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesCbc, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        for len in [16, 24, 32] {
            assert_eq!(
                AesCbc::new(&[0; 32][..len]).unwrap().backend,
                select(detected())
            );
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use crate::aes::Backend;
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
