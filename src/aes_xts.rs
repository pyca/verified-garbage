//! XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) with 256-, 384- and
//! 512-bit keys (AES-128, AES-192 and AES-256), in place, with ciphertext
//! stealing for a data unit that is not of whole blocks.
//!
//! The data unit is verified assembly: `vg_aes_expand_key` (contract
//! `VG.Spec.Aes.expandKeyContract`) writes the key schedules of `Key1` and
//! `Key2`, and `vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`
//! (`VG.Spec.Xts.aesEncryptUnitContract`, `aesDecryptUnitContract`) replace
//! a whole data unit with its XTS-AES encryption or decryption (§5.3.2,
//! §5.4.2), in constant time, ciphertext stealing for a partial last block
//! included. This module checks the lengths, which the assembly requires.
//!
//! Their variants, with the same contracts, are chosen on CPUs with the
//! features their `_FEATURES` constants name (and the key expansion's): on
//! x86-64, `crate::aes::Backend` chooses `_vaes`, then `_aesni` (both with
//! `vg_aes_expand_key_aesni`), and a CPU with the features of
//! `vg_aes_xts_encrypt_unit_vaes_vpclmul` and
//! `vg_aes_xts_decrypt_unit_vaes_vpclmul` too runs those instead of the
//! `_vaes` ones, and one with those of the `_aesni_pclmul` ones those instead
//! of the `_aesni` ones; on x86, `_aesni`; on AArch64, `_aes`.

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
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_UNIT_AES_FEATURES, VG_AES_XTS_ENCRYPT_UNIT_AES_FEATURES,
    vg_aes_xts_decrypt_unit_aes, vg_aes_xts_encrypt_unit_aes,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_UNIT_AESNI_FEATURES, VG_AES_XTS_ENCRYPT_UNIT_AESNI_FEATURES,
    vg_aes_xts_decrypt_unit_aesni, vg_aes_xts_encrypt_unit_aesni,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_UNIT_AESNI_PCLMUL_FEATURES, VG_AES_XTS_ENCRYPT_UNIT_AESNI_PCLMUL_FEATURES,
    vg_aes_xts_decrypt_unit_aesni_pclmul, vg_aes_xts_encrypt_unit_aesni_pclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_UNIT_VAES_FEATURES, VG_AES_XTS_ENCRYPT_UNIT_VAES_FEATURES,
    vg_aes_xts_decrypt_unit_vaes, vg_aes_xts_encrypt_unit_vaes,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_xts::{
    VG_AES_XTS_DECRYPT_UNIT_VAES_VPCLMUL_FEATURES, VG_AES_XTS_ENCRYPT_UNIT_VAES_VPCLMUL_FEATURES,
    vg_aes_xts_decrypt_unit_vaes_vpclmul, vg_aes_xts_encrypt_unit_vaes_vpclmul,
};
use crate::arch::aes_xts::{vg_aes_xts_decrypt_unit, vg_aes_xts_encrypt_unit};
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

/// The XTS functions a key uses: those of an implementation of AES, or
/// x86-64's `_vaes_vpclmul` or `_aesni_pclmul` ones, with VAES's or
/// AES-NI's key expansion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Impl {
    /// The `vg_aes_xts_*_unit` functions of an implementation of AES.
    Blocks(Backend),
    /// `vg_aes_xts_encrypt_unit_vaes_vpclmul` and
    /// `vg_aes_xts_decrypt_unit_vaes_vpclmul`.
    #[cfg(target_arch = "x86_64")]
    VaesVpclmul,
    /// `vg_aes_xts_encrypt_unit_aesni_pclmul` and
    /// `vg_aes_xts_decrypt_unit_aesni_pclmul`.
    #[cfg(target_arch = "x86_64")]
    AesNiPclmul,
}

impl Impl {
    /// The implementation of AES that expands the keys.
    fn aes(self) -> Backend {
        match self {
            Impl::Blocks(backend) => backend,
            #[cfg(target_arch = "x86_64")]
            Impl::VaesVpclmul => Backend::Vaes,
            #[cfg(target_arch = "x86_64")]
            Impl::AesNiPclmul => Backend::AesNi,
        }
    }
}

/// The best XTS functions a CPU with the features `f` can run: the
/// `_vaes_vpclmul` or `_aesni_pclmul` ones if it has their features and
/// those of the `_vaes` or `_aesni` ones.
#[cfg(target_arch = "x86_64")]
fn select(f: Features) -> Impl {
    const VAES: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_VAES_VPCLMUL_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_VAES_VPCLMUL_FEATURES,
    ]);
    const AESNI: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_AESNI_PCLMUL_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_AESNI_PCLMUL_FEATURES,
    ]);
    match select_aes(f) {
        Backend::Vaes if f.contains(VAES) => Impl::VaesVpclmul,
        Backend::AesNi if f.contains(AESNI) => Impl::AesNiPclmul,
        backend => Impl::Blocks(backend),
    }
}

/// The best XTS functions a CPU with the features `f` can run.
#[cfg(not(target_arch = "x86_64"))]
fn select(f: Features) -> Impl {
    Impl::Blocks(select_aes(f))
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions.
#[cfg(target_arch = "x86_64")]
fn select_aes(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_AESNI_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_AESNI_FEATURES,
    ]);
    const VAES: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_VAES_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_VAES_FEATURES,
    ]);
    Backend::select_for(f, VAES, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions.
#[cfg(target_arch = "x86")]
fn select_aes(f: Features) -> Backend {
    const AESNI: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_AESNI_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_AESNI_FEATURES,
    ]);
    Backend::select_for(f, AESNI)
}

/// The best implementation of AES a CPU with the features `f` can run, with
/// its XTS functions.
#[cfg(target_arch = "aarch64")]
fn select_aes(f: Features) -> Backend {
    const AES: Features = Features::all(&[
        VG_AES_XTS_ENCRYPT_UNIT_AES_FEATURES,
        VG_AES_XTS_DECRYPT_UNIT_AES_FEATURES,
    ]);
    Backend::select_for(f, AES)
}

/// The only implementation of AES on ARMv7, PPC64LE and RISC-V.
#[cfg(any(
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
fn select_aes(f: Features) -> Backend {
    Backend::select(f)
}

/// The most blocks a data unit may have (IEEE Std 1619-2007 §5.1, NIST SP
/// 800-38E).
pub const MAX_BLOCKS: usize = 1 << 20;

/// Why an XTS-AES operation failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The key is not 32, 48 or 64 bytes long.
    InvalidKeyLength,
    /// The two halves of the key, `Key1` and `Key2`, are equal, which
    /// SP 800-38E's implementation guidance (FIPS 140-3 IG C.I) forbids.
    EqualKeyHalves,
    /// The data unit is shorter than one block (16 bytes).
    DataUnitTooShort,
    /// The data unit is longer than [`MAX_BLOCKS`] blocks.
    DataUnitTooLong,
}

crate::error::impl_error! {
    Error {
        InvalidKeyLength => "invalid AES-XTS key length",
        EqualKeyHalves => "AES-XTS key halves are equal",
        DataUnitTooShort => "AES-XTS data unit is shorter than a block",
        DataUnitTooLong => "AES-XTS data unit is too long",
    }
}

/// An XTS-AES key, `Key1 ‖ Key2`, expanded for encryption and decryption.
///
/// Each operation takes a whole data unit, of 16 bytes or more, and its
/// 16-byte tweak value `i` (for a storage device, usually the data unit's
/// number, little-endian).
pub struct AesXts {
    /// The key schedule of `Key1`, which enciphers the data.
    data_schedule: [u8; 240],
    /// The key schedule of `Key2`, which enciphers the tweak value.
    tweak_schedule: [u8; 240],
    /// The number of rounds of AES: 10, 12 or 14.
    rounds: usize,
    /// The XTS functions, and the implementation of AES the others use.
    imp: Impl,
}

/// The signature of `vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`.
#[cfg(target_arch = "x86_64")]
type Unit = unsafe extern "sysv64" fn(
    *const [u8; 240],
    *const [u8; 240],
    usize,
    *const [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 304],
);
/// The signature of `vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit`.
#[cfg(any(
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "powerpc64",
    target_arch = "riscv64"
))]
type Unit = unsafe extern "C" fn(
    *const [u8; 240],
    *const [u8; 240],
    usize,
    *const [u8; 16],
    *mut u8,
    usize,
    *mut [u64; 304],
);

impl AesXts {
    /// Expands a 32-, 48- or 64-byte key, `Key1 ‖ Key2`, for use in either
    /// direction.
    pub fn new(key: &[u8]) -> Result<Self, Error> {
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(Error::InvalidKeyLength);
        }
        let (key1, key2) = key.split_at(key.len() / 2);
        // Without branching on the key's bytes, only on whether they are all
        // equal.
        if crate::ct::eq(key1, key2) {
            return Err(Error::EqualKeyHalves);
        }
        let imp = select(detected());
        let expand = instance!(
            imp.aes(),
            vg_aes_expand_key,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aesni,
            vg_aes_expand_key_aes
        );
        let mut data_schedule = [0; 240];
        let mut tweak_schedule = [0; 240];
        // SAFETY: each half of the key is 16, 24 or 32 bytes long; it and
        // its schedule are separate valid buffers of the sizes of the
        // signature, and `select` chose `expand` for the CPU's features. The
        // function zeroes its working space on its own stack before
        // returning.
        unsafe {
            expand(key1.as_ptr(), key1.len(), &mut data_schedule);
            expand(key2.as_ptr(), key2.len(), &mut tweak_schedule);
        }
        Ok(Self {
            data_schedule,
            tweak_schedule,
            rounds: key1.len() / 4 + 6,
            imp,
        })
    }

    /// Encrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.3.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`MAX_BLOCKS`] blocks.
    pub fn encrypt(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f: Unit = match self.imp {
            Impl::Blocks(backend) => instance!(
                backend,
                vg_aes_xts_encrypt_unit,
                vg_aes_xts_encrypt_unit_aesni,
                vg_aes_xts_encrypt_unit_vaes,
                vg_aes_xts_encrypt_unit_aes
            ),
            #[cfg(target_arch = "x86_64")]
            Impl::VaesVpclmul => vg_aes_xts_encrypt_unit_vaes_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Impl::AesNiPclmul => vg_aes_xts_encrypt_unit_aesni_pclmul,
        };
        self.unit(f, i, buffer)
    }

    /// Decrypts the data unit `buffer` in place with the tweak value `i`
    /// (§5.4.2). Returns an error without changing the buffer if it is
    /// shorter than 16 bytes or longer than [`MAX_BLOCKS`] blocks.
    pub fn decrypt(&self, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        let f: Unit = match self.imp {
            Impl::Blocks(backend) => instance!(
                backend,
                vg_aes_xts_decrypt_unit,
                vg_aes_xts_decrypt_unit_aesni,
                vg_aes_xts_decrypt_unit_vaes,
                vg_aes_xts_decrypt_unit_aes
            ),
            #[cfg(target_arch = "x86_64")]
            Impl::VaesVpclmul => vg_aes_xts_decrypt_unit_vaes_vpclmul,
            #[cfg(target_arch = "x86_64")]
            Impl::AesNiPclmul => vg_aes_xts_decrypt_unit_aesni_pclmul,
        };
        self.unit(f, i, buffer)
    }

    /// Runs `f` on the data unit `buffer` with the tweak value `i`, after
    /// checking its length.
    fn unit(&self, f: Unit, i: &[u8; 16], buffer: &mut [u8]) -> Result<(), Error> {
        if buffer.len() < 16 {
            return Err(Error::DataUnitTooShort);
        }
        if buffer.len() > 16 * MAX_BLOCKS {
            return Err(Error::DataUnitTooLong);
        }
        let mut scratch = [0; 304];
        // SAFETY: `rounds` is 10, 12 or 14 and the schedules hold its key
        // schedules; `buffer` holds `len` bytes, at least 16 and at most
        // `MAX_BLOCKS` blocks; it, the tweak value, the schedules and the
        // scratch space are separate valid objects of the sizes of the
        // signature. `select` chose `f` for the CPU's features.
        unsafe {
            f(
                &self.data_schedule,
                &self.tweak_schedule,
                self.rounds,
                i,
                buffer.as_mut_ptr(),
                buffer.len(),
                &mut scratch,
            );
        }
        // The scratch space may hold the key schedule, the tweaks, the data
        // and our caller's registers.
        zeroize(&mut scratch);
        Ok(())
    }
}

impl Drop for AesXts {
    fn drop(&mut self) {
        zeroize(&mut self.data_schedule);
        zeroize(&mut self.tweak_schedule);
    }
}

#[cfg(test)]
mod tests {
    use super::{AesXts, select};
    use crate::cpu::detected;

    /// A new key uses the implementation chosen for the CPU's features.
    #[test]
    fn select_detected() {
        let key: [u8; 64] = core::array::from_fn(|i| i as u8);
        for len in [32, 48, 64] {
            assert_eq!(AesXts::new(&key[..len]).unwrap().imp, select(detected()));
        }
    }

    /// Each implementation is chosen for the features of its functions.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn select_features() {
        use super::Impl;
        use crate::aes::Backend;
        use verified_garbage_cpu::{Features, feature};
        assert_eq!(select(Features(0)), Impl::Blocks(Backend::Scalar));
        #[cfg(target_arch = "x86_64")]
        {
            let aesni = Features(feature::AES | feature::SSSE3);
            assert_eq!(select(aesni), Impl::Blocks(Backend::AesNi));
            let vaes = Features(
                feature::AES | feature::AVX | feature::AVX2 | feature::SSSE3 | feature::VAES,
            );
            assert_eq!(select(vaes), Impl::Blocks(Backend::Vaes));
            let one_pass = Features(
                feature::AES
                    | feature::AVX
                    | feature::AVX2
                    | feature::SSSE3
                    | feature::VAES
                    | feature::VPCLMULQDQ,
            );
            assert_eq!(select(one_pass), Impl::VaesVpclmul);
            assert_eq!(Impl::VaesVpclmul.aes(), Backend::Vaes);
            let aesni_pclmul =
                Features(feature::AES | feature::AVX | feature::PCLMULQDQ | feature::SSSE3);
            assert_eq!(select(aesni_pclmul), Impl::AesNiPclmul);
            assert_eq!(Impl::AesNiPclmul.aes(), Backend::AesNi);
            // VPCLMULQDQ without VAES, and PCLMULQDQ without AVX.
            let no_vaes = Features(
                feature::AES | feature::AVX | feature::AVX2 | feature::SSSE3 | feature::VPCLMULQDQ,
            );
            assert_eq!(select(no_vaes), Impl::Blocks(Backend::AesNi));
            let no_avx = Features(feature::AES | feature::PCLMULQDQ | feature::SSSE3);
            assert_eq!(select(no_avx), Impl::Blocks(Backend::AesNi));
        }
        #[cfg(target_arch = "x86")]
        assert_eq!(select(Features(feature::AES)), Impl::Blocks(Backend::AesNi));
        #[cfg(target_arch = "aarch64")]
        assert_eq!(select(Features(feature::AES)), Impl::Blocks(Backend::Aes));
    }
}
