//! AES-GCM-SIV (RFC 8452) with 128- and 256-bit keys: nonce-misuse-resistant
//! authenticated encryption.
//!
//! Repeating a nonce under one key reveals only whether two messages with the
//! same associated data are equal.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::aead::aes_gcm::{Backend, instance, select as select_gcm};
use crate::arch::aes::vg_aes_expand_key;
#[cfg(target_arch = "aarch64")]
use crate::arch::aes::vg_aes_expand_key_aes;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes::vg_aes_expand_key_aesni;
use crate::arch::aes_gcm_siv::{vg_aes_gcm_siv_open, vg_aes_gcm_siv_seal};
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_gcm_siv::{
    vg_aes_gcm_siv_open_aes, vg_aes_gcm_siv_open_aes_sha3, vg_aes_gcm_siv_seal_aes,
    vg_aes_gcm_siv_seal_aes_sha3,
};
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::arch::aes_gcm_siv::{
    vg_aes_gcm_siv_open_aesni, vg_aes_gcm_siv_open_aesni_pclmul, vg_aes_gcm_siv_open_pclmul,
    vg_aes_gcm_siv_seal_aesni, vg_aes_gcm_siv_seal_aesni_pclmul, vg_aes_gcm_siv_seal_pclmul,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_gcm_siv::{
    vg_aes_gcm_siv_open_aesni_pclmul_avx, vg_aes_gcm_siv_open_aesni_vpclmul,
    vg_aes_gcm_siv_open_vaes, vg_aes_gcm_siv_open_vaes_pclmul, vg_aes_gcm_siv_open_vaes_vpclmul,
    vg_aes_gcm_siv_open_vaes_vpclmul_avx512, vg_aes_gcm_siv_open_vpclmul,
    vg_aes_gcm_siv_seal_aesni_pclmul_avx, vg_aes_gcm_siv_seal_aesni_vpclmul,
    vg_aes_gcm_siv_seal_vaes, vg_aes_gcm_siv_seal_vaes_pclmul, vg_aes_gcm_siv_seal_vaes_vpclmul,
    vg_aes_gcm_siv_seal_vaes_vpclmul_avx512, vg_aes_gcm_siv_seal_vpclmul,
};
use crate::cpu::detected;
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;

/// SIV can use AVX2 copies independently of its AES and GHASH callees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SivBackend {
    Gcm(Backend),
    #[cfg(target_arch = "x86_64")]
    Avx2(Backend),
}

impl SivBackend {
    /// Below eight whole blocks neither copy loop uses AVX2. Keep those
    /// messages on the ordinary instance instead of its extra loop checks.
    #[cfg(target_arch = "x86_64")]
    fn for_lengths(self, aad_len: usize, len: usize) -> Self {
        match self {
            Self::Avx2(b) if aad_len < 128 && len < 128 => Self::Gcm(b),
            _ => self,
        }
    }

    fn gcm(self) -> Backend {
        match self {
            Self::Gcm(b) => b,
            #[cfg(target_arch = "x86_64")]
            Self::Avx2(b) => b,
        }
    }
}

#[cfg(target_arch = "x86_64")]
use crate::arch::aes_gcm_siv::{
    VG_AES_GCM_SIV_SEAL_AVX2_FEATURES, vg_aes_gcm_siv_open_aesni_avx2,
    vg_aes_gcm_siv_open_aesni_pclmul_avx_avx2, vg_aes_gcm_siv_open_aesni_pclmul_avx2,
    vg_aes_gcm_siv_open_aesni_vpclmul_avx2, vg_aes_gcm_siv_open_avx2,
    vg_aes_gcm_siv_open_pclmul_avx2, vg_aes_gcm_siv_open_vaes_avx2,
    vg_aes_gcm_siv_open_vaes_pclmul_avx2, vg_aes_gcm_siv_open_vaes_vpclmul_avx2,
    vg_aes_gcm_siv_open_vaes_vpclmul_avx512_avx2, vg_aes_gcm_siv_open_vpclmul_avx2,
    vg_aes_gcm_siv_seal_aesni_avx2, vg_aes_gcm_siv_seal_aesni_pclmul_avx_avx2,
    vg_aes_gcm_siv_seal_aesni_pclmul_avx2, vg_aes_gcm_siv_seal_aesni_vpclmul_avx2,
    vg_aes_gcm_siv_seal_avx2, vg_aes_gcm_siv_seal_pclmul_avx2, vg_aes_gcm_siv_seal_vaes_avx2,
    vg_aes_gcm_siv_seal_vaes_pclmul_avx2, vg_aes_gcm_siv_seal_vaes_vpclmul_avx2,
    vg_aes_gcm_siv_seal_vaes_vpclmul_avx512_avx2, vg_aes_gcm_siv_seal_vpclmul_avx2,
};

fn select(f: verified_garbage_cpu::Features) -> SivBackend {
    let b = select_gcm(f);
    #[cfg(target_arch = "x86_64")]
    if f.contains(VG_AES_GCM_SIV_SEAL_AVX2_FEATURES) {
        return SivBackend::Avx2(b);
    }
    SivBackend::Gcm(b)
}

/// The longest plaintext and additional data, in bytes (§6: `P_MAX` and
/// `A_MAX`, `2^36`).
const MAX_LEN: u64 = 1 << 36;

/// Why an AES-GCM-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The plaintext or ciphertext is longer than `2^36` bytes (§6).
    InvalidTextLength,
    /// The additional data is longer than `2^36` bytes (§6).
    InvalidAadLength,
    /// The tag does not match: the ciphertext, the additional data or the
    /// nonce is not what was authenticated under this key.
    TagMismatch,
}

crate::error::impl_error! {
    Error {
        InvalidTextLength => "AES-GCM-SIV text is too long",
        InvalidAadLength => "AES-GCM-SIV additional data is too long",
        TagMismatch => "AES-GCM-SIV tag does not match",
    }
}

/// An AES-GCM-SIV key: the AES key schedule of the key-generating key.
#[derive(Clone)]
pub struct AesGcmSiv {
    /// The key schedule `vg_aes_expand_key` writes.
    schedule: [u8; 240],
    /// The number of rounds of AES: 10 or 14.
    rounds: usize,
    /// The variants of the functions to call.
    backend: SivBackend,
}

impl Drop for AesGcmSiv {
    /// Wipes the key schedule.
    fn drop(&mut self) {
        zeroize(&mut self.schedule);
    }
}

/// Checks the lengths of §6: of the additional data and of the text.
fn check(aad_len: u64, len: u64) -> Result<(), Error> {
    if len > MAX_LEN {
        return Err(Error::InvalidTextLength);
    }
    if aad_len > MAX_LEN {
        return Err(Error::InvalidAadLength);
    }
    Ok(())
}

impl AesGcmSiv {
    /// Prepares the key-generating key `key`, which must be 16 or 32 bytes
    /// long (AEAD_AES_128_GCM_SIV, AEAD_AES_256_GCM_SIV).
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 16 | 32) {
            return Err(InvalidKeyLength);
        }
        let backend = select(detected());
        // The variants whose suffix names `aesni` or `vaes` take
        // `vg_aes_expand_key_aesni`'s schedule, AArch64's
        // `vg_aes_expand_key_aes`'s.
        let expand = instance!(backend.gcm(), vg_aes_expand_key,
            x86_64: [vg_aes_expand_key_aesni, vg_aes_expand_key, vg_aes_expand_key_aesni],
            vaes: [vg_aes_expand_key_aesni, vg_aes_expand_key, vg_aes_expand_key_aesni,
                vg_aes_expand_key_aesni, vg_aes_expand_key_aesni, vg_aes_expand_key_aesni],
            avx: [vg_aes_expand_key_aesni],
            aarch64: [vg_aes_expand_key_aes, vg_aes_expand_key_aes]);
        // The schedule is written in the value returned, not copied into it
        // after: a copy reads the schedule's 16-byte stores with wider loads,
        // which cannot take them from the store buffer and wait for them.
        let mut k = Ok(AesGcmSiv {
            schedule: [0; 240],
            rounds: key.len() / 4 + 6,
            backend,
        });
        if let Ok(k) = &mut k {
            // SAFETY: `key` is valid for reads of `key.len()` bytes, which is
            // 16 or 32, and `k.schedule` for reads and writes of 240 bytes.
            // They are distinct objects, so they do not overlap, nor do they
            // overlap the return address on the stack or the stack below it,
            // and neither wraps around the end of the address space. The CPU
            // has the features of the implementation selected.
            unsafe { expand(key.as_ptr(), key.len(), &mut k.schedule) };
        }
        k
    }

    /// Encryption (§4): encrypts `data` in place under the 12-byte `nonce`,
    /// and returns the 16-byte tag, which authenticates the plaintext and
    /// `aad`. The RFC's ciphertext is `data` followed by the tag. Reusing a
    /// nonce with the same key reveals only whether two messages (with
    /// their additional data) are equal.
    pub fn encrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
    ) -> Result<[u8; 16], Error> {
        check(aad.len() as u64, data.len() as u64)?;
        let backend = self.backend;
        #[cfg(target_arch = "x86_64")]
        let backend = backend.for_lengths(aad.len(), data.len());
        let seal = match backend {
            SivBackend::Gcm(b) => instance!(b, vg_aes_gcm_siv_seal,
            x86_64: [vg_aes_gcm_siv_seal_aesni, vg_aes_gcm_siv_seal_pclmul, vg_aes_gcm_siv_seal_aesni_pclmul],
            vaes: [vg_aes_gcm_siv_seal_vaes, vg_aes_gcm_siv_seal_vpclmul, vg_aes_gcm_siv_seal_vaes_pclmul,
                vg_aes_gcm_siv_seal_aesni_vpclmul, vg_aes_gcm_siv_seal_vaes_vpclmul,
                vg_aes_gcm_siv_seal_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_siv_seal_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_siv_seal_aes, vg_aes_gcm_siv_seal_aes_sha3]),
            #[cfg(target_arch = "x86_64")]
            SivBackend::Avx2(b) => instance!(b, vg_aes_gcm_siv_seal_avx2,
            x86_64: [vg_aes_gcm_siv_seal_aesni_avx2, vg_aes_gcm_siv_seal_pclmul_avx2, vg_aes_gcm_siv_seal_aesni_pclmul_avx2],
            vaes: [vg_aes_gcm_siv_seal_vaes_avx2, vg_aes_gcm_siv_seal_vpclmul_avx2, vg_aes_gcm_siv_seal_vaes_pclmul_avx2,
                vg_aes_gcm_siv_seal_aesni_vpclmul_avx2, vg_aes_gcm_siv_seal_vaes_vpclmul_avx2,
                vg_aes_gcm_siv_seal_vaes_vpclmul_avx512_avx2],
            avx: [vg_aes_gcm_siv_seal_aesni_pclmul_avx_avx2],
            aarch64: [vg_aes_gcm_siv_seal_aes, vg_aes_gcm_siv_seal_aes_sha3]),
        };
        let mut tag = [0u8; 16];
        // SAFETY: `self.schedule` is the key schedule `vg_aes_expand_key`
        // wrote for `self.rounds` (10 or 14) rounds, valid for reads of 240
        // bytes. `nonce` (12 bytes) and `aad` are valid for reads of their
        // lengths, `data` for reads and writes of `data.len()` bytes, and
        // `tag` for reads and writes of 16. `data` and `tag` are unique
        // borrows, so they overlap neither each other nor the other buffers;
        // no buffer overlaps the arguments on the stack, the return address
        // or the stack below it, and none wraps around the end of the address
        // space. The CPU has the features of the implementation selected
        // (see `features_cover_instances`).
        unsafe {
            seal(
                &self.schedule,
                self.rounds,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut tag,
            )
        };
        Ok(tag)
    }

    /// Decryption (§5): if `tag` authenticates the ciphertext in `data`,
    /// `aad` and `nonce`, decrypts `data` in place. Otherwise returns an
    /// error and overwrites `data` with zeros.
    pub fn decrypt_in_place(
        &self,
        nonce: &[u8; 12],
        aad: &[u8],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        check(aad.len() as u64, data.len() as u64)?;
        let backend = self.backend;
        #[cfg(target_arch = "x86_64")]
        let backend = backend.for_lengths(aad.len(), data.len());
        let open = match backend {
            SivBackend::Gcm(b) => instance!(b, vg_aes_gcm_siv_open,
            x86_64: [vg_aes_gcm_siv_open_aesni, vg_aes_gcm_siv_open_pclmul, vg_aes_gcm_siv_open_aesni_pclmul],
            vaes: [vg_aes_gcm_siv_open_vaes, vg_aes_gcm_siv_open_vpclmul, vg_aes_gcm_siv_open_vaes_pclmul,
                vg_aes_gcm_siv_open_aesni_vpclmul, vg_aes_gcm_siv_open_vaes_vpclmul,
                vg_aes_gcm_siv_open_vaes_vpclmul_avx512],
            avx: [vg_aes_gcm_siv_open_aesni_pclmul_avx],
            aarch64: [vg_aes_gcm_siv_open_aes, vg_aes_gcm_siv_open_aes_sha3]),
            #[cfg(target_arch = "x86_64")]
            SivBackend::Avx2(b) => instance!(b, vg_aes_gcm_siv_open_avx2,
            x86_64: [vg_aes_gcm_siv_open_aesni_avx2, vg_aes_gcm_siv_open_pclmul_avx2, vg_aes_gcm_siv_open_aesni_pclmul_avx2],
            vaes: [vg_aes_gcm_siv_open_vaes_avx2, vg_aes_gcm_siv_open_vpclmul_avx2, vg_aes_gcm_siv_open_vaes_pclmul_avx2,
                vg_aes_gcm_siv_open_aesni_vpclmul_avx2, vg_aes_gcm_siv_open_vaes_vpclmul_avx2,
                vg_aes_gcm_siv_open_vaes_vpclmul_avx512_avx2],
            avx: [vg_aes_gcm_siv_open_aesni_pclmul_avx_avx2],
            aarch64: [vg_aes_gcm_siv_open_aes, vg_aes_gcm_siv_open_aes_sha3]),
        };
        // SAFETY: as in `encrypt_in_place`, with the received tag `tag`
        // valid for reads of 16 bytes, which `data`, a unique borrow, does not
        // overlap.
        let ok = unsafe {
            open(
                &self.schedule,
                self.rounds,
                nonce,
                aad.as_ptr(),
                aad.len(),
                data.as_mut_ptr(),
                data.len(),
                tag,
            )
        };
        // `open`'s contract leaves the plaintext in `data` if it returns 1,
        // and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AesGcmSiv, Error, InvalidKeyLength, MAX_LEN, check};
    use crate::aead::aes_gcm::{Backend, instance};
    #[cfg(target_arch = "aarch64")]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AES_FEATURES, VG_AES_GCM_SIV_OPEN_AES_SHA3_FEATURES,
        VG_AES_GCM_SIV_SEAL_AES_FEATURES, VG_AES_GCM_SIV_SEAL_AES_SHA3_FEATURES,
    };
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AESNI_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_FEATURES,
        VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_PCLMUL_FEATURES,
    };
    #[cfg(target_arch = "x86_64")]
    use crate::arch::aes_gcm_siv::{
        VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_FEATURES,
        VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VPCLMUL_FEATURES,
    };
    use verified_garbage_cpu::Features;

    /// The features of every instance of a backend are within those it is
    /// selected by (AES-GCM's `seal`'s).
    #[test]
    fn features_cover_instances() {
        const NONE: Features = Features(0);
        for &(b, need) in Backend::ALL {
            let seal = instance!(b, NONE,
                x86_64: [VG_AES_GCM_SIV_SEAL_AESNI_FEATURES, VG_AES_GCM_SIV_SEAL_PCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_FEATURES],
                vaes: [VG_AES_GCM_SIV_SEAL_VAES_FEATURES, VG_AES_GCM_SIV_SEAL_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_FEATURES,
                    VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_FEATURES,
                    VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_FEATURES],
                avx: [VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_FEATURES],
                aarch64: [VG_AES_GCM_SIV_SEAL_AES_FEATURES, VG_AES_GCM_SIV_SEAL_AES_SHA3_FEATURES]);
            let open = instance!(b, NONE,
                x86_64: [VG_AES_GCM_SIV_OPEN_AESNI_FEATURES, VG_AES_GCM_SIV_OPEN_PCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_FEATURES],
                vaes: [VG_AES_GCM_SIV_OPEN_VAES_FEATURES, VG_AES_GCM_SIV_OPEN_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_FEATURES,
                    VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_FEATURES,
                    VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_FEATURES],
                avx: [VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_FEATURES],
                aarch64: [VG_AES_GCM_SIV_OPEN_AES_FEATURES, VG_AES_GCM_SIV_OPEN_AES_SHA3_FEATURES]);
            assert!(need.contains(seal) && need.contains(open), "{b:?}");
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn avx2_copy_selection_and_features() {
        use super::{SivBackend, select};
        use crate::arch::aes_gcm_siv::{
            VG_AES_GCM_SIV_OPEN_AESNI_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_PCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_AVX2_FEATURES,
            VG_AES_GCM_SIV_OPEN_VPCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_PCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_AVX2_FEATURES,
            VG_AES_GCM_SIV_SEAL_VPCLMUL_AVX2_FEATURES,
        };
        for &(b, base_need) in Backend::ALL {
            let seal = instance!(b, VG_AES_GCM_SIV_SEAL_AVX2_FEATURES,
                x86_64: [VG_AES_GCM_SIV_SEAL_AESNI_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_PCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX2_FEATURES],
                vaes: [VG_AES_GCM_SIV_SEAL_VAES_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_VPCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_SEAL_VAES_PCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_AESNI_VPCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_SEAL_VAES_VPCLMUL_AVX512_AVX2_FEATURES],
                avx: [VG_AES_GCM_SIV_SEAL_AESNI_PCLMUL_AVX_AVX2_FEATURES],
                aarch64: [NONE, NONE]);
            let open = instance!(b, VG_AES_GCM_SIV_OPEN_AVX2_FEATURES,
                x86_64: [VG_AES_GCM_SIV_OPEN_AESNI_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_PCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX2_FEATURES],
                vaes: [VG_AES_GCM_SIV_OPEN_VAES_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_VPCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_OPEN_VAES_PCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_AESNI_VPCLMUL_AVX2_FEATURES,
                    VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX2_FEATURES, VG_AES_GCM_SIV_OPEN_VAES_VPCLMUL_AVX512_AVX2_FEATURES],
                avx: [VG_AES_GCM_SIV_OPEN_AESNI_PCLMUL_AVX_AVX2_FEATURES],
                aarch64: [NONE, NONE]);
            let need = Features::all(&[base_need, seal]);
            assert!(need.contains(open));
            assert_eq!(select(need).gcm(), super::select_gcm(need));
            assert!(matches!(select(need), SivBackend::Avx2(_)));
            for aad_len in [0, 127, 128, 129] {
                for len in [0, 127, 128, 129] {
                    let chosen = select(need).for_lengths(aad_len, len);
                    if aad_len < 128 && len < 128 {
                        assert_eq!(chosen, SivBackend::Gcm(super::select_gcm(need)));
                    } else {
                        assert_eq!(chosen, select(need));
                    }
                }
            }
            let key = match b {
                Backend::Scalar | Backend::Pclmul | Backend::Vpclmul => Features(0),
                _ => crate::arch::aes::VG_AES_EXPAND_KEY_AESNI_FEATURES,
            };
            assert!(seal.contains(key));
            for bit in 0..32 {
                if VG_AES_GCM_SIV_SEAL_AVX2_FEATURES.0 & (1 << bit) != 0 {
                    assert!(matches!(
                        select(Features(need.0 & !(1 << bit))),
                        SivBackend::Gcm(_)
                    ));
                }
            }
        }
        assert_eq!(select(Features(0)), SivBackend::Gcm(Backend::Scalar));
    }

    /// The lengths of §6, which no test can allocate.
    #[test]
    fn lengths() {
        assert_eq!(check(MAX_LEN, MAX_LEN), Ok(()));
        assert_eq!(check(0, MAX_LEN + 1), Err(Error::InvalidTextLength));
        assert_eq!(check(MAX_LEN + 1, 0), Err(Error::InvalidAadLength));
    }

    #[test]
    fn errors() {
        let key = [0u8; 40];
        for n in [0, 15, 17, 24, 31, 33, 40] {
            assert_eq!(AesGcmSiv::new(&key[..n]).err(), Some(InvalidKeyLength));
        }
    }
}
