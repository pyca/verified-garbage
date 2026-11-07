//! AES-SIV (RFC 5297) with 256-, 384- and 512-bit keys (AES-128, AES-192 and
//! AES-256 for each half): deterministic authenticated encryption, and
//! nonce-based when the caller passes a nonce as the last associated-data
//! component (§3).

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::aes_siv::{
    vg_aes_siv_decrypt_auto, vg_aes_siv_encrypt_auto, vg_aes_siv_init_auto,
};
use crate::error::InvalidKeyLength;
use crate::zeroize::zeroize;
use core::mem::MaybeUninit;

// The `_aes_cbc` (AArch64) or `_aesni_cbc` (x86-64) implementations, which
// the dispatchers never choose: `encrypt` and `decrypt` run them on long
// inputs (`chains_long`), where they are faster.
#[cfg(target_arch = "aarch64")]
use crate::arch::aes_siv::{
    VG_AES_SIV_DECRYPT_AES_CBC_FEATURES as DECRYPT_CBC_FEATURES,
    VG_AES_SIV_ENCRYPT_AES_CBC_FEATURES as ENCRYPT_CBC_FEATURES,
    vg_aes_siv_decrypt_aes_cbc as decrypt_cbc, vg_aes_siv_encrypt_aes_cbc as encrypt_cbc,
};
#[cfg(target_arch = "x86_64")]
use crate::arch::aes_siv::{
    VG_AES_SIV_DECRYPT_AESNI_CBC_FEATURES as DECRYPT_CBC_FEATURES,
    VG_AES_SIV_ENCRYPT_AESNI_CBC_FEATURES as ENCRYPT_CBC_FEATURES,
    vg_aes_siv_decrypt_aesni_cbc as decrypt_cbc, vg_aes_siv_encrypt_aesni_cbc as encrypt_cbc,
};
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
use crate::cpu::detected;

/// A 16-byte block.
type Block = [u8; 16];

/// Whether `encrypt` and `decrypt` should run the `_aes_cbc` instances (on
/// AArch64 with the AES extension) or the `_aesni_cbc` ones (on x86-64 with
/// AES-NI) rather than the others: when the associated-data components
/// `ads` and the `len` bytes of data total more than 32 bytes, as AES-CMAC's
/// updates (`crate::cmac::aes`).
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
fn chains_long(ads: &[&[u8]], len: usize) -> bool {
    ads.iter()
        .fold(len, |total, ad| total.saturating_add(ad.len()))
        > 32
}

/// `vg_aes_siv_encrypt` of the components `ads`, described by `descs`: its
/// `_aes_cbc` or `_aesni_cbc` implementation on long inputs (`chains_long`)
/// if the CPU has its features, else its dispatcher's choice.
///
/// # Safety
///
/// `vg_aes_siv_encrypt`'s, for the descriptors `descs` of `ads`.
unsafe fn encrypt(
    ctx: &[u64; 64],
    rounds: usize,
    ads: &[&[u8]],
    descs: *const [usize; 2],
    data: &mut [u8],
    siv: &mut Block,
) {
    let (d, len) = (data.as_mut_ptr(), data.len());
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if chains_long(ads, len) && detected().contains(ENCRYPT_CBC_FEATURES) {
        // SAFETY: the caller's, and the CPU has the features it needs.
        return unsafe { encrypt_cbc(ctx, rounds, descs, ads.len(), d, len, siv) };
    }
    // SAFETY: the caller's. The dispatcher calls only an implementation the
    // CPU has the features of.
    unsafe { vg_aes_siv_encrypt_auto(ctx, rounds, descs, ads.len(), d, len, siv) }
}

/// `vg_aes_siv_decrypt`, chosen as `encrypt` chooses `vg_aes_siv_encrypt`.
///
/// # Safety
///
/// `vg_aes_siv_decrypt`'s, for the descriptors `descs` of `ads`.
unsafe fn decrypt(
    ctx: &[u64; 64],
    rounds: usize,
    ads: &[&[u8]],
    descs: *const [usize; 2],
    data: &mut [u8],
    tag: &Block,
) -> u32 {
    let (d, len) = (data.as_mut_ptr(), data.len());
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    if chains_long(ads, len) && detected().contains(DECRYPT_CBC_FEATURES) {
        // SAFETY: the caller's, and the CPU has the features it needs.
        return unsafe { decrypt_cbc(ctx, rounds, descs, ads.len(), d, len, tag) };
    }
    // SAFETY: the caller's. The dispatcher calls only an implementation the
    // CPU has the features of.
    unsafe { vg_aes_siv_decrypt_auto(ctx, rounds, descs, ads.len(), d, len, tag) }
}

/// Why an AES-SIV operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// More than [`AesSiv::MAX_COMPONENTS`] associated-data components.
    TooManyComponents,
    /// The synthetic IV does not match: the ciphertext or the associated
    /// data is not what was authenticated under this key.
    TagMismatch,
}

crate::error::impl_error! {
    Error {
        TooManyComponents => "too many AES-SIV associated-data components",
        TagMismatch => "AES-SIV synthetic IV does not match",
    }
}

/// An AES-SIV key: its key context. [`encrypt_in_place`](Self::encrypt_in_place)
/// is `SIV-ENCRYPT` and [`decrypt_in_place`](Self::decrypt_in_place)
/// `SIV-DECRYPT` (RFC 5297 §2.6, §2.7), with the synthetic IV `V` apart from
/// the data: the RFC's output is `V` followed by the ciphertext.
#[derive(Clone)]
pub struct AesSiv {
    /// The key context `vg_aes_siv_init` writes (`VG.Spec.Siv.KeyRepr`).
    ctx: [u64; 64],
    /// The number of rounds of AES for each half of the key.
    rounds: usize,
}

impl Drop for AesSiv {
    /// Wipes the key context.
    fn drop(&mut self) {
        zeroize(&mut self.ctx);
    }
}

impl AesSiv {
    /// The size of the synthetic IV, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// The most associated-data components a message may have (RFC 5297
    /// §2.6: S2V takes at most 127 strings, the last the plaintext).
    pub const MAX_COMPONENTS: usize = 126;

    /// Prepares `key`, which must be 32, 48 or 64 bytes long: `K1`, for
    /// S2V, then `K2`, for CTR, each 16, 24 or 32 bytes.
    pub fn new(key: &[u8]) -> Result<Self, InvalidKeyLength> {
        if !matches!(key.len(), 32 | 48 | 64) {
            return Err(InvalidKeyLength);
        }
        let mut k = AesSiv {
            ctx: [0; 64],
            rounds: key.len() / 8 + 6,
        };
        // SAFETY: `key` is valid for reads of `key.len()` bytes, which is 32,
        // 48 or 64, and `k.ctx` for reads and writes of 512 bytes. They are
        // distinct objects, so they do not overlap each other, the return
        // addresses on the stack (on x86 and x86-64) or the stack below them that
        // the function uses, and neither wraps around the end of the address
        // space. The dispatcher calls only an implementation the CPU has the
        // features of.
        unsafe { vg_aes_siv_init_auto(key.as_ptr(), key.len(), &mut k.ctx) };
        Ok(k)
    }

    /// Writes the descriptors of the associated-data components `ads` to the
    /// start of `descs`, as `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt`
    /// take them: each its address and its length. Only those `ads.len()`
    /// entries are written (the rest stay uninitialized, and the functions
    /// read only those), so a short list costs no more than its length.
    fn descriptors(
        ads: &[&[u8]],
        descs: &mut [MaybeUninit<[usize; 2]>; Self::MAX_COMPONENTS],
    ) -> Result<*const [usize; 2], Error> {
        if ads.len() > Self::MAX_COMPONENTS {
            return Err(Error::TooManyComponents);
        }
        for (d, s) in descs.iter_mut().zip(ads) {
            d.write([s.as_ptr() as usize, s.len()]);
        }
        Ok(descs.as_ptr().cast())
    }

    /// `SIV-ENCRYPT` (RFC 5297 §2.6): encrypts `data` in place, and returns
    /// the synthetic IV `V`, which authenticates the plaintext and the
    /// associated-data components `ads` (at most
    /// [`MAX_COMPONENTS`](Self::MAX_COMPONENTS) of them, in order). The same
    /// key, components and plaintext always give the same output: a
    /// protocol that must hide repeated messages passes a nonce as the last
    /// component.
    pub fn encrypt_in_place(&self, ads: &[&[u8]], data: &mut [u8]) -> Result<Block, Error> {
        let mut storage = [const { MaybeUninit::uninit() }; Self::MAX_COMPONENTS];
        let descs = Self::descriptors(ads, &mut storage)?;
        let mut siv = [0u8; 16];
        // SAFETY: `self.ctx` is the key context `vg_aes_siv_init` wrote for
        // `self.rounds` (10, 12 or 14) rounds (every implementation writes
        // the same one), valid for reads of 512 bytes. `descs` points to
        // `storage`, whose first `ads.len()` entries (`16 * ads.len()`
        // bytes, all the function reads) `descriptors` initialized to list
        // the components of `ads`, each valid for reads of its length in
        // bytes. `data` is valid for reads and writes of `data.len()` bytes
        // and `siv` for reads and writes of 16. `data` and `siv` are unique
        // borrows, so they overlap neither each other nor `self.ctx`,
        // `storage` or a component; no buffer overlaps the arguments on the
        // stack or the return address (on x86 and x86-64) or the stack below
        // them that the function uses, and none wraps around the end of the
        // address space.
        unsafe { encrypt(&self.ctx, self.rounds, ads, descs, data, &mut siv) };
        Ok(siv)
    }

    /// `SIV-DECRYPT` (RFC 5297 §2.7): decrypts `data` in place with the
    /// synthetic IV `tag`, and checks that `tag` authenticates the plaintext
    /// and the associated-data components `ads`. If it does not, returns an
    /// error and overwrites `data` with zeros.
    pub fn decrypt_in_place(
        &self,
        ads: &[&[u8]],
        data: &mut [u8],
        tag: &[u8; 16],
    ) -> Result<(), Error> {
        let mut storage = [const { MaybeUninit::uninit() }; Self::MAX_COMPONENTS];
        let descs = Self::descriptors(ads, &mut storage)?;
        // SAFETY: as in `encrypt_in_place`, with the received synthetic IV
        // `tag`, valid for reads of 16 bytes, in place of `siv`: it is a
        // shared borrow, so it does not overlap `data`, a unique one, and
        // only read-only buffers may overlap it.
        let ok = unsafe { decrypt(&self.ctx, self.rounds, ads, descs, data, tag) };
        // `decrypt`'s contract leaves the plaintext in `data` if it returns
        // 1, and zeros otherwise.
        if ok == 1 {
            Ok(())
        } else {
            Err(Error::TagMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AesSiv, Error, InvalidKeyLength};

    /// The `_aes_cbc` (or `_aesni_cbc`) instances run when the components
    /// and the data total more than 32 bytes, and the others otherwise.
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    #[test]
    fn chains_long() {
        use super::chains_long;
        assert!(!chains_long(&[], 0));
        assert!(!chains_long(&[], 32));
        assert!(chains_long(&[], 33));
        assert!(!chains_long(&[&[0; 16], &[0; 8]], 8));
        assert!(chains_long(&[&[0; 16], &[0; 8]], 9));
        assert!(chains_long(&[&[0; 33]], 0));
    }

    #[test]
    fn key_lengths() {
        let key = [0u8; 80];
        for n in [0, 16, 24, 31, 33, 47, 63, 65, 80] {
            assert_eq!(AesSiv::new(&key[..n]).err(), Some(InvalidKeyLength));
        }
    }

    #[test]
    fn too_many_components() {
        let k = AesSiv::new(&[0; 32]).unwrap();
        let ads = [&[][..]; AesSiv::MAX_COMPONENTS + 1];
        let mut data = [1u8; 5];
        assert_eq!(
            k.encrypt_in_place(&ads, &mut data),
            Err(Error::TooManyComponents)
        );
        assert_eq!(
            k.decrypt_in_place(&ads, &mut data, &[0; 16]),
            Err(Error::TooManyComponents)
        );
        // Nothing was touched.
        assert_eq!(data, [1; 5]);
        // The most components allowed round-trip.
        let ads = &ads[..AesSiv::MAX_COMPONENTS];
        let tag = k.encrypt_in_place(ads, &mut data).unwrap();
        k.decrypt_in_place(ads, &mut data, &tag).unwrap();
        assert_eq!(data, [1; 5]);
    }
}
