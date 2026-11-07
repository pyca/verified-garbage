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

/// A 16-byte block.
type Block = [u8; 16];

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
        // address space. The dispatcher calls only an implementation the
        // CPU has the features of.
        unsafe {
            vg_aes_siv_encrypt_auto(
                &self.ctx,
                self.rounds,
                descs,
                ads.len(),
                data.as_mut_ptr(),
                data.len(),
                &mut siv,
            )
        };
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
        let ok = unsafe {
            vg_aes_siv_decrypt_auto(
                &self.ctx,
                self.rounds,
                descs,
                ads.len(),
                data.as_mut_ptr(),
                data.len(),
                tag,
            )
        };
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
