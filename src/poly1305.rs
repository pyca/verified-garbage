//! Poly1305 (RFC 8439 §2.5), a one-time authenticator.
//!
//! A key must authenticate only one message: the tags of two messages under the
//! same key reveal enough to forge others.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::poly1305::vg_poly1305_update_auto;
use crate::arch::dispatch::poly1305::{vg_poly1305_finalize_auto, vg_poly1305_init_auto};
use crate::zeroize::zeroize;

use crate::error::InvalidMac;

/// An incremental Poly1305 computation.
pub struct Poly1305 {
    /// The streaming state, representing the key and the message so far.
    state: CacheAligned<[u64; 16]>,
    /// The message length so far, in bytes, modulo 2⁶⁴.
    count: u64,
}

impl Drop for Poly1305 {
    /// Wipes the state, which holds the key.
    fn drop(&mut self) {
        zeroize(&mut self.state.0);
    }
}

impl Poly1305 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Starts a computation with the one-time key `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        crate::dit::enter!(dit);
        let mut state = CacheAligned([0; 16]);
        // SAFETY: `state` is valid for writes of 128 bytes and `key` for
        // reads of 32 bytes; they are distinct objects, so they do not overlap
        // each other or anything on the stack (the return address and any
        // arguments), and do not wrap around the end of the address space.
        unsafe { vg_poly1305_init_auto(dit, &mut state.0, key) };
        Poly1305 { state, count: 0 }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        crate::dit::enter!(dit);
        // SAFETY: `self.state` is valid for reads and writes of 128 bytes and
        // `data` for reads of `data.len()` bytes; they are distinct objects,
        // so they do not overlap each other or anything on the stack (the
        // return address, any arguments, and the stack below the stack
        // pointer the calls use), and do not wrap around the end of the
        // address space. `self.state` represents a message of `self.count`
        // bytes, modulo 2⁶⁴. The dispatcher calls only an implementation the
        // CPU has the features of.
        unsafe {
            vg_poly1305_update_auto(
                dit,
                &mut self.state.0,
                self.count,
                data.as_ptr(),
                data.len(),
            )
        };
        self.count = self.count.wrapping_add(data.len() as u64);
    }

    /// Returns the tag of everything absorbed.
    pub fn finalize(self) -> [u8; 16] {
        crate::dit::enter!(dit);
        self.finalize_with(dit)
    }

    /// [`finalize`](Self::finalize), with the token of the operation it is
    /// part of (see `crate::dit`).
    fn finalize_with(mut self, dit: crate::dit::Dit<'_>) -> [u8; 16] {
        let mut tag = [0; 16];
        // SAFETY: `self.state` is valid for reads and writes of 128 bytes and
        // `tag` for writes of 16 bytes; they are distinct objects, so they do
        // not overlap each other or anything on the stack (the return address
        // and any arguments), and do not wrap around the end of the address
        // space. `self.state` represents a message of `self.count` bytes,
        // modulo 2⁶⁴.
        unsafe { vg_poly1305_finalize_auto(dit, &mut self.state.0, self.count, &mut tag) };
        tag
    }

    /// Checks that `tag` is the tag of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `tag`
    /// differs from it (its length is public). `tag` must be the whole tag,
    /// of [`Self::TAG_SIZE`] bytes; a truncated one is rejected.
    pub fn verify(self, tag: &[u8]) -> Result<(), InvalidMac> {
        crate::dit::enter!(dit);
        if crate::ct::eq(dit, &self.finalize_with(dit), tag) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The tag of `data` with the one-time key `key`.
    pub fn mac(key: &[u8; 32], data: &[u8]) -> [u8; 16] {
        let mut p = Self::new(key);
        p.update(data);
        p.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::{InvalidMac, Poly1305};

    /// Every message, absorbed in two pieces split at every position, and
    /// with the second piece a byte at a time, has the tag of the whole.
    #[test]
    fn incremental() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 13 + 5) as u8);
        let msg: [u8; 70] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Poly1305::mac(&key, &msg[..len]);
            for split in 0..=len {
                let mut p = Poly1305::new(&key);
                p.update(&msg[..split]);
                p.update(&msg[split..len]);
                assert_eq!(p.finalize(), expected);
                let mut p = Poly1305::new(&key);
                p.update(&msg[..split]);
                for byte in &msg[split..len] {
                    p.update(core::slice::from_ref(byte));
                }
                assert_eq!(p.finalize(), expected);
            }
        }
    }

    /// `verify` accepts the tag and rejects any other: one with a bit
    /// flipped in its first, a middle or its last byte, a truncated tag and
    /// a longer one.
    #[test]
    fn verify() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 13 + 5) as u8);
        let data = b"Cryptographic Forum Research Group";
        let tag = Poly1305::mac(&key, data);
        let check = |t: &[u8]| {
            let mut p = Poly1305::new(&key);
            p.update(data);
            p.verify(t)
        };
        assert_eq!(check(&tag), Ok(()));
        for i in [0, 7, 15] {
            let mut bad = tag;
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(InvalidMac));
        }
        assert_eq!(check(&tag[..15]), Err(InvalidMac));
        assert_eq!(check(&[]), Err(InvalidMac));
        let mut longer = [0u8; 17];
        longer[..16].copy_from_slice(&tag);
        assert_eq!(check(&longer), Err(InvalidMac));
    }
}
