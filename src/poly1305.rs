//! Poly1305 (RFC 8439 §2.5), a one-time authenticator.
//!
//! Its whole computation is verified assembly: `vg_poly1305_init`,
//! `vg_poly1305_update` and `vg_poly1305_finalize` (contracts
//! `VG.Spec.Poly1305.initContract`, `updateContract` and `finalizeContract`)
//! maintain a streaming state that represents the key and the message
//! absorbed so far, with the message's last bytes that do not fill a block
//! buffered in it (`VG.Spec.Poly1305.Buffered`), and compute the tag. This
//! module only keeps that state together with the message length (modulo
//! 2⁶⁴), which the contracts take as an argument.
//!
//! The variants of `vg_poly1305_update`, with the same contract, are chosen
//! by `Backend::select`: on x86-64, on CPUs with the features their
//! `_FEATURES` constants name, `vg_poly1305_update_ifma`,
//! `vg_poly1305_update_avx512` and `vg_poly1305_update_avx2`, in this order.
//! On AArch64, `vg_poly1305_update_neon` needs only AdvSIMD, which every
//! AArch64 CPU has; it is chosen only on Apple's cores (`target_vendor =
//! "apple"`), because on others, such as Arm's Neoverse N2, the baseline
//! implementation is faster.
//!
//! A key must be used to authenticate only one message: the tags of two
//! messages under the same key reveal enough to forge others.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "aarch64")]
use crate::arch::poly1305::vg_poly1305_update_neon;
#[cfg(target_arch = "x86_64")]
use crate::arch::poly1305::{
    VG_POLY1305_UPDATE_AVX2_FEATURES, VG_POLY1305_UPDATE_AVX512_FEATURES,
    VG_POLY1305_UPDATE_IFMA_FEATURES, vg_poly1305_update_avx2, vg_poly1305_update_avx512,
    vg_poly1305_update_ifma,
};
use crate::arch::poly1305::{vg_poly1305_finalize, vg_poly1305_init, vg_poly1305_update};
use crate::cpu::detected;
use crate::zeroize::zeroize;
use verified_garbage_cpu::Features;

pub use crate::hmac::InvalidMac;

/// The implementations of `vg_poly1305_update`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Backend {
    /// The baseline ISA.
    Scalar,
    /// `vg_poly1305_update_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// `vg_poly1305_update_avx512`.
    #[cfg(target_arch = "x86_64")]
    Avx512,
    /// `vg_poly1305_update_ifma`.
    #[cfg(target_arch = "x86_64")]
    Ifma,
    /// `vg_poly1305_update_neon`.
    #[cfg(target_arch = "aarch64")]
    Neon,
}

impl Backend {
    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    fn select(f: Features) -> Backend {
        if f.contains(VG_POLY1305_UPDATE_IFMA_FEATURES) {
            Backend::Ifma
        } else if f.contains(VG_POLY1305_UPDATE_AVX512_FEATURES) {
            Backend::Avx512
        } else if f.contains(VG_POLY1305_UPDATE_AVX2_FEATURES) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: NEON on
    /// Apple's cores.
    #[cfg(target_arch = "aarch64")]
    fn select(f: Features) -> Backend {
        Backend::select_for(f, cfg!(target_vendor = "apple"))
    }

    /// The best implementation a CPU with the features `f` can run, on
    /// Apple's cores if `apple`: no CPU feature tells which run
    /// `vg_poly1305_update_neon` faster than the baseline implementation
    /// (Apple's, about twice as fast) or slower (Arm's Neoverse N2).
    #[cfg(target_arch = "aarch64")]
    fn select_for(f: Features, apple: bool) -> Backend {
        if apple && f.contains(const { Features(verified_garbage_cpu::feature::NEON) }) {
            Backend::Neon
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// An incremental Poly1305 computation.
pub struct Poly1305 {
    /// The streaming state, representing the key and the message so far.
    state: [u64; 16],
    /// The message length so far, in bytes, modulo 2⁶⁴.
    count: u64,
    /// The implementation of `vg_poly1305_update` to call.
    backend: Backend,
}

impl Drop for Poly1305 {
    /// Wipes the state, which holds the key.
    fn drop(&mut self) {
        zeroize(&mut self.state);
    }
}

impl Poly1305 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a tag, in bytes.
    pub const TAG_SIZE: usize = 16;

    /// Starts a computation with the one-time key `key`.
    pub fn new(key: &[u8; 32]) -> Self {
        let mut state = [0; 16];
        // SAFETY: `state` is valid for writes of 128 bytes and `key` for
        // reads of 32 bytes; they are distinct objects, so they do not overlap
        // each other or anything on the stack (the return address and any
        // arguments), and do not wrap around the end of the address space.
        unsafe { vg_poly1305_init(&mut state, key) };
        Poly1305 {
            state,
            count: 0,
            backend: Backend::select(detected()),
        }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        let update = match self.backend {
            Backend::Scalar => vg_poly1305_update,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_poly1305_update_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_poly1305_update_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_poly1305_update_ifma,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_poly1305_update_neon,
        };
        // SAFETY: `self.state` is valid for reads and writes of 128 bytes and
        // `data` for reads of `data.len()` bytes; they are distinct objects,
        // so they do not overlap each other or anything on the stack (the
        // return address, any arguments, and the stack below the stack
        // pointer the calls use), and do not wrap around the end of the
        // address space. `self.state` represents a message of `self.count`
        // bytes, modulo 2⁶⁴. The CPU has the features of the implementation
        // selected (`Backend::select`).
        unsafe { update(&mut self.state, self.count, data.as_ptr(), data.len()) };
        self.count = self.count.wrapping_add(data.len() as u64);
    }

    /// Returns the tag of everything absorbed.
    pub fn finalize(mut self) -> [u8; 16] {
        let mut tag = [0; 16];
        // SAFETY: `self.state` is valid for reads and writes of 128 bytes and
        // `tag` for writes of 16 bytes; they are distinct objects, so they do
        // not overlap each other or anything on the stack (the return address
        // and any arguments), and do not wrap around the end of the address
        // space. `self.state` represents a message of `self.count` bytes,
        // modulo 2⁶⁴.
        unsafe { vg_poly1305_finalize(&mut self.state, self.count, &mut tag) };
        tag
    }

    /// Checks that `tag` is the tag of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `tag`
    /// differs from it (its length is public). `tag` must be the whole tag,
    /// of [`Self::TAG_SIZE`] bytes; a truncated one is rejected.
    pub fn verify(self, tag: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(&self.finalize(), tag) {
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
    use super::*;

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

    /// The implementation chosen, and on AArch64 the NEON one whichever is
    /// chosen, give the same tag as the baseline one, for lengths up to 1100
    /// bytes, many within a byte of a multiple of a block, in one piece and
    /// in two split at many positions.
    #[test]
    fn implementations_agree() {
        let key: [u8; 32] = core::array::from_fn(|i| (i * 11 + 1) as u8);
        let msg: [u8; 1100] = core::array::from_fn(|i| (i * 31 + 7) as u8);
        #[allow(unused_mut)]
        let mut backends = [Backend::select(detected()); 2];
        #[cfg(target_arch = "aarch64")]
        {
            backends[1] = Backend::Neon;
        }
        for len in [
            0, 1, 15, 16, 17, 63, 64, 65, 127, 128, 129, 191, 192, 193, 255, 256, 257, 271, 272,
            273, 319, 320, 321, 447, 448, 449, 495, 496, 511, 512, 513, 527, 528, 529, 623, 624,
            625, 639, 640, 641, 1024, 1100,
        ] {
            let mut scalar = Poly1305::new(&key);
            scalar.backend = Backend::Scalar;
            scalar.update(&msg[..len]);
            let expected = scalar.finalize();
            assert_eq!(Poly1305::mac(&key, &msg[..len]), expected);
            for backend in backends {
                for split in (0..=len).step_by(13) {
                    let mut p = Poly1305::new(&key);
                    p.backend = backend;
                    p.update(&msg[..split]);
                    p.update(&msg[split..len]);
                    assert_eq!(p.finalize(), expected);
                }
            }
        }
    }

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        assert_eq!(Poly1305::new(&[0; 32]).backend, Backend::select(detected()));
        #[cfg(target_arch = "x86_64")]
        {
            let avx2 = VG_POLY1305_UPDATE_AVX2_FEATURES;
            let avx512 = VG_POLY1305_UPDATE_AVX512_FEATURES;
            let ifma = VG_POLY1305_UPDATE_IFMA_FEATURES;
            assert_eq!(Backend::select(ifma), Backend::Ifma);
            assert_eq!(Backend::select(avx512), Backend::Avx512);
            assert_eq!(Backend::select(avx2), Backend::Avx2);
            // AVX-512F alone is not enough:
            // `VG_POLY1305_UPDATE_AVX512_FEATURES` names more.
            assert_eq!(
                Backend::select(Features(
                    verified_garbage_cpu::feature::AVX | verified_garbage_cpu::feature::AVX512F
                )),
                Backend::Scalar
            );
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::AVX)),
                Backend::Scalar
            );
        }
        #[cfg(target_arch = "aarch64")]
        {
            let neon = Features(verified_garbage_cpu::feature::NEON);
            assert_eq!(Backend::select_for(neon, true), Backend::Neon);
            assert_eq!(Backend::select_for(neon, false), Backend::Scalar);
            assert_eq!(Backend::select_for(Features(0), true), Backend::Scalar);
            assert_eq!(Backend::select_for(Features(0), false), Backend::Scalar);
        }
    }
}
