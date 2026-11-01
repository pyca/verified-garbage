//! ChaCha20 (RFC 8439), with the 16-byte nonce of OpenSSL and
//! pyca/cryptography.
//!
//! The cipher is the verified assembly of the target architecture, on an
//! opaque streaming state that holds the key, the position in the keystream
//! and a partly used block: `vg_chacha20_init` (contract
//! `VG.Spec.ChaCha20.initContract`) starts the keystream of a key and nonce,
//! `vg_chacha20_set_nonce` (`VG.Spec.ChaCha20.setNonceContract`) restarts it
//! for another nonce, and `vg_chacha20_apply`
//! (`VG.Spec.ChaCha20.applyContract`) XORs the next bytes of it into data.
//!
//! The 16-byte nonce is the initial block counter (4 bytes, little-endian)
//! followed by the 12-byte RFC 8439 nonce, i.e. state words 12–15. As in
//! RFC 8439 (and pyca/cryptography), the block counter is word 12 alone, so
//! a keystream starting at block counter `c` is 2³² − `c` blocks long:
//! applying more of it panics, rather than wrapping the counter around or
//! carrying it into word 13, the first word of the nonce, as OpenSSL does
//! (the keystream past that point would be another nonce's, e.g. after
//! 64 bytes from `c = 0xffffffff`). `vg_chacha20_apply` checks this itself,
//! and leaves the data and the keystream unchanged if it fails.
//!
//! The variants of `vg_chacha20_apply`, with the same contract, are chosen
//! by `Backend::select` on CPUs with the features their `_FEATURES`
//! constants name: on x86-64, `vg_chacha20_apply_ifma` (with AVX512_IFMA
//! too), `vg_chacha20_apply_avx512vl`, `vg_chacha20_apply_avx512` and
//! `vg_chacha20_apply_avx2`, in this order; on x86,
//! `vg_chacha20_apply_ssse3`; on AArch64, `vg_chacha20_apply_sve2` (with
//! AdvSIMD), then `vg_chacha20_apply_neon` on CPUs with AdvSIMD.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

#[cfg(target_arch = "x86_64")]
use crate::arch::chacha20::{
    VG_CHACHA20_APPLY_AVX2_FEATURES, VG_CHACHA20_APPLY_AVX512_FEATURES,
    VG_CHACHA20_APPLY_AVX512VL_FEATURES, VG_CHACHA20_APPLY_IFMA_FEATURES, vg_chacha20_apply_avx2,
    vg_chacha20_apply_avx512, vg_chacha20_apply_avx512vl, vg_chacha20_apply_ifma,
};
#[cfg(target_arch = "x86")]
use crate::arch::chacha20::{VG_CHACHA20_APPLY_SSSE3_FEATURES, vg_chacha20_apply_ssse3};
#[cfg(target_arch = "aarch64")]
use crate::arch::chacha20::{
    VG_CHACHA20_APPLY_SVE2_FEATURES, vg_chacha20_apply_neon, vg_chacha20_apply_sve2,
};
use crate::arch::chacha20::{vg_chacha20_apply, vg_chacha20_init, vg_chacha20_set_nonce};
use crate::cpu::detected;
use crate::zeroize::zeroize_raw;
use core::mem::MaybeUninit;
use verified_garbage_cpu::Features;

/// The implementations of `vg_chacha20_apply`, which ChaCha20-Poly1305
/// follows (`crate::chacha20poly1305`): each variant but `Scalar` is the
/// one with its suffix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Scalar,
    /// `_neon`.
    #[cfg(target_arch = "aarch64")]
    Neon,
    /// `_sve2`.
    #[cfg(target_arch = "aarch64")]
    Sve2,
    /// `_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// `_avx512`.
    #[cfg(target_arch = "x86_64")]
    Avx512,
    /// `_avx512vl`, on CPUs without AVX512_IFMA.
    #[cfg(target_arch = "x86_64")]
    Avx512Vl,
    /// `_ifma`, on CPUs with AVX512_IFMA.
    #[cfg(target_arch = "x86_64")]
    Ifma,
    /// `_ssse3`.
    #[cfg(target_arch = "x86")]
    Ssse3,
}

/// AVX512_IFMA, which `VG_CHACHA20_APPLY_IFMA_FEATURES` does not name:
/// `Backend::Ifma` is chosen on the CPUs whose ChaCha20-Poly1305 runs its
/// `_ifma` variants, which need it.
#[cfg(target_arch = "x86_64")]
const IFMA: Features = Features(verified_garbage_cpu::feature::AVX512IFMA);

impl Backend {
    /// AdvSIMD is part of our AArch64 baseline. Tracking it also lets
    /// `VG_CPU_FEATURES=none` exercise the scalar implementation. SVE2 is
    /// not: its variants need `VG_CHACHA20_APPLY_SVE2_FEATURES` (which
    /// ChaCha20-Poly1305's need too, see its tests).
    #[cfg(target_arch = "aarch64")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(const { Features(verified_garbage_cpu::feature::NEON) })
            && f.contains(VG_CHACHA20_APPLY_SVE2_FEATURES)
        {
            Backend::Sve2
        } else if f.contains(const { Features(verified_garbage_cpu::feature::NEON) }) {
            Backend::Neon
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select(f: Features) -> Backend {
        Backend::select_for(
            f,
            Features::all(&[VG_CHACHA20_APPLY_IFMA_FEATURES, IFMA]),
            VG_CHACHA20_APPLY_AVX512VL_FEATURES,
            VG_CHACHA20_APPLY_AVX512_FEATURES,
            VG_CHACHA20_APPLY_AVX2_FEATURES,
        )
    }

    /// The best implementation a CPU with the features `f` can run, for
    /// functions whose variants `_ifma`, `_avx512vl`, `_avx512` and `_avx2`
    /// need the features `ifma`, `avx512vl`, `avx512` and `avx2`
    /// (ChaCha20-Poly1305's need more than `vg_chacha20_apply`'s). `ifma`
    /// comes first, so `_avx512vl` is chosen only on CPUs without
    /// AVX512_IFMA.
    #[cfg(target_arch = "x86_64")]
    pub(crate) fn select_for(
        f: Features,
        ifma: Features,
        avx512vl: Features,
        avx512: Features,
        avx2: Features,
    ) -> Backend {
        if f.contains(ifma) {
            Backend::Ifma
        } else if f.contains(avx512vl) {
            Backend::Avx512Vl
        } else if f.contains(avx512) {
            Backend::Avx512
        } else if f.contains(avx2) {
            Backend::Avx2
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run.
    #[cfg(target_arch = "x86")]
    pub(crate) fn select(f: Features) -> Backend {
        if f.contains(VG_CHACHA20_APPLY_SSSE3_FEATURES) {
            Backend::Ssse3
        } else {
            Backend::Scalar
        }
    }

    /// The best implementation a CPU with the features `f` can run: there
    /// is only one here.
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64", target_arch = "x86")))]
    pub(crate) fn select(_: Features) -> Backend {
        Backend::Scalar
    }
}

/// A ChaCha20 keystream, applied incrementally.
///
/// `new` only stores the key and the nonce: `vg_chacha20_init` runs on the
/// first `apply_keystream`, on the state in place. Were `new` to run it, on
/// a local it then returns, the 776-byte state would be copied to the
/// caller's object: `init` is given the local's address, so the compiler
/// cannot build it in the caller's.
#[repr(C)]
pub struct ChaCha20 {
    /// The streaming state of `vg_chacha20_init` and `vg_chacha20_apply`
    /// (`VG.Spec.ChaCha20.restAt`): the key, the position in the keystream
    /// and the partly used block, then the working space of `apply`. Only
    /// the verified functions read or write it, and they read only bytes
    /// they have written, so it need not be initialized.
    state: MaybeUninit<[u64; 96]>,
    /// The key and the nonce of `new` (and `reset_nonce`), which `init`
    /// reads while `pending`.
    key: [u8; 32],
    nonce: [u8; 16],
    /// Whether `init` has yet to run: `state` holds nothing.
    pending: bool,
    backend: Backend,
}

impl Drop for ChaCha20 {
    /// Wipes the whole object: the state, which holds the key and keystream
    /// (all of it, as the contract lets the functions write any of it), and
    /// the key.
    fn drop(&mut self) {
        // SAFETY: `self` is valid for writes of its size; it is a distinct
        // object, so it does not overlap the callee's stack frame or wrap
        // around the end of the address space. It is not used after the
        // drop, so its fields need not stay valid.
        unsafe { zeroize_raw((self as *mut Self).cast::<u8>(), size_of::<Self>()) };
    }
}

impl ChaCha20 {
    /// The size of a key, in bytes.
    pub const KEY_SIZE: usize = 32;
    /// The size of a nonce (initial block counter and RFC 8439 nonce), in bytes.
    pub const NONCE_SIZE: usize = 16;

    /// Starts the keystream for `key` and `nonce` (the initial block counter,
    /// little-endian, followed by the 12-byte RFC 8439 nonce).
    pub fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        ChaCha20 {
            state: MaybeUninit::uninit(),
            key: *key,
            nonce: *nonce,
            pending: true,
            backend: Backend::select(detected()),
        }
    }

    /// Runs `vg_chacha20_init` on the key and nonce stored.
    fn start(&mut self) {
        // SAFETY: `state` is valid for writes of 768 bytes (`init` reads none
        // of them), `key` for reads of 32 bytes and `nonce` for reads of 16
        // bytes; they are distinct fields, so they do not overlap each other
        // or the return address, and do not wrap around the end of the
        // address space.
        unsafe { vg_chacha20_init(self.state.as_mut_ptr(), &self.key, &self.nonce) };
        self.pending = false;
    }

    /// Restarts the keystream, with the same key, for `nonce`.
    pub fn reset_nonce(&mut self, nonce: &[u8; 16]) {
        if self.pending {
            self.nonce = *nonce;
            return;
        }
        // SAFETY: as in `start`, for `state` and `nonce` (`set_nonce` reads
        // no byte of `state` either).
        unsafe { vg_chacha20_set_nonce(self.state.as_mut_ptr(), nonce) };
    }

    /// XORs the next `data.len()` bytes of the keystream into `data`
    /// (encrypting or decrypting it).
    ///
    /// # Panics
    ///
    /// If the keystream is not that long: if the block counter would pass
    /// `0xffffffff`, i.e. if more than 64 × (2³² − `c`) bytes in all would
    /// have been applied since the nonce (with initial block counter `c`) was
    /// set. `data` is then left unchanged.
    pub fn apply_keystream(&mut self, data: &mut [u8]) {
        if self.pending {
            self.start();
        }
        let f = match self.backend {
            Backend::Scalar => vg_chacha20_apply,
            #[cfg(target_arch = "aarch64")]
            Backend::Neon => vg_chacha20_apply_neon,
            #[cfg(target_arch = "aarch64")]
            Backend::Sve2 => vg_chacha20_apply_sve2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx2 => vg_chacha20_apply_avx2,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512 => vg_chacha20_apply_avx512,
            #[cfg(target_arch = "x86_64")]
            Backend::Avx512Vl => vg_chacha20_apply_avx512vl,
            #[cfg(target_arch = "x86_64")]
            Backend::Ifma => vg_chacha20_apply_ifma,
            #[cfg(target_arch = "x86")]
            Backend::Ssse3 => vg_chacha20_apply_ssse3,
        };
        // SAFETY: `state` is valid for reads and writes of 768 bytes (the
        // bytes `apply` reads before writing them are those `init` and
        // `set_nonce` wrote) and `data` for reads and writes of `data.len()`
        // bytes; they are
        // distinct objects, so they do not overlap each other, the stack
        // frame of the call (the return address) or the stack below it, and
        // do not wrap around the end of the address space. The CPU has the
        // features of the implementation selected.
        let ok = unsafe { f(self.state.as_mut_ptr(), data.as_mut_ptr(), data.len()) };
        assert!(ok == 1, "ChaCha20 block counter would overflow");
    }
}

#[cfg(test)]
mod tests {
    use super::{Backend, ChaCha20};
    use crate::cpu::detected;

    fn unhex<const N: usize>(s: &str) -> [u8; N] {
        let mut out = [0u8; N];
        for (i, o) in out.iter_mut().enumerate() {
            *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    /// A fixed key, `00:01:…:1f`.
    fn key() -> [u8; 32] {
        core::array::from_fn(|i| i as u8)
    }

    /// A 16-byte nonce from an RFC 8439 block counter and nonce.
    fn nonce(counter: u32, nonce: &[u8; 12]) -> [u8; 16] {
        let mut n = [0u8; 16];
        n[..4].copy_from_slice(&counter.to_le_bytes());
        n[4..].copy_from_slice(nonce);
        n
    }

    /// The first `N` bytes of keystream.
    fn keystream<const N: usize>(key: &[u8; 32], nonce: &[u8; 16]) -> [u8; N] {
        let mut out = [0u8; N];
        ChaCha20::new(key, nonce).apply_keystream(&mut out);
        out
    }

    /// Applying the keystream in two pieces, or a byte at a time, is the
    /// same as applying it at once, for every split around block boundaries.
    #[test]
    fn incremental() {
        let n = nonce(7, &[3; 12]);
        let expected = keystream::<200>(&key(), &n);
        for split in 0..=200 {
            let mut data = [0u8; 200];
            let mut c = ChaCha20::new(&key(), &n);
            c.apply_keystream(&mut data[..split]);
            c.apply_keystream(&mut data[split..]);
            assert_eq!(data, expected);
        }
        let mut data = [0u8; 200];
        let mut c = ChaCha20::new(&key(), &n);
        for byte in data.chunks_mut(1) {
            c.apply_keystream(byte);
        }
        assert_eq!(data, expected);
    }

    /// `reset_nonce` restarts the keystream.
    #[test]
    fn reset_nonce() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// `reset_nonce` before any keystream is applied replaces the nonce of
    /// `new`.
    #[test]
    fn reset_nonce_first() {
        let (n1, n2) = (nonce(0, &[1; 12]), nonce(5, &[2; 12]));
        let mut c = ChaCha20::new(&key(), &n1);
        c.reset_nonce(&n2);
        let mut data = [0u8; 100];
        c.apply_keystream(&mut data);
        assert_eq!(data, keystream::<100>(&key(), &n2));
    }

    /// The keystream from block counter 0xffffffff is one block long,
    /// however it is applied, and `reset_nonce` starts a new one.
    #[test]
    fn last_block() {
        let n = nonce(0xffff_ffff, &unhex("0900000011223344aabbccdd"));
        let ks = keystream::<64>(&key(), &n);
        let mut c = ChaCha20::new(&key(), &n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data[..10]);
        c.apply_keystream(&mut data[10..]);
        c.apply_keystream(&mut []);
        assert_eq!(data, ks);
        c.reset_nonce(&n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data);
        assert_eq!(data, ks);
    }

    /// Applies `first` bytes of the keystream from block counter `counter`
    /// and then `then` more, which the tests below make too many.
    fn overflow(counter: u32, first: usize, then: usize) {
        let mut c = ChaCha20::new(&key(), &nonce(counter, &[4; 12]));
        let mut data = [0u8; 192];
        c.apply_keystream(&mut data[..first]);
        c.apply_keystream(&mut data[..then]);
    }

    /// Applying keystream past block counter 0xffffffff panics: in whole
    /// blocks, byte by byte, and after part of the last block.
    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_whole_blocks() {
        overflow(0xffff_fffe, 0, 64 * 3);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_after_blocks() {
        overflow(0xffff_fffe, 64, 64 * 2);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_one_byte() {
        overflow(0xffff_ffff, 64, 1);
    }

    #[test]
    #[should_panic(expected = "ChaCha20 block counter would overflow")]
    fn overflow_partial_block() {
        overflow(0xffff_ffff, 10, 55);
    }

    /// Applying more keystream than is left leaves the data unchanged, and
    /// what is left of the keystream can still be applied.
    #[test]
    fn overflow_unchanged() {
        extern crate std;
        let n = nonce(0xffff_ffff, &[7; 12]);
        let ks = keystream::<64>(&key(), &n);
        let mut c = ChaCha20::new(&key(), &n);
        let mut data = [0u8; 64];
        c.apply_keystream(&mut data[..10]);
        let mut more = [0x5au8; 55];
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            c.apply_keystream(&mut more)
        }));
        assert!(r.is_err());
        assert_eq!(more, [0x5a; 55]);
        c.apply_keystream(&mut data[10..]);
        assert_eq!(data, ks);
    }

    /// The implementation chosen gives the same keystream as the baseline
    /// one, for 35 blocks in one call and split every 61 bytes, and up to the
    /// last block counter.
    #[test]
    fn implementations_agree() {
        const LEN: usize = 16 * 64 * 2 + 64 * 3;
        for counter in [0, 0u32.wrapping_sub((LEN / 64) as u32)] {
            let n = nonce(counter, &[5; 12]);
            let mut expected = [0u8; LEN];
            let mut scalar = ChaCha20::new(&key(), &n);
            scalar.backend = Backend::Scalar;
            scalar.apply_keystream(&mut expected);
            let mut once = [0u8; LEN];
            ChaCha20::new(&key(), &n).apply_keystream(&mut once);
            assert_eq!(once, expected);
            for split in (0..=LEN).step_by(61) {
                let mut data = [0u8; LEN];
                let mut c = ChaCha20::new(&key(), &n);
                c.apply_keystream(&mut data[..split]);
                c.apply_keystream(&mut data[split..]);
                assert_eq!(data, expected);
            }
        }
    }

    /// The implementation chosen gives the same keystream as the baseline
    /// one on unaligned slices, leaving the bytes around them unchanged, for
    /// lengths within a byte of multiples of a block, from three blocks to
    /// sixteen, and up to the last block counter.
    #[test]
    fn bulk_boundaries() {
        for len in [
            191, 192, 193, 255, 256, 257, 319, 320, 321, 383, 384, 385, 447, 448, 449, 511, 512,
            513, 575, 576, 577, 767, 768, 769, 1023, 1024,
        ] {
            for offset in [0, 1, 7, 15] {
                for counter in [7, u32::MAX - (len as u32).div_ceil(64) + 1] {
                    let n = nonce(counter, &[6; 12]);
                    let msg: [u8; 1040] = core::array::from_fn(|i| (i * 29) as u8);
                    let mut expected = msg;
                    let mut scalar = ChaCha20::new(&key(), &n);
                    scalar.backend = Backend::Scalar;
                    scalar.apply_keystream(&mut expected[offset..offset + len]);
                    let mut actual = msg;
                    ChaCha20::new(&key(), &n).apply_keystream(&mut actual[offset..offset + len]);
                    assert_eq!(actual, expected);
                    // Starting with a partial block gives the same keystream,
                    // up to the same final counter.
                    let mut fragmented = msg;
                    let mut c = ChaCha20::new(&key(), &n);
                    c.apply_keystream(&mut fragmented[offset..offset + 1]);
                    c.apply_keystream(&mut fragmented[offset + 1..offset + len]);
                    assert_eq!(fragmented, expected);
                }
            }
        }
    }

    /// The implementation chosen for each set of features.
    #[test]
    fn select() {
        let best = ChaCha20::new(&key(), &nonce(0, &[0; 12])).backend;
        assert_eq!(best, Backend::select(detected()));
        #[cfg(target_arch = "aarch64")]
        {
            use verified_garbage_cpu::Features;
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::NEON)),
                Backend::Neon
            );
            assert_eq!(
                Backend::select(Features(
                    verified_garbage_cpu::feature::NEON | verified_garbage_cpu::feature::SVE2
                )),
                Backend::Sve2
            );
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::SVE2)),
                Backend::Scalar
            );
            assert_eq!(Backend::select(Features(0)), Backend::Scalar);
        }
        #[cfg(target_arch = "x86_64")]
        {
            use crate::arch::chacha20::{
                VG_CHACHA20_APPLY_AVX2_FEATURES, VG_CHACHA20_APPLY_AVX512_FEATURES,
                VG_CHACHA20_APPLY_AVX512VL_FEATURES, VG_CHACHA20_APPLY_IFMA_FEATURES,
            };
            use verified_garbage_cpu::Features;
            let avx2 = VG_CHACHA20_APPLY_AVX2_FEATURES;
            let avx512 = VG_CHACHA20_APPLY_AVX512_FEATURES;
            let avx512vl = VG_CHACHA20_APPLY_AVX512VL_FEATURES;
            assert_eq!(Backend::select(avx2), Backend::Avx2);
            assert_eq!(Backend::select(avx512), Backend::Avx512);
            assert_eq!(Backend::select(avx512vl), Backend::Avx512Vl);
            assert_eq!(VG_CHACHA20_APPLY_IFMA_FEATURES, avx512);
            assert_eq!(
                Backend::select(Features::all(&[avx512, super::IFMA])),
                Backend::Ifma
            );
            assert_eq!(
                Backend::select(Features::all(&[avx512vl, super::IFMA])),
                Backend::Ifma
            );
            assert_eq!(
                Backend::select(Features::all(&[
                    VG_CHACHA20_APPLY_AVX2_FEATURES,
                    VG_CHACHA20_APPLY_AVX512_FEATURES
                ])),
                Backend::Avx512
            );
            assert_eq!(
                Backend::select(Features(verified_garbage_cpu::feature::AVX)),
                Backend::Scalar
            );
        }
        #[cfg(target_arch = "x86")]
        {
            use crate::arch::chacha20::VG_CHACHA20_APPLY_SSSE3_FEATURES;
            use verified_garbage_cpu::Features;
            assert_eq!(
                Backend::select(VG_CHACHA20_APPLY_SSSE3_FEATURES),
                Backend::Ssse3
            );
            assert_eq!(Backend::select(Features(0)), Backend::Scalar);
        }
    }
}
