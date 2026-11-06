//! SHA3-224, SHA3-256, SHA3-384 and SHA3-512, and the extendable-output
//! functions SHAKE128 and SHAKE256 (FIPS 202).
//!
//! Each function has verified functions of its own, whose code has its rate
//! and domain-separation suffix and whose contracts name the function of
//! FIPS 202 they compute (`VG.Spec.Sha3`): `update` absorbs a piece of the
//! message, and `finalize` writes the digest (SHA-3) or pads the message for
//! `squeeze` to output it in pieces (SHAKE). This module keeps the state, the
//! position in the block that each call returns for the next, and the
//! implementation chosen.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::sha3::{
    vg_sha3_224_finalize, vg_sha3_224_update, vg_sha3_256_finalize, vg_sha3_256_update,
    vg_sha3_384_finalize, vg_sha3_384_update, vg_sha3_512_finalize, vg_sha3_512_update,
    vg_shake128_finalize, vg_shake128_squeeze, vg_shake128_update, vg_shake256_finalize,
    vg_shake256_squeeze, vg_shake256_update,
};
use core::mem::MaybeUninit;

#[cfg(target_arch = "aarch64")]
use crate::arch::sha3::{
    VG_SHA3_224_FINALIZE_SHA3_FEATURES, VG_SHA3_224_UPDATE_SHA3_FEATURES,
    VG_SHA3_256_FINALIZE_SHA3_FEATURES, VG_SHA3_256_UPDATE_SHA3_FEATURES,
    VG_SHA3_384_FINALIZE_SHA3_FEATURES, VG_SHA3_384_UPDATE_SHA3_FEATURES,
    VG_SHA3_512_FINALIZE_SHA3_FEATURES, VG_SHA3_512_UPDATE_SHA3_FEATURES,
    VG_SHAKE128_FINALIZE_SHA3_FEATURES, VG_SHAKE128_SQUEEZE_SHA3_FEATURES,
    VG_SHAKE128_UPDATE_SHA3_FEATURES, VG_SHAKE256_FINALIZE_SHA3_FEATURES,
    VG_SHAKE256_SQUEEZE_SHA3_FEATURES, VG_SHAKE256_UPDATE_SHA3_FEATURES, vg_sha3_224_finalize_sha3,
    vg_sha3_224_update_sha3, vg_sha3_256_finalize_sha3, vg_sha3_256_update_sha3,
    vg_sha3_384_finalize_sha3, vg_sha3_384_update_sha3, vg_sha3_512_finalize_sha3,
    vg_sha3_512_update_sha3, vg_shake128_finalize_sha3, vg_shake128_squeeze_sha3,
    vg_shake128_update_sha3, vg_shake256_finalize_sha3, vg_shake256_squeeze_sha3,
    vg_shake256_update_sha3,
};

/// The working space of the `update` functions, aligned to a cache line.
#[repr(C, align(128))]
struct Scratch(MaybeUninit<[u64; 80]>);

/// The implementations of the functions, the same for every function and
/// every phase of a computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Scalar,
    /// `_sha3`.
    #[cfg(target_arch = "aarch64")]
    Sha3,
}

impl Backend {
    pub(crate) fn detected() -> Self {
        // The `_sha3` variants are faster on Apple's cores and slower on
        // Neoverse N2; explicit feature requests retain access to them for
        // testing.
        #[cfg(all(target_arch = "aarch64", feature = "cpu-features-env"))]
        {
            static BACKEND: std::sync::OnceLock<Backend> = std::sync::OnceLock::new();
            *BACKEND.get_or_init(|| {
                let requested = std::env::var("VG_CPU_FEATURES")
                    .unwrap_or_default()
                    .split(',')
                    .any(|name| name == "sha3");
                Self::select(
                    crate::cpu::detected(),
                    cfg!(target_vendor = "apple"),
                    requested,
                )
            })
        }
        #[cfg(all(target_arch = "aarch64", not(feature = "cpu-features-env")))]
        {
            if cfg!(target_vendor = "apple") {
                Self::select(crate::cpu::detected(), true, false)
            } else {
                Self::Scalar
            }
        }
        #[cfg(not(target_arch = "aarch64"))]
        Self::Scalar
    }

    #[cfg(target_arch = "aarch64")]
    fn select(features: verified_garbage_cpu::Features, apple: bool, requested: bool) -> Self {
        if (apple || requested)
            && features.contains(
                const {
                    verified_garbage_cpu::Features::all(&[
                        VG_SHA3_224_UPDATE_SHA3_FEATURES,
                        VG_SHA3_224_FINALIZE_SHA3_FEATURES,
                        VG_SHA3_256_UPDATE_SHA3_FEATURES,
                        VG_SHA3_256_FINALIZE_SHA3_FEATURES,
                        VG_SHA3_384_UPDATE_SHA3_FEATURES,
                        VG_SHA3_384_FINALIZE_SHA3_FEATURES,
                        VG_SHA3_512_UPDATE_SHA3_FEATURES,
                        VG_SHA3_512_FINALIZE_SHA3_FEATURES,
                        VG_SHAKE128_UPDATE_SHA3_FEATURES,
                        VG_SHAKE128_FINALIZE_SHA3_FEATURES,
                        VG_SHAKE128_SQUEEZE_SHA3_FEATURES,
                        VG_SHAKE256_UPDATE_SHA3_FEATURES,
                        VG_SHAKE256_FINALIZE_SHA3_FEATURES,
                        VG_SHAKE256_SQUEEZE_SHA3_FEATURES,
                    ])
                },
            )
        {
            Self::Sha3
        } else {
            Self::Scalar
        }
    }
}

/// The state of a computation absorbing a message: `state` represents the
/// message so far for the function's rate, and `pos` is the position its
/// `update` returned (the message's length modulo the rate, less than it).
#[derive(Clone)]
struct Absorbing {
    state: [u64; 25],
    pos: usize,
    backend: Option<Backend>,
}

impl Absorbing {
    /// The empty message: the all-zero state, at position 0.
    const fn new() -> Self {
        Absorbing {
            state: [0; 25],
            pos: 0,
            backend: None,
        }
    }

    /// Select lazily so the public constructors remain `const`.
    fn backend(&mut self) -> Backend {
        *self.backend.get_or_insert_with(Backend::detected)
    }
}

impl Drop for Absorbing {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state);
    }
}

/// The state of an extendable-output function's output: squeezed from
/// `pos`, the position its `finalize` or `squeeze` left (at most the rate),
/// `state` gives the rest of the output.
#[derive(Clone)]
struct Squeezing {
    state: [u64; 25],
    pos: usize,
    backend: Backend,
}

impl Drop for Squeezing {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state);
    }
}

/// `update`, through the implementation `backend`: absorbs `data` into
/// `$s` (an `Absorbing`), with the token `$dit`, with the function's `update` or its `_sha3`
/// variant.
macro_rules! absorb {
    ($dit:expr, $s:expr, $data:expr, $update:ident, $update_sha3:ident) => {{
        let dit: crate::dit::Dit<'_> = $dit;
        let s: &mut Absorbing = $s;
        let data: &[u8] = $data;
        let backend = s.backend();
        // Uninitialized: the contract holds whatever the scratch holds, so
        // filling it first would only cost time.
        let mut scratch = Scratch(MaybeUninit::uninit());
        // SAFETY: `s.pos` is the position the function's `update` returned
        // for the message `s.state` represents (0 for the all-zero state, the
        // empty message), so it is less than the function's rate.
        // `s.state` is valid for reads and writes of 200 bytes, `data` for
        // reads of `data.len()` bytes and `scratch` for reads and writes of
        // 640 bytes (the state and `scratch`, arrays of `u64`, are aligned
        // for it); they are distinct objects, so they do not overlap each
        // other or the stack below the stack pointer. Backend selection
        // checked every CPU feature the hardware variant requires.
        s.pos = unsafe {
            match backend {
                Backend::Scalar => $update(
                    dit,
                    &mut s.state,
                    s.pos,
                    data.as_ptr(),
                    data.len(),
                    scratch.0.as_mut_ptr(),
                ),
                #[cfg(target_arch = "aarch64")]
                Backend::Sha3 => $update_sha3(
                    dit,
                    &mut s.state,
                    s.pos,
                    data.as_ptr(),
                    data.len(),
                    scratch.0.as_mut_ptr(),
                ),
            }
        };
    }};
}

/// Defines a SHA-3 hash function with a rate of `$rate` bytes,
/// `$output`-byte digests, and the verified functions `$update` and
/// `$finalize` (and their `_sha3` variants).
macro_rules! sha3 {
    ($(#[$doc:meta])* $name:ident {
        rate: $rate:literal,
        output: $output:literal,
        update: ($update:ident, $update_sha3:ident),
        finalize: ($finalize:ident, $finalize_sha3:ident) $(,)?
    }) => {
        $(#[$doc])*
        #[derive(Clone)]
        pub struct $name(Absorbing);

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $output;
            /// The rate of the sponge, in bytes (the block size of HMAC).
            pub const BLOCK_SIZE: usize = $rate;

            /// Starts a new computation.
            pub const fn new() -> Self {
                $name(Absorbing::new())
            }

            /// Absorbs `data`.
            pub fn update(&mut self, data: &[u8]) {
                self.update_with(crate::dit::public(crate::dit::Why::UnkeyedHash), data);
            }

            /// [`update`](Self::update), with the token of the operation it
            /// is part of (see `crate::dit`).
            pub(crate) fn update_with(&mut self, dit: crate::dit::Dit<'_>, data: &[u8]) {
                absorb!(dit, &mut self.0, data, $update, $update_sha3);
            }

            /// Pads the message and returns its digest.
            pub fn finalize(self) -> [u8; $output] {
                self.finalize_with(crate::dit::public(crate::dit::Why::UnkeyedHash))
            }

            /// [`finalize`](Self::finalize), with the token of the operation
            /// it is part of (see `crate::dit`).
            pub(crate) fn finalize_with(mut self, dit: crate::dit::Dit<'_>) -> [u8; $output] {
                let backend = self.0.backend();
                let mut digest = [0; $output];
                // SAFETY: as in `update`, `self.0.pos` is the position
                // `update` returned for the message `self.0.state`
                // represents; `self.0.state` is valid for reads and writes of
                // 200 bytes and `digest` for writes of its size, distinct
                // objects. Backend selection checked every CPU feature the
                // hardware variant requires.
                unsafe {
                    match backend {
                        Backend::Scalar => {
                            $finalize(dit, &mut self.0.state, self.0.pos, &mut digest)
                        }
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => {
                            $finalize_sha3(dit, &mut self.0.state, self.0.pos, &mut digest)
                        }
                    }
                };
                digest
            }

            /// The digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; $output] {
                Self::digest_with(crate::dit::public(crate::dit::Why::UnkeyedHash), data)
            }

            /// [`digest`](Self::digest), with the token of the operation it
            /// is part of (see `crate::dit`).
            #[allow(dead_code)]
            pub(crate) fn digest_with(dit: crate::dit::Dit<'_>, data: &[u8]) -> [u8; $output] {
                let mut h = Self::new();
                h.update_with(dit, data);
                h.finalize_with(dit)
            }
        }

        impl super::HashFunction for $name {
            const OUTPUT_SIZE: usize = $name::OUTPUT_SIZE;
            const BLOCK_SIZE: usize = $name::BLOCK_SIZE;
            type Output = [u8; $output];

            fn new() -> Self {
                $name::new()
            }

            fn update(&mut self, data: &[u8]) {
                $name::update(self, data)
            }

            fn finalize(self) -> [u8; $output] {
                $name::finalize(self)
            }
        }
    };
}

/// Defines a SHAKE extendable-output function with a rate of `$rate` bytes,
/// the reader of its output, and the verified functions `$update`,
/// `$finalize` and `$squeeze` (and their `_sha3` variants).
macro_rules! shake {
    ($(#[$doc:meta])* $name:ident, $(#[$rdoc:meta])* $reader:ident {
        rate: $rate:literal,
        update: ($update:ident, $update_sha3:ident),
        finalize: ($finalize:ident, $finalize_sha3:ident),
        squeeze: ($squeeze:ident, $squeeze_sha3:ident) $(,)?
    }) => {
        $(#[$doc])*
        #[derive(Clone)]
        pub struct $name(Absorbing);

        $(#[$rdoc])*
        #[derive(Clone)]
        pub struct $reader(Squeezing);

        impl $reader {
            /// Writes the next `out.len()` bytes of output to `out`.
            pub fn squeeze(&mut self, out: &mut [u8]) {
                self.squeeze_with(crate::dit::public(crate::dit::Why::UnkeyedHash), out);
            }

            /// [`squeeze`](Self::squeeze), with the token of the operation
            /// it is part of (see `crate::dit`).
            pub(crate) fn squeeze_with(&mut self, dit: crate::dit::Dit<'_>, out: &mut [u8]) {
                let s = &mut self.0;
                // SAFETY: `s.pos` is the position `finalize` (0) or the last
                // `squeeze` left, at most the rate, from which `s.state`
                // continues the output. `s.state` is valid for reads and
                // writes of 200 bytes and `out` for writes of `out.len()`
                // bytes; they are distinct objects, so they do not overlap
                // each other or the stack below the stack pointer. The
                // backend was selected only after checking every required CPU
                // feature.
                s.pos = unsafe {
                    match s.backend {
                        Backend::Scalar => {
                            $squeeze(dit, &mut s.state, s.pos, out.as_mut_ptr(), out.len())
                        }
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => {
                            $squeeze_sha3(dit, &mut s.state, s.pos, out.as_mut_ptr(), out.len())
                        }
                    }
                };
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $name {
            /// The rate of the sponge, in bytes.
            pub const BLOCK_SIZE: usize = $rate;

            /// Starts a new computation.
            pub const fn new() -> Self {
                $name(Absorbing::new())
            }

            /// Absorbs `data`.
            pub fn update(&mut self, data: &[u8]) {
                self.update_with(crate::dit::public(crate::dit::Why::UnkeyedHash), data);
            }

            /// [`update`](Self::update), with the token of the operation it
            /// is part of (see `crate::dit`).
            pub(crate) fn update_with(&mut self, dit: crate::dit::Dit<'_>, data: &[u8]) {
                absorb!(dit, &mut self.0, data, $update, $update_sha3);
            }

            /// Pads the message and returns a reader of its output, which
            /// can be squeezed in pieces.
            pub fn finalize_xof(self) -> $reader {
                self.finalize_xof_with(crate::dit::public(crate::dit::Why::UnkeyedHash))
            }

            /// [`finalize_xof`](Self::finalize_xof), with the token of the
            /// operation it is part of (see `crate::dit`).
            pub(crate) fn finalize_xof_with(mut self, dit: crate::dit::Dit<'_>) -> $reader {
                let backend = self.0.backend();
                let mut state = self.0.state;
                // SAFETY: as in `update`, `self.0.pos` is the position
                // `update` returned for the message `state` represents;
                // `state` is valid for reads and writes of 200 bytes. Backend
                // selection checked every CPU feature the hardware variant
                // requires.
                unsafe {
                    match backend {
                        Backend::Scalar => $finalize(dit, &mut state, self.0.pos),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $finalize_sha3(dit, &mut state, self.0.pos),
                    }
                };
                // From position 0, the padded state gives the output from its
                // first byte on.
                $reader(Squeezing {
                    state,
                    pos: 0,
                    backend,
                })
            }

            /// Pads the message and fills `out` with the first `out.len()`
            /// bytes of output.
            pub fn finalize(self, out: &mut [u8]) {
                self.finalize_with(crate::dit::public(crate::dit::Why::UnkeyedHash), out);
            }

            /// [`finalize`](Self::finalize), with the token of the operation
            /// it is part of (see `crate::dit`).
            #[allow(dead_code)]
            pub(crate) fn finalize_with(self, dit: crate::dit::Dit<'_>, out: &mut [u8]) {
                self.finalize_xof_with(dit).squeeze_with(dit, out);
            }

            /// Fills `out` with the first `out.len()` bytes of output for
            /// `data`.
            pub fn digest(data: &[u8], out: &mut [u8]) {
                Self::digest_with(crate::dit::public(crate::dit::Why::UnkeyedHash), data, out);
            }

            /// [`digest`](Self::digest), with the token of the operation it
            /// is part of (see `crate::dit`).
            #[allow(dead_code)]
            pub(crate) fn digest_with(dit: crate::dit::Dit<'_>, data: &[u8], out: &mut [u8]) {
                let mut h = Self::new();
                h.update_with(dit, data);
                h.finalize_with(dit, out);
            }
        }
    };
}

sha3!(
    /// An incremental SHA3-224 computation.
    Sha3_224 {
        rate: 144,
        output: 28,
        update: (vg_sha3_224_update, vg_sha3_224_update_sha3),
        finalize: (vg_sha3_224_finalize, vg_sha3_224_finalize_sha3),
    }
);
sha3!(
    /// An incremental SHA3-256 computation.
    Sha3_256 {
        rate: 136,
        output: 32,
        update: (vg_sha3_256_update, vg_sha3_256_update_sha3),
        finalize: (vg_sha3_256_finalize, vg_sha3_256_finalize_sha3),
    }
);
sha3!(
    /// An incremental SHA3-384 computation.
    Sha3_384 {
        rate: 104,
        output: 48,
        update: (vg_sha3_384_update, vg_sha3_384_update_sha3),
        finalize: (vg_sha3_384_finalize, vg_sha3_384_finalize_sha3),
    }
);
sha3!(
    /// An incremental SHA3-512 computation.
    Sha3_512 {
        rate: 72,
        output: 64,
        update: (vg_sha3_512_update, vg_sha3_512_update_sha3),
        finalize: (vg_sha3_512_finalize, vg_sha3_512_finalize_sha3),
    }
);
shake!(
    /// An incremental SHAKE128 computation.
    Shake128,
    /// The output of SHAKE128, squeezed in pieces.
    Shake128Reader {
        rate: 168,
        update: (vg_shake128_update, vg_shake128_update_sha3),
        finalize: (vg_shake128_finalize, vg_shake128_finalize_sha3),
        squeeze: (vg_shake128_squeeze, vg_shake128_squeeze_sha3),
    }
);
shake!(
    /// An incremental SHAKE256 computation.
    Shake256,
    /// The output of SHAKE256, squeezed in pieces.
    Shake256Reader {
        rate: 136,
        update: (vg_shake256_update, vg_shake256_update_sha3),
        finalize: (vg_shake256_finalize, vg_shake256_finalize_sha3),
        squeeze: (vg_shake256_squeeze, vg_shake256_squeeze_sha3),
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};
    use crate::hashes::HashFunction;

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn backend_selection() {
        use super::Backend;
        use verified_garbage_cpu::{Features, feature};
        for apple in [false, true] {
            for requested in [false, true] {
                assert_eq!(
                    Backend::select(Features(0), apple, requested),
                    Backend::Scalar
                );
                assert_eq!(
                    Backend::select(Features(feature::SHA3), apple, requested),
                    if apple || requested {
                        Backend::Sha3
                    } else {
                        Backend::Scalar
                    }
                );
            }
        }
    }

    /// Compare the baseline and `_sha3` implementations of each function at
    /// every rate boundary, with split updates and multi-block output.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn scalar_matches_sha3() {
        use super::Backend;
        if Backend::select(crate::cpu::detected(), true, true) != Backend::Sha3 {
            return;
        }
        let msg: [u8; 3 * 168 + 1] = core::array::from_fn(|i| (i * 37 + 11) as u8);
        macro_rules! check_hash {
            ($h:ident) => {
                let rate = $h::BLOCK_SIZE;
                for len in [0, 1, rate - 1, rate, rate + 1, 2 * rate, 3 * rate + 1] {
                    for split in [0, 1.min(len), len / 2, len] {
                        let [a, b] = [Backend::Scalar, Backend::Sha3].map(|backend| {
                            let mut h = $h::new();
                            h.0.backend = Some(backend);
                            h.update(&msg[..split]);
                            h.update(&msg[split..len]);
                            h.finalize()
                        });
                        assert_eq!(a, b);
                    }
                }
            };
        }
        macro_rules! check_xof {
            ($h:ident) => {
                let rate = $h::BLOCK_SIZE;
                for len in [0, 1, rate - 1, rate, rate + 1, 2 * rate, 3 * rate + 1] {
                    for split in [0, 1.min(len), len / 2, len] {
                        let [a, b] = [Backend::Scalar, Backend::Sha3].map(|backend| {
                            let mut h = $h::new();
                            h.0.backend = Some(backend);
                            h.update(&msg[..split]);
                            h.update(&msg[split..len]);
                            let mut reader = h.finalize_xof();
                            let mut out = [0u8; 2 * 168 + 1];
                            reader.squeeze(&mut out[..rate - 1]);
                            reader.squeeze(&mut out[rate - 1..]);
                            out
                        });
                        assert_eq!(a, b);
                    }
                }
            };
        }
        check_hash!(Sha3_224);
        check_hash!(Sha3_256);
        check_hash!(Sha3_384);
        check_hash!(Sha3_512);
        check_xof!(Shake128);
        check_xof!(Shake256);
    }

    /// Every way of splitting a message into two updates, or into single
    /// bytes after the split, gives the same digest as one update, for
    /// every length up to past two blocks, through `HashFunction`.
    fn incremental<H: HashFunction>() {
        let msg: [u8; 300] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in (0..msg.len()).step_by(7).chain([
            H::BLOCK_SIZE - 1,
            H::BLOCK_SIZE,
            H::BLOCK_SIZE + 1,
            2 * H::BLOCK_SIZE - 1,
            2 * H::BLOCK_SIZE,
            2 * H::BLOCK_SIZE + 1,
        ]) {
            let expected = H::digest(&msg[..len]);
            for split in (0..=len).step_by(5) {
                let mut h = H::new();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize().as_ref(), expected.as_ref());
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize().as_ref(), expected.as_ref());
            }
        }
    }

    #[test]
    fn sha3_incremental() {
        incremental::<Sha3_224>();
        incremental::<Sha3_256>();
        incremental::<Sha3_384>();
        incremental::<Sha3_512>();
    }

    #[test]
    fn sha3_default() {
        assert_eq!(Sha3_224::default().finalize(), Sha3_224::digest(b""));
        assert_eq!(Sha3_256::default().finalize(), Sha3_256::digest(b""));
        assert_eq!(Sha3_384::default().finalize(), Sha3_384::digest(b""));
        assert_eq!(Sha3_512::default().finalize(), Sha3_512::digest(b""));
    }

    /// Splitting the message, and the output length: a prefix of a longer
    /// output is the shorter output.
    #[test]
    fn shake_incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        let mut long = [0u8; 500];
        Shake128::digest(&msg, &mut long);
        for split in (0..=msg.len()).step_by(13) {
            let mut h = Shake128::default();
            h.update(&msg[..split]);
            h.update(&msg[split..]);
            let mut out = [0u8; 337];
            h.finalize(&mut out);
            assert_eq!(out[..], long[..337]);
        }
        let mut long = [0u8; 500];
        Shake256::digest(&msg, &mut long);
        for split in (0..=msg.len()).step_by(13) {
            let mut h = Shake256::default();
            h.update(&msg[..split]);
            h.update(&msg[split..]);
            let mut out = [0u8; 273];
            h.finalize(&mut out);
            assert_eq!(out[..], long[..273]);
        }
    }

    /// Splitting a message into two updates around each rate boundary,
    /// including a partial block followed by two blocks, gives the output
    /// of one update.
    #[test]
    fn shake_absorb_boundaries() {
        let msg: [u8; 337] = core::array::from_fn(|i| (i * 11 + 5) as u8);
        macro_rules! check {
            ($xof:ident, $rate:literal) => {
                for len in [
                    $rate - 1,
                    $rate,
                    $rate + 1,
                    2 * $rate - 1,
                    2 * $rate,
                    2 * $rate + 1,
                ] {
                    let mut expected = [0u8; 32];
                    $xof::digest(&msg[..len], &mut expected);
                    for split in [0, 1, $rate - 1, $rate, $rate + 1, len]
                        .into_iter()
                        .filter(|&split| split <= len)
                    {
                        let mut h = $xof::new();
                        h.update(&msg[..split]);
                        h.update(&msg[split..len]);
                        let mut output = [0u8; 32];
                        h.finalize(&mut output);
                        assert_eq!(output, expected);
                    }
                }
            };
        }
        check!(Shake128, 168);
        check!(Shake256, 136);
    }

    /// Output squeezed in pieces of every size from 0 to 300 bytes is the
    /// output squeezed at once.
    #[test]
    fn shake_reader() {
        let mut long = [0u8; 2000];
        Shake128::digest(b"abc", &mut long);
        for piece in 0..300 {
            let mut r = Shake128::default().clone();
            r.update(b"abc");
            let mut r = r.finalize_xof();
            let mut out = [0u8; 2000];
            for chunk in out.chunks_mut(piece.max(1)) {
                r.clone().squeeze(&mut []);
                r.squeeze(chunk);
            }
            assert_eq!(out, long);
        }
        let mut long = [0u8; 2000];
        Shake256::digest(b"abc", &mut long);
        for piece in 1..300 {
            let mut h = Shake256::new();
            h.update(b"abc");
            let mut r = h.finalize_xof();
            let mut out = [0u8; 2000];
            for chunk in out.chunks_mut(piece) {
                r.squeeze(chunk);
            }
            assert_eq!(out, long);
        }
    }
}
