//! SHA3-224, SHA3-256, SHA3-384 and SHA3-512, and the extendable-output
//! functions SHAKE128 and SHAKE256 (FIPS 202).
//!
//! Each function has verified functions of its own, whose code has its rate
//! and domain-separation suffix and whose contracts name the function of
//! FIPS 202 they compute (`VG.Spec.Sha3`): `update` absorbs a piece of the
//! message, and `finalize` writes the digest (SHA-3) or pads the message for
//! `squeeze` to output it in pieces (SHAKE). Absorbing depends only on the
//! rate, so SHAKE256 absorbs with SHA3-256's `update`, of the same rate. This module keeps the state and
//! the position in the block that each call returns for the next; each call
//! runs the function's dispatcher (`crate::arch::dispatch::sha3`).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::sha3::{
    vg_sha3_224_finalize_auto, vg_sha3_224_update_auto, vg_sha3_256_finalize_auto,
    vg_sha3_256_update_auto, vg_sha3_384_finalize_auto, vg_sha3_384_update_auto,
    vg_sha3_512_finalize_auto, vg_sha3_512_update_auto, vg_shake128_finalize_auto,
    vg_shake128_squeeze_auto, vg_shake128_update_auto, vg_shake256_finalize_auto,
    vg_shake256_squeeze_auto,
};
use core::mem::MaybeUninit;

/// The working space of the `update` functions, aligned to a cache line.
#[repr(C, align(128))]
struct Scratch(MaybeUninit<[u64; 80]>);

/// The state of a computation absorbing a message: `state` represents the
/// message so far for the function's rate, and `pos` is the position its
/// `update` returned (the message's length modulo the rate, less than it).
#[derive(Clone)]
struct Absorbing {
    state: [u64; 25],
    pos: usize,
}

impl Absorbing {
    /// The empty message: the all-zero state, at position 0.
    const fn new() -> Self {
        Absorbing {
            state: [0; 25],
            pos: 0,
        }
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
}

impl Drop for Squeezing {
    fn drop(&mut self) {
        crate::zeroize::zeroize(&mut self.state);
    }
}

/// `update`: absorbs `data` into `$s` (an `Absorbing`), with the dispatcher
/// of the function's `update`.
macro_rules! absorb {
    ($s:expr, $data:expr, $update:ident) => {{
        let s: &mut Absorbing = $s;
        let data: &[u8] = $data;
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
        // other or the stack below the stack pointer. The dispatcher calls
        // only an implementation the CPU has the features of.
        s.pos = unsafe {
            $update(
                &mut s.state,
                s.pos,
                data.as_ptr(),
                data.len(),
                scratch.0.as_mut_ptr(),
            )
        };
    }};
}

/// Defines a SHA-3 hash function with a rate of `$rate` bytes,
/// `$output`-byte digests, and the dispatchers of the verified functions
/// `$update` and `$finalize`.
macro_rules! sha3 {
    ($(#[$doc:meta])* $name:ident {
        rate: $rate:literal,
        output: $output:literal,
        update: $update:ident,
        finalize: $finalize:ident $(,)?
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
                absorb!(&mut self.0, data, $update);
            }

            /// Pads the message and returns its digest.
            pub fn finalize(mut self) -> [u8; $output] {
                let mut digest = [0; $output];
                // SAFETY: as in `update`, `self.0.pos` is the position
                // `update` returned for the message `self.0.state`
                // represents; `self.0.state` is valid for reads and writes of
                // 200 bytes and `digest` for writes of its size, distinct
                // objects. The dispatcher calls only an implementation the
                // CPU has the features of.
                unsafe { $finalize(&mut self.0.state, self.0.pos, &mut digest) };
                digest
            }

            /// The digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; $output] {
                let mut h = Self::new();
                h.update(data);
                h.finalize()
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
/// the reader of its output, and the dispatchers of the verified functions
/// `$update`, `$finalize` and `$squeeze`.
macro_rules! shake {
    ($(#[$doc:meta])* $name:ident, $(#[$rdoc:meta])* $reader:ident {
        rate: $rate:literal,
        update: $update:ident,
        finalize: $finalize:ident,
        squeeze: $squeeze:ident $(,)?
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
                let s = &mut self.0;
                // SAFETY: `s.pos` is the position `finalize` (0) or the last
                // `squeeze` left, at most the rate, from which `s.state`
                // continues the output. `s.state` is valid for reads and
                // writes of 200 bytes and `out` for writes of `out.len()`
                // bytes; they are distinct objects, so they do not overlap
                // each other or the stack below the stack pointer. The
                // dispatcher calls only an implementation the CPU has the
                // features of.
                s.pos = unsafe { $squeeze(&mut s.state, s.pos, out.as_mut_ptr(), out.len()) };
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
                absorb!(&mut self.0, data, $update);
            }

            /// Pads the message and returns a reader of its output, which
            /// can be squeezed in pieces.
            pub fn finalize_xof(self) -> $reader {
                let mut state = self.0.state;
                // SAFETY: as in `update`, `self.0.pos` is the position
                // `update` returned for the message `state` represents;
                // `state` is valid for reads and writes of 200 bytes. The
                // dispatcher calls only an implementation the CPU has the
                // features of.
                unsafe { $finalize(&mut state, self.0.pos) };
                // From position 0, the padded state gives the output from its
                // first byte on.
                $reader(Squeezing { state, pos: 0 })
            }

            /// Pads the message and fills `out` with the first `out.len()`
            /// bytes of output.
            pub fn finalize(self, out: &mut [u8]) {
                self.finalize_xof().squeeze(out);
            }

            /// Fills `out` with the first `out.len()` bytes of output for
            /// `data`.
            pub fn digest(data: &[u8], out: &mut [u8]) {
                let mut h = Self::new();
                h.update(data);
                h.finalize(out);
            }
        }
    };
}

sha3!(
    /// An incremental SHA3-224 computation.
    Sha3_224 {
        rate: 144,
        output: 28,
        update: vg_sha3_224_update_auto,
        finalize: vg_sha3_224_finalize_auto,
    }
);
sha3!(
    /// An incremental SHA3-256 computation.
    Sha3_256 {
        rate: 136,
        output: 32,
        update: vg_sha3_256_update_auto,
        finalize: vg_sha3_256_finalize_auto,
    }
);
sha3!(
    /// An incremental SHA3-384 computation.
    Sha3_384 {
        rate: 104,
        output: 48,
        update: vg_sha3_384_update_auto,
        finalize: vg_sha3_384_finalize_auto,
    }
);
sha3!(
    /// An incremental SHA3-512 computation.
    Sha3_512 {
        rate: 72,
        output: 64,
        update: vg_sha3_512_update_auto,
        finalize: vg_sha3_512_finalize_auto,
    }
);
shake!(
    /// An incremental SHAKE128 computation.
    Shake128,
    /// The output of SHAKE128, squeezed in pieces.
    Shake128Reader {
        rate: 168,
        update: vg_shake128_update_auto,
        finalize: vg_shake128_finalize_auto,
        squeeze: vg_shake128_squeeze_auto,
    }
);
shake!(
    /// An incremental SHAKE256 computation.
    Shake256,
    /// The output of SHAKE256, squeezed in pieces.
    Shake256Reader {
        rate: 136,
        // SHA3-256's: absorbing depends only on the rate, which they share
        // (`VG.Spec.Sha3.updateContract`).
        update: vg_sha3_256_update_auto,
        finalize: vg_shake256_finalize_auto,
        squeeze: vg_shake256_squeeze_auto,
    }
);

#[cfg(test)]
mod tests {
    use super::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};
    use crate::hashes::HashFunction;

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
