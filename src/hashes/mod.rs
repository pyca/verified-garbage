//! Hash functions, one module each: MD5, SHA-1, the SHA-2 and SHA-3 families,
//! BLAKE2 and SM3.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod blake2;
pub mod blake2b;
pub mod blake2s;
pub mod md5;
pub mod sha1;
pub mod sha224;
pub mod sha256;
pub mod sha3;
pub mod sha384;
pub mod sha512;
pub mod sha512_224;
pub mod sha512_256;
pub mod sm3;
pub(crate) mod tables;

/// A hash function with an incremental interface, as used by the
/// constructions that are generic over it (HMAC).
pub trait HashFunction: Clone {
    /// The size of a digest, in bytes.
    const OUTPUT_SIZE: usize;
    /// The size of the input blocks, in bytes (the `B` of HMAC).
    const BLOCK_SIZE: usize;
    /// A digest: `OUTPUT_SIZE` bytes.
    type Output: AsRef<[u8]> + AsMut<[u8]> + Clone;

    /// Starts a new computation.
    fn new() -> Self;
    /// Absorbs `data`.
    fn update(&mut self, data: &[u8]);
    /// Returns the digest of everything absorbed.
    fn finalize(self) -> Self::Output;

    /// The digest of `data`.
    fn digest(data: &[u8]) -> Self::Output {
        let mut h = Self::new();
        h.update(data);
        h.finalize()
    }
}

/// Defines a hash function over verified streaming primitives:
///
/// * `init(state: *mut [u8; STATE])` makes `state` represent the empty
///   message;
/// * `update(state, count: u64, data: *const u8, len: usize)`
///   absorbs `len` bytes into a state representing a message of `count`
///   bytes;
/// * `finalize(state, count: u64, out: *mut [u8; OUTPUT])` writes the
///   digest.
///
/// `backends` names the enum of the implementations of `update` and
/// `finalize` to choose from, each a variant: first the one for the
/// target's baseline ISA, then any that need CPU features (their generated
/// `_FEATURES` constants), best first. An object uses the first
/// that the CPU can run, chosen when it is created (see `crate::cpu`).
///
/// `digests`, if given, is every implementation's one-shot
/// `digest(data: *const u8, len: usize, out: *mut [u8; OUTPUT])`, which
/// `digest` calls: the match is exhaustive, so an implementation without one
/// does not compile. Without it, `digest` uses the streaming functions.
///
/// `tables`, if given, is every implementation's tables of functions
/// (`crate::arch::fn_tables`), each with the generated constants of the CPU
/// features it needs (none for the baseline ISA's: it fails to compile if
/// they are not all among those `select` requires to choose that
/// implementation), which `tables` returns for the verified functions that take a hash function as a table
/// (`tables::TableHash`): its table of `Hash`, its table of `MdHash` and,
/// on the architectures with tables of `Hmac` (`tables::Tables`), its table
/// of `Hmac`. The match is exhaustive, so an implementation without its
/// tables does not compile.
///
/// Every region is a distinct Rust object, so none overlaps another or the
/// return address, and none wraps around the end of the address space; the
/// length is kept exactly (`update` panics rather than let it reach 2⁶⁴
/// bytes).
macro_rules! streaming_hash {
    // `digest`, with the one-shot `digests`.
    (@digest $backend:ident, $output:literal, { $($dvariant:ident)* }) => {
        /// The digest of `data`, in one call.
        pub fn digest(data: &[u8]) -> [u8; $output] {
            let mut out = [0; $output];
            // SAFETY: `data` is valid for reads of `data.len()` bytes and
            // `out` for writes of its size; they are distinct objects, so
            // they do not overlap each other, the return address or the
            // arguments on the stack, and do not wrap around the end of the
            // address space. The backend is selected for this CPU's
            // features.
            unsafe {
                $backend::select($crate::cpu::detected()).digest(data.as_ptr(), data.len(), &mut out)
            };
            out
        }
    };
    // `digest`, with the streaming functions.
    (@digest $backend:ident, $output:literal) => {
        /// The digest of `data`.
        pub fn digest(data: &[u8]) -> [u8; $output] {
            let mut h = Self::new();
            h.update(data);
            h.finalize()
        }
    };
    (
        $(#[$doc:meta])*
        $name:ident {
            state: $state:literal,
            block: $block:literal,
            output: $output:literal,
            init: $init:path,
            backends: $backend:ident {
                $base:ident => ($update:path, $finalize:path)
                $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => ($vupdate:path, $vfinalize:path))*
                $(,)?
            }
            $(, digests: {
                $($(#[$dattr:meta])* $dvariant:ident => $digest:path),* $(,)?
            })?
            $(, tables: {
                $($(#[$tattr:meta])* $tvariant:ident => {
                    hash: $thash:path [$($threq:path),*],
                    md_hash: $tmd:path [$($tmreq:path),*]
                    $(, hmac: $thmac:path [$($thmreq:path),*])? $(,)?
                }),* $(,)?
            })? $(,)?
        }
    ) => {
        /// The implementations of the streaming primitives.
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(crate) enum $backend {
            /// For the baseline ISA.
            $base,
            $(
                $(#[$attr])*
                /// Needing CPU features.
                $variant,
            )*
        }

        impl $backend {
            /// The CPU features `select` requires to choose each
            /// implementation, by its discriminant (none for the baseline):
            /// every CPU it is chosen for has them, so a function chosen
            /// with it may need no other, which its caller checks when it
            /// compiles (`assert!` in a `const`). (A hash function with no
            /// implementation but the baseline, and no tables, does not use
            /// it.)
            #[allow(dead_code)]
            pub(crate) const REQUIRES: &[verified_garbage_cpu::Features] = &[
                verified_garbage_cpu::Features(0),
                $(
                    $(#[$attr])*
                    verified_garbage_cpu::Features::all(&[$($req),*]),
                )*
            ];

            /// The best implementation a CPU with the features `f` can run.
            pub(crate) fn select(f: verified_garbage_cpu::Features) -> Self {
                $(
                    $(#[$attr])*
                    if f.contains(Self::REQUIRES[Self::$variant as usize]) {
                        return Self::$variant;
                    }
                )*
                let _ = f;
                Self::$base
            }

            /// `update`.
            ///
            /// # Safety
            ///
            /// As for the artifacts; the CPU must have the features of the
            /// implementation (as `select` guarantees).
            #[inline(always)]
            pub(crate) unsafe fn update(
                self,
                state: &mut [u8; $state],
                count: u64,
                data: *const u8,
                len: usize,
            ) {
                // SAFETY: the caller's obligations.
                unsafe {
                    match self {
                        Self::$base => $update(state, count, data, len),
                        $($(#[$attr])* Self::$variant => $vupdate(state, count, data, len),)*
                    }
                }
            }

            /// `finalize`.
            ///
            /// # Safety
            ///
            /// As for the artifacts; the CPU must have the features of the
            /// implementation (as `select` guarantees).
            #[inline(always)]
            pub(crate) unsafe fn finalize(
                self,
                state: &mut [u8; $state],
                count: u64,
                out: &mut [u8; $output],
            ) {
                // SAFETY: the caller's obligations.
                unsafe {
                    match self {
                        Self::$base => $finalize(state, count, out),
                        $($(#[$attr])* Self::$variant => $vfinalize(state, count, out),)*
                    }
                }
            }

            $(
            /// The one-shot `digest` of the `len` bytes at `data` into `out`.
            ///
            /// # Safety
            ///
            /// As for the artifacts; the CPU must have the features of the
            /// implementation (as `select` guarantees).
            pub(crate) unsafe fn digest(self, data: *const u8, len: usize, out: &mut [u8; $output]) {
                // SAFETY: the caller's obligations.
                unsafe {
                    match self {
                        $($(#[$dattr])* Self::$dvariant => $digest(data, len, out),)*
                    }
                }
            }
            )?
        }

        $(
        // Each implementation's tables need no CPU feature that `select`
        // does not require to choose it.
        $(
            $(#[$tattr])*
            const _: () = assert!(
                $backend::REQUIRES[$backend::$tvariant as usize].contains(
                    verified_garbage_cpu::Features::all(&[$($threq,)* $($tmreq,)* $($($thmreq),*)?])
                ),
                "a table needs a CPU feature its implementation is not chosen for"
            );
        )*

        impl $backend {
            /// The tables of functions of this implementation.
            pub(crate) fn tables(self) -> $crate::hashes::tables::Tables {
                match self {
                    $($(#[$tattr])* Self::$tvariant => $crate::hashes::tables::Tables {
                        #[cfg(feature = "alloc")]
                        hash: &$thash,
                        #[cfg(feature = "alloc")]
                        md_hash: &$tmd,
                        $(
                        hmac: &$thmac,
                        )?
                    },)*
                }
            }
        }
        )?

        $(#[$doc])*
        ///
        /// Messages are limited to 2⁶⁴ − 1 bytes.
        #[derive(Clone)]
        pub struct $name {
            /// The streaming state, representing the message so far.
            state: [u8; $state],
            /// The message length so far, in bytes.
            length: u64,
            /// The implementation this CPU runs.
            backend: $backend,
        }

        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }

        impl Drop for $name {
            /// Wipes the streaming state (which, for HMAC, represents the
            /// key).
            fn drop(&mut self) {
                $crate::zeroize::zeroize(&mut self.state);
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $output;
            /// The size of a message block, in bytes.
            pub const BLOCK_SIZE: usize = $block;

            /// Starts a new computation.
            pub fn new() -> Self {
                let mut state = [0; $state];
                // SAFETY: `state` is valid for writes of its size, and is a
                // distinct object from the return address (on x86-64 and x86)
                // and the argument on the stack (on x86); as a Rust object, it
                // does not wrap around the end of the address space.
                unsafe { $init(&mut state) };
                let backend = $backend::select($crate::cpu::detected());
                $name { state, length: 0, backend }
            }

            /// Absorbs `data`.
            ///
            /// # Panics
            ///
            /// If the message reaches 2⁶⁴ bytes.
            pub fn update(&mut self, data: &[u8]) {
                let (length, overflow) = self.length.overflowing_add(data.len() as u64);
                assert!(!overflow, "message too long");
                // SAFETY: `self.state` is valid for reads and writes of its
                // size and `data` for reads of `data.len()` bytes; they are
                // distinct objects, so they do not overlap each other, the return
                // address (on x86-64 and x86) or the arguments on the stack
                // (on 32-bit ARM and x86), and do not wrap around the end of
                // the address space. `self.length` is the length of the
                // message `self.state` represents. `self.backend` was
                // selected for this CPU's features.
                unsafe {
                    self.backend.update(
                        &mut self.state,
                        self.length,
                        data.as_ptr(),
                        data.len(),
                    )
                };
                self.length = length;
            }

            /// Pads the message and returns its digest.
            pub fn finalize(mut self) -> [u8; $output] {
                let mut out = [0; $output];
                // SAFETY: `self.state` is valid for reads and writes of its
                // size and `out` for writes of its size; they are distinct
                // objects, so they
                // do not overlap each other, the return address (on x86-64
                // and x86) or the arguments on the stack (on 32-bit ARM and
                // x86), and do not wrap around the end of the address space.
                // `self.length` is the exact length of the message
                // `self.state` represents. `self.backend` was selected for
                // this CPU's features.
                unsafe {
                    self.backend
                        .finalize(&mut self.state, self.length, &mut out)
                };
                out
            }

            $crate::hashes::streaming_hash!(@digest $backend, $output $(, { $($dvariant)* })?);

            /// A computation whose streaming state is `state`, which must
            /// represent a message of `length` bytes (for HMAC, whose
            /// `init` makes such states), and which runs the implementation
            /// `backend` (which must have been selected for this CPU).
            #[allow(dead_code)]
            pub(crate) fn from_state(state: [u8; $state], length: u64, backend: $backend) -> Self {
                $name { state, length, backend }
            }

            /// The implementation this computation runs, selected for this
            /// CPU, which functions built on it (e.g. HMAC's) follow.
            #[allow(dead_code)]
            pub(crate) fn backend(&self) -> $backend {
                self.backend
            }

            /// The streaming state, in place, and the length of the message
            /// it represents.
            #[allow(dead_code)]
            pub(crate) fn state_mut(&mut self) -> (&mut [u8; $state], u64) {
                (&mut self.state, self.length)
            }
        }

        impl $crate::hashes::HashFunction for $name {
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

use streaming_hash;
