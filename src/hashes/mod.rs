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

/// Defines a hash function over the dispatchers of verified streaming
/// primitives (`crate::arch::dispatch`), each of which runs the best
/// implementation this CPU runs:
///
/// * `init(state: *mut [u8; STATE])` makes `state` represent the empty
///   message;
/// * `update(state, count: u64, data: *const u8, len: usize)`
///   absorbs `len` bytes into a state representing a message of `count`
///   bytes;
/// * `finalize(state, count: u64, out: *mut [u8; OUTPUT])` writes the
///   digest;
/// * `digest(data: *const u8, len: usize, out: *mut [u8; OUTPUT])`, if
///   given, writes the digest of the `len` bytes at `data` in one call.
///   Without it, `digest` uses the streaming functions.
///
/// Every region is a distinct Rust object, so none overlaps another or the
/// return address, and none wraps around the end of the address space; the
/// length is kept exactly (`update` panics rather than let it reach 2⁶⁴
/// bytes).
macro_rules! streaming_hash {
    // `digest`, with the one-shot `digest`.
    (@digest $output:literal, $digest:path) => {
        /// The digest of `data`, in one call.
        pub fn digest(data: &[u8]) -> [u8; $output] {
            let mut out = [0; $output];
            // SAFETY: `data` is valid for reads of `data.len()` bytes and
            // `out` for writes of its size; they are distinct objects, so
            // they do not overlap each other, the return address or the
            // arguments on the stack, and do not wrap around the end of the
            // address space. The dispatcher calls only an implementation
            // the CPU has the features of.
            unsafe { $digest(data.as_ptr(), data.len(), &mut out) };
            out
        }
    };
    // `digest`, with the streaming functions.
    (@digest $output:literal) => {
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
            update: $update:path,
            finalize: $finalize:path
            $(, digest: $digest:path)?
            $(,)?
        }
    ) => {
        $(#[$doc])*
        ///
        /// Messages are limited to 2⁶⁴ − 1 bytes.
        #[derive(Clone)]
        pub struct $name {
            /// The streaming state, representing the message so far.
            state: $crate::align::CacheAligned<[u8; $state]>,
            /// The message length so far, in bytes.
            length: u64,
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
                $crate::zeroize::zeroize(&mut self.state.0);
            }
        }

        impl $name {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = $output;
            /// The size of a message block, in bytes.
            pub const BLOCK_SIZE: usize = $block;

            /// Starts a new computation.
            pub fn new() -> Self {
                let mut state = $crate::align::CacheAligned([0; $state]);
                // SAFETY: `state` is valid for writes of its size, and is a
                // distinct object from the return address (on x86-64 and x86)
                // and the argument on the stack (on x86); as a Rust object, it
                // does not wrap around the end of the address space.
                unsafe { $init(&mut state.0) };
                $name { state, length: 0 }
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
                // message `self.state` represents. The dispatcher calls only
                // an implementation the CPU has the features of.
                unsafe { $update(&mut self.state.0, self.length, data.as_ptr(), data.len()) };
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
                // `self.state` represents. The dispatcher calls only an
                // implementation the CPU has the features of.
                unsafe { $finalize(&mut self.state.0, self.length, &mut out) };
                out
            }

            $crate::hashes::streaming_hash!(@digest $output $(, $digest)?);

            /// A computation whose streaming state is `state`, which must
            /// represent a message of `length` bytes (for HMAC, whose
            /// `init` makes such states).
            #[allow(dead_code)]
            pub(crate) fn from_state(state: [u8; $state], length: u64) -> Self {
                $name {
                    state: $crate::align::CacheAligned(state),
                    length,
                }
            }

            /// The streaming state, in place, and the length of the message
            /// it represents.
            #[allow(dead_code)]
            pub(crate) fn state_mut(&mut self) -> (&mut [u8; $state], u64) {
                (&mut self.state.0, self.length)
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
