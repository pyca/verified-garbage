//! What BLAKE2b and BLAKE2s (RFC 7693) share.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "x86",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

/// Defines a BLAKE2 hash function with blocks of `$block` bytes (sixteen
/// words of `$block / 16` bytes) over verified streaming primitives:
///
/// * `init(state: *mut [u8; STATE], outlen: usize, key: *const u8, keylen: usize)`
///   makes `state` represent the key block (none for an empty key), hashed
///   from the initial state for an `outlen`-byte digest;
/// * `update(state, count: u64, data: *const u8, len: usize)`
///   absorbs `len` bytes into a state representing data of `count` bytes;
/// * `finalize(state, count: u64, out: *mut [u8; MAX])` writes the
///   final hash value, whose first `outlen` bytes are the digest.
///
/// `update` and `finalize` are their dispatchers
/// (`crate::arch::dispatch::blake2<b|s>`), which run the best
/// implementation this CPU runs.
///
/// Every region is a distinct Rust object, so none overlaps another, the
/// return address (on x86-64 and x86), the arguments on the stack (on 32-bit
/// ARM and x86) or the stack below them that the call uses, and none wraps
/// around the end of the address space; the length is kept exactly
/// (`update` panics rather than let it reach 2⁶⁴ bytes).
macro_rules! blake2 {
    (
        $(#[$doc:meta])*
        $name:ident {
            state: $state:literal,
            block: $block:literal,
            max: $max:literal,
            init: $init:path,
            update: $update:path,
            finalize: $finalize:path $(,)?
        }
    ) => {
        $(#[$doc])*
        ///
        /// `N` is the size of the digest, 1 to
        #[doc = concat!(stringify!($max), " bytes (a compile-time error otherwise).")]
        /// Keys are at most as long as the largest digest, and data (after
        /// a key block, for keyed hashing) is limited to 2⁶⁴ − 1 bytes.
        #[derive(Clone)]
        pub struct $name<const N: usize = $max> {
            /// The streaming state, representing the data so far.
            state: $crate::align::CacheAligned<[u8; $state]>,
            /// The length of the data so far (the key block included), in
            /// bytes.
            length: u64,
            /// Whether the computation is keyed, a MAC, which takes data
            /// independent timing (see `crate::dit`).
            keyed: bool,
        }

        impl<const N: usize> Drop for $name<N> {
            /// Wipes the streaming state (which represents the key, if any).
            fn drop(&mut self) {
                $crate::zeroize::zeroize(&mut self.state.0);
            }
        }

        impl<const N: usize> Default for $name<N> {
            fn default() -> Self {
                Self::new()
            }
        }

        impl<const N: usize> $name<N> {
            /// The size of a digest, in bytes.
            pub const OUTPUT_SIZE: usize = N;
            /// The size of a block, in bytes.
            pub const BLOCK_SIZE: usize = $block;
            /// The largest digest and key, in bytes.
            pub const MAX_SIZE: usize = $max;

            /// Starts a new (unkeyed) computation.
            pub fn new() -> Self {
                Self::new_keyed(&[])
            }

            /// Starts a new computation keyed with `key` (RFC 7693 §2.9), or
            /// unkeyed if `key` is empty.
            ///
            /// # Panics
            ///
            #[doc = concat!("If `key` is longer than ", stringify!($max), " bytes.")]
            pub fn new_keyed(key: &[u8]) -> Self {
                crate::dit::enter_if!(dit, !key.is_empty(), crate::dit::Why::UnkeyedHash);
                Self::new_keyed_with(dit, key)
            }

            /// [`new_keyed`](Self::new_keyed), with the token of the
            /// operation it is part of (see `crate::dit`).
            fn new_keyed_with(dit: crate::dit::Dit<'_>, key: &[u8]) -> Self {
                const { assert!(1 <= N && N <= $max, "unsupported digest size") };
                assert!(key.len() <= $max, "key too long");
                let mut state = $crate::align::CacheAligned([0; $state]);
                // SAFETY: `1 ≤ N ≤ MAX` and `key.len() ≤ MAX`. `state` is
                // valid for writes of its size and `key` for reads of
                // `key.len()` bytes; they are distinct objects, so they do
                // not overlap each other, the return address (on x86-64 and
                // x86) or the arguments on the stack (on x86), and do not
                // wrap around the end of the address space.
                unsafe { $init(dit, &mut state.0, N, key.as_ptr(), key.len()) };
                // The key block is the first block of the data.
                let length = if key.is_empty() { 0 } else { $block };
                $name { state, length, keyed: !key.is_empty() }
            }

            /// Absorbs `data`.
            ///
            /// # Panics
            ///
            /// If the data reaches 2⁶⁴ bytes.
            pub fn update(&mut self, data: &[u8]) {
                crate::dit::enter_if!(dit, self.keyed, crate::dit::Why::UnkeyedHash);
                self.update_with(dit, data);
            }

            /// [`update`](Self::update), with the token of the operation it
            /// is part of (see `crate::dit`).
            fn update_with(&mut self, dit: crate::dit::Dit<'_>, data: &[u8]) {
                let length = self
                    .length
                    .checked_add(data.len() as u64)
                    .expect("data too long");
                // SAFETY: `self.state` is valid for reads and writes of its
                // size and `data` for reads of `data.len()` bytes; they are
                // distinct objects, so they do not overlap each other, the return
                // address (on x86-64 and x86), the arguments on the stack
                // (on 32-bit ARM and x86) or the stack below them that the
                // call uses, and do not wrap around the end of the address
                // space. `self.length` is the length of the data
                // `self.state` represents, and adding `data.len()` to it
                // does not reach 2⁶⁴. The dispatcher calls only an
                // implementation the CPU has the features of.
                unsafe { $update(dit, &mut self.state.0, self.length, data.as_ptr(), data.len()) };
                self.length = length;
            }

            /// Returns the digest of the data.
            pub fn finalize(self) -> [u8; N] {
                crate::dit::enter_if!(dit, self.keyed, crate::dit::Why::UnkeyedHash);
                self.finalize_with(dit)
            }

            /// [`finalize`](Self::finalize), with the token of the operation
            /// it is part of (see `crate::dit`).
            fn finalize_with(mut self, dit: crate::dit::Dit<'_>) -> [u8; N] {
                let mut out = [0; $max];
                // SAFETY: `self.state` is valid for reads and writes of its
                // size and `out` for writes of its size; they are distinct
                // objects, so they
                // do not overlap each other, the return address (on x86-64
                // and x86), the arguments on the stack (on 32-bit ARM and
                // x86) or the stack below them that the call uses, and do not
                // wrap around the end of the address space. `self.length` is
                // the exact length, less than 2⁶⁴, of the data `self.state`
                // represents. The dispatcher calls only an implementation
                // the CPU has the features of.
                unsafe { $finalize(dit, &mut self.state.0, self.length, &mut out) };
                let mut digest = [0; N];
                digest.copy_from_slice(&out[..N]);
                digest
            }

            /// Checks that `mac` is the digest of the data (its MAC, if the
            /// computation is keyed), in constant time: the time taken does
            /// not depend on where, or whether, `mac` differs from it (its
            /// length is public). `mac` must be the whole digest, of `N`
            /// bytes; a truncated one is rejected.
            pub fn verify(self, mac: &[u8]) -> Result<(), $crate::error::InvalidMac> {
                crate::dit::enter_if!(dit, self.keyed, crate::dit::Why::UnkeyedHash);
                if $crate::ct::eq(dit, &self.finalize_with(dit), mac) {
                    Ok(())
                } else {
                    Err($crate::error::InvalidMac)
                }
            }

            /// The (unkeyed) digest of `data`.
            pub fn digest(data: &[u8]) -> [u8; N] {
                Self::digest_keyed(&[], data)
            }

            /// The digest of `data` keyed with `key` (a MAC; RFC 7693 §2.9).
            ///
            /// # Panics
            ///
            #[doc = concat!("If `key` is longer than ", stringify!($max), " bytes.")]
            pub fn digest_keyed(key: &[u8], data: &[u8]) -> [u8; N] {
                crate::dit::enter_if!(dit, !key.is_empty(), crate::dit::Why::UnkeyedHash);
                let mut h = Self::new_keyed_with(dit, key);
                h.update_with(dit, data);
                h.finalize_with(dit)
            }
        }

        impl<const N: usize> super::HashFunction for $name<N> {
            const OUTPUT_SIZE: usize = N;
            const BLOCK_SIZE: usize = $block;
            type Output = [u8; N];

            fn new() -> Self {
                $name::new()
            }

            fn update(&mut self, data: &[u8]) {
                $name::update(self, data)
            }

            fn finalize(self) -> [u8; N] {
                $name::finalize(self)
            }
        }
    };
}

pub(super) use blake2;

#[cfg(test)]
mod tests {
    use super::super::blake2b::Blake2b;
    use super::super::blake2s::Blake2s;
    use crate::error::InvalidMac;

    /// `verify`, run by a computation of `mac`, accepts `mac` and rejects
    /// any other: one with a bit flipped in its first, a middle or its last
    /// byte, a truncated MAC, an empty one and a longer one.
    fn check<const N: usize>(mac: [u8; N], verify: impl Fn(&[u8]) -> Result<(), InvalidMac>) {
        assert_eq!(verify(&mac), Ok(()));
        for i in [0, N / 2, N - 1] {
            let mut bad = mac;
            bad[i] ^= 1;
            assert_eq!(verify(&bad), Err(InvalidMac));
        }
        assert_eq!(verify(&mac[..N - 1]), Err(InvalidMac));
        assert_eq!(verify(&[]), Err(InvalidMac));
        let mut longer = [0u8; 65];
        longer[..N].copy_from_slice(&mac);
        assert_eq!(verify(&longer[..N + 1]), Err(InvalidMac));
    }

    /// `verify`, keyed and unkeyed, for the largest digest and a smaller
    /// one.
    #[test]
    fn verify() {
        let (key, data) = (b"key", b"data");
        macro_rules! sizes {
            ($($hash:ident<$n:literal>),*) => {$(
                check($hash::<$n>::digest_keyed(key, data), |m| {
                    let mut h = $hash::<$n>::new_keyed(key);
                    h.update(data);
                    h.verify(m)
                });
                check($hash::<$n>::digest(data), |m| {
                    let mut h = $hash::<$n>::new();
                    h.update(data);
                    h.verify(m)
                });
            )*};
        }
        sizes!(Blake2b<64>, Blake2b<20>, Blake2s<32>, Blake2s<16>);
    }
}
