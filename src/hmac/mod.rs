//! HMAC (FIPS 198-1, RFC 2104), for any hash function with a verified HMAC
//! implementation.
//!
//! The construction is the same for every hash function `H` ([`HmacHash`]);
//! what each one provides, in a module of its own here, is verified
//! assembly for a key of any length, which computes
//! `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))` (`VG.Spec.Hmac.hmac`): a key
//! longer than a block is hashed by the verified `init` itself (FIPS 198-1
//! §4, steps 1–3), in working space it wipes before returning.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use crate::hashes::HashFunction;

mod md5;
mod sha1;
mod sha224;
mod sha256;
mod sha384;
mod sha512;
mod sha512_224;
mod sha512_256;

mod sealed {
    pub trait Sealed {}
}

/// A hash function with a verified HMAC implementation.
pub trait HmacHash: HashFunction + sealed::Sealed {
    /// The state of an HMAC computation.
    #[doc(hidden)]
    type State: Clone;
    /// A state with no key yet, for [`HmacHash::hmac_init`] to key in place:
    /// it holds nothing secret, so it may be moved.
    #[doc(hidden)]
    fn hmac_empty() -> Self::State;
    /// Starts an HMAC computation in `state` with a key of any length.
    #[doc(hidden)]
    fn hmac_init(state: &mut Self::State, key: &[u8]);
    /// Absorbs `data`.
    #[doc(hidden)]
    fn hmac_update(state: &mut Self::State, data: &[u8]);
    /// Returns the MAC, finalizing `state` in place (where it is wiped when
    /// it is dropped).
    #[doc(hidden)]
    fn hmac_finalize(state: &mut Self::State) -> Self::Output;
    /// Restores the state `hmac_init` keyed, in place, after
    /// [`HmacHash::hmac_finalize`].
    #[doc(hidden)]
    fn hmac_reset(state: &mut Self::State);
}

/// The MAC did not match: the message or the key is not what was
/// authenticated. [`crate::cmac`], [`crate::poly1305`] and keyed BLAKE2
/// ([`crate::hashes::blake2b`], [`crate::hashes::blake2s`]) return this
/// type too.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidMac;

impl core::fmt::Display for InvalidMac {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("MAC does not match")
    }
}

impl core::error::Error for InvalidMac {}

/// An incremental HMAC computation with the hash function `H`.
///
/// Its state, which represents the key, is wiped when it is dropped. The
/// computation keys and finalizes it in place, and leaves no copy of it
/// behind: [`Hmac::new`] moves it to the caller and wipes its own. A copy the
/// caller makes (by [`Clone`], or by moving the value) is wiped only where
/// it is dropped, and is not wiped where it was moved from: this includes the
/// copy Rust may make of a variable to pass it to [`Hmac::finalize`] or
/// [`Hmac::verify`], which take it by value. [`Hmac::mac`] makes none, and
/// neither does [`Hmac::finalize_reset`], which takes it by reference.
#[derive(Clone)]
pub struct Hmac<H: HmacHash> {
    state: H::State,
}

impl<H: HmacHash> Hmac<H> {
    /// Starts an HMAC computation with `key`, of any length (a key longer
    /// than the block size is hashed first).
    // Never inlined, here and in `finalize` and `verify`: inlined, a call
    // copies the state between the caller's variable and the function's,
    // and leaves the copy wiped at the end unwiped where it was; a call
    // passes the caller's variable by its address.
    #[inline(never)]
    pub fn new(key: &[u8]) -> Self {
        let mut h = core::mem::ManuallyDrop::new(Self::empty());
        H::hmac_init(&mut h.state, key);
        // Rust does not build a returned local in the caller's place:
        // returning `h` would copy it there and leave this copy as it is.
        // So the copy is read out as the function's value, straight into
        // the caller's place, and `h`, never dropped, is zeroed when `wipe`
        // is dropped, after the value is computed. (Binding the copy to a
        // local first would put it in a temporary of its own, left as it
        // is.)
        let wipe = WipeOnDrop(&mut h);
        // SAFETY: `h` is a computation, valid for reads, which `wipe` keeps
        // borrowed until after the read; it is never dropped, so the copy
        // is the only computation that owns its state, whatever the state
        // owns.
        unsafe { core::ptr::read(&**wipe.0) }
    }

    /// A computation with no key yet, for `init` to key in place.
    fn empty() -> Self {
        Hmac {
            state: H::hmac_empty(),
        }
    }

    /// Absorbs `data`.
    pub fn update(&mut self, data: &[u8]) {
        H::hmac_update(&mut self.state, data);
    }

    /// Returns the MAC of everything absorbed.
    #[inline(never)]
    pub fn finalize(mut self) -> H::Output {
        H::hmac_finalize(&mut self.state)
    }

    /// Returns the MAC of everything absorbed, and starts a new computation
    /// with the same key in place, ready for the next message (the key is
    /// not needed again). Unlike [`Hmac::finalize`], it never moves the
    /// state, so it leaves no copy of it where the caller's variable was.
    pub fn finalize_reset(&mut self) -> H::Output {
        let mac = H::hmac_finalize(&mut self.state);
        H::hmac_reset(&mut self.state);
        mac
    }

    /// Checks that `mac` is the MAC of everything absorbed, in constant
    /// time: the time taken does not depend on where, or whether, `mac`
    /// differs from it (its length is public). `mac` must be the whole MAC,
    /// of `H::OUTPUT_SIZE` bytes; a truncated one is rejected.
    #[inline(never)]
    pub fn verify(mut self, mac: &[u8]) -> Result<(), InvalidMac> {
        if crate::ct::eq(H::hmac_finalize(&mut self.state).as_ref(), mac) {
            Ok(())
        } else {
            Err(InvalidMac)
        }
    }

    /// The MAC of `data` with `key`.
    pub fn mac(key: &[u8], data: &[u8]) -> H::Output {
        // Keyed and finalized in place, and wiped when it is dropped.
        let mut h = Self::empty();
        H::hmac_init(&mut h.state, key);
        h.update(data);
        H::hmac_finalize(&mut h.state)
    }
}

/// Zeroes the value it borrows, never dropped, when it is dropped: `new`'s
/// local, once its copy is the function's value.
struct WipeOnDrop<'a, T>(&'a mut core::mem::ManuallyDrop<T>);

impl<T> Drop for WipeOnDrop<'_, T> {
    fn drop(&mut self) {
        let p: *mut core::mem::ManuallyDrop<T> = self.0;
        // SAFETY: the value is valid for writes of its size, and is never
        // read or dropped again (it is in a `ManuallyDrop`).
        unsafe { crate::zeroize::zeroize_raw(p.cast::<u8>(), core::mem::size_of::<T>()) };
    }
}

/// An HMAC computation with a hash function over verified streaming
/// primitives: the computation of the inner hash, whose message is
/// `(K₀ ⊕ ipad) ‖ text`, the streaming state of the outer one, which
/// represents `K₀ ⊕ opad`, and the `V`-byte hash value of `K₀ ⊕ ipad` (the
/// inner state once keyed, of one block, whose buffer it does not read), for
/// `finalize_reset` to restore.
/// In C's layout, so `ipad` directly follows `outer` (arrays of bytes, with
/// no padding between them), for one wipe of both.
#[doc(hidden)]
#[derive(Clone)]
#[repr(C)]
pub struct StreamingHmacState<H, const S: usize, const V: usize> {
    pub(crate) inner: H,
    pub(crate) outer: [u8; S],
    pub(crate) ipad: [u8; V],
}

impl<H, const S: usize, const V: usize> Drop for StreamingHmacState<H, S, V> {
    /// Wipes the outer state, which represents `K₀ ⊕ opad`, and the hash
    /// value of `K₀ ⊕ ipad`, in one call (the inner hash wipes its own).
    fn drop(&mut self) {
        // SAFETY: `outer` and `ipad` are the `S + V` bytes from `outer`'s
        // start (`repr(C)`: in that order, each of alignment 1, so with no
        // padding between them), valid for writes, in a value being dropped.
        unsafe { crate::zeroize::zeroize_raw(self.outer.as_mut_ptr(), S + V) };
    }
}

/// Makes a hash function over verified streaming primitives (defined by
/// `streaming_hash!`) an [`HmacHash`], with its verified
/// `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize` (contracts
/// `VG.Spec.Hmac.Instance.initAnyKeyContract` and `finalizeContract` of the
/// hash's `Instance`), given its streaming state size and its digest size.
/// The text is absorbed by the hash's own `update`.
///
/// `init` and `finalize` are listed for each implementation of the hash (its
/// backend enum's variants, with the CPU features they need), and a
/// computation runs those of the implementation its hash was selected for:
/// the `match` on the backend is exhaustive, so a new implementation of the
/// hash does not compile until its HMAC functions are listed here too (see
/// "Variants and generic callers" in `lean/VerifiedGarbage/TCB/Emit.lean`),
/// and a test checks that they need no CPU feature the hash's
/// implementation was not selected for.
macro_rules! streaming_hmac {
    (
        $hash:ident ($backend:ident) {
            $base:ident => ($init:path, $finalize:path)
            $(, $(#[$attr:meta])* $variant:ident if [$($req:path),*] => ($vinit:path, $vfinalize:path))*
            $(,)?
        },
        state: $state:literal,
        output: $output:literal $(,)?
    ) => {
        // The CPU features of each implementation, which `tests` checks.
        $(
            $(#[$attr])*
            const _: &[$crate::cpu::Features] = &[$($req),*];
        )*

        impl super::sealed::Sealed for $hash {}

        impl super::HmacHash for $hash {
            // The hash value is the start of the streaming state, before
            // its block buffer.
            type State = super::StreamingHmacState<$hash, $state, { $state - $hash::BLOCK_SIZE }>;

            fn hmac_empty() -> Self::State {
                let backend = $backend::select($crate::cpu::detected());
                super::StreamingHmacState {
                    inner: $hash::from_state([0; $state], Self::BLOCK_SIZE as u64, backend),
                    outer: [0; $state],
                    ipad: [0; $state - $hash::BLOCK_SIZE],
                }
            }

            fn hmac_init(state: &mut Self::State, key: &[u8]) {
                let init = match state.inner.backend() {
                    $backend::$base => $init,
                    $($(#[$attr])* $backend::$variant => $vinit,)*
                };
                // The states are written in place, where they are wiped when
                // the computation is dropped. Once `init` has run, the inner
                // one represents `K₀ ⊕ ipad`, of a block.
                let (inner, _) = state.inner.state_mut();
                // SAFETY: `inner` and `state.outer` are valid for reads and
                // writes of a streaming state and `key` for reads of
                // `key.len()` bytes (of any length); they are distinct
                // objects or fields, so they do not overlap each other or the
                // call's stack frame, nor wrap around the address space.
                // `init` needs no CPU feature that the hash's implementation
                // was not selected for (`tests::backend_features`).
                unsafe { init(inner, &mut state.outer, key.as_ptr(), key.len()) };
                // Its hash value, for `hmac_reset`: copied in place.
                state.ipad.copy_from_slice(&inner[..$state - $hash::BLOCK_SIZE]);
            }

            fn hmac_reset(state: &mut Self::State) {
                // The keyed inner state, of one block, in place: its hash
                // value, and the length of `K₀ ⊕ ipad`. Its buffer, of no byte
                // of the message, is not read.
                let (inner, _) = state.inner.state_mut();
                inner[..$state - $hash::BLOCK_SIZE].copy_from_slice(&state.ipad);
                state.inner.set_length(Self::BLOCK_SIZE as u64);
            }

            fn hmac_update(state: &mut Self::State, data: &[u8]) {
                state.inner.update(data);
            }

            fn hmac_finalize(state: &mut Self::State) -> [u8; $output] {
                let finalize = match state.inner.backend() {
                    $backend::$base => $finalize,
                    $($(#[$attr])* $backend::$variant => $vfinalize,)*
                };
                // The inner state is finalized in place, and wiped with the
                // computation.
                let (inner, count) = state.inner.state_mut();
                let mut mac = [0; $output];
                // SAFETY: `inner` is valid for reads and writes of a streaming
                // state, `state.outer` for reads of one and `mac` for writes
                // of a digest; they are distinct objects or fields, so they do
                // not overlap each other or the call's stack frame, nor wrap
                // around the address space. `inner` represents `(K₀ ⊕ ipad) ‖
                // text`, of `count` bytes (which the hash's `update` keeps
                // below 2⁶⁴, so the text is shorter than 2⁶⁴ − B bytes), and
                // `state.outer` represents `K₀ ⊕ opad`. `finalize` needs no
                // CPU feature that the hash's implementation was not selected
                // for (`tests::backend_features`).
                unsafe { finalize(inner, &state.outer, count, &mut mac) };
                mac
            }
        }

        #[cfg(test)]
        mod tests {
            #[allow(unused_imports)]
            use super::*;

            /// Each implementation's `init` and `finalize` need no CPU
            /// feature that the hash's implementation is not selected for:
            /// on every set of features that selects it.
            #[test]
            fn backend_features() {
                $(
                    $(#[$attr])*
                    for bits in 0..1u32 << $crate::cpu::NAMES.len() {
                        let f = $crate::cpu::Features(bits);
                        if $backend::select(f) == $backend::$variant {
                            assert!(f.contains($crate::cpu::Features::all(&[$($req),*])));
                        }
                    }
                )*
            }

            /// A key longer than a block gives the MAC of its digest (FIPS
            /// 198-1 §4, step 2), which the verified `init` computes, and a
            /// key of a block is used as it is: keys of a block and of one
            /// byte more up to several blocks, with the implementation this
            /// CPU runs.
            #[test]
            fn long_key() {
                use $crate::hashes::HashFunction;
                let b = <$hash as HashFunction>::BLOCK_SIZE;
                let data = b"data";
                let mut bytes = [0u8; 1000];
                for (i, x) in bytes.iter_mut().enumerate() {
                    *x = i as u8;
                }
                for len in [b + 1, b + 2, 2 * b, 2 * b + 3, 1000] {
                    let key = &bytes[..len];
                    let digest = <$hash as HashFunction>::digest(key);
                    assert_eq!(
                        super::super::Hmac::<$hash>::mac(key, data).as_ref(),
                        super::super::Hmac::<$hash>::mac(digest.as_ref(), data).as_ref(),
                    );
                }
                let key = &bytes[..b];
                let digest = <$hash as HashFunction>::digest(key);
                assert_ne!(
                    super::super::Hmac::<$hash>::mac(key, data).as_ref(),
                    super::super::Hmac::<$hash>::mac(digest.as_ref(), data).as_ref(),
                );
            }

            /// `finalize_reset` returns the MAC and leaves the computation
            /// keyed again: each message after it, of no byte, of a block and
            /// longer, gets its MAC with the same key, as `mac` computes it,
            /// for a short key and one longer than a block, with the
            /// implementation this CPU runs.
            #[test]
            fn finalize_reset() {
                use $crate::hashes::HashFunction;
                let b = <$hash as HashFunction>::BLOCK_SIZE;
                let mut bytes = [0u8; 1000];
                for (i, x) in bytes.iter_mut().enumerate() {
                    *x = (i as u8).wrapping_mul(7);
                }
                for key in [&bytes[..16], &bytes[..2 * b + 3]] {
                    let mut h = super::super::Hmac::<$hash>::new(key);
                    for data in [&bytes[..3], &bytes[..0], &bytes[..b], &bytes[..3 * b + 5], &bytes[..3]] {
                        h.update(data);
                        assert_eq!(
                            h.finalize_reset().as_ref(),
                            super::super::Hmac::<$hash>::mac(key, data).as_ref(),
                        );
                    }
                    // After a reset, `finalize` and `verify` see only what
                    // follows it.
                    h.update(&bytes[..b + 1]);
                    let mac = super::super::Hmac::<$hash>::mac(key, &bytes[..b + 1]);
                    assert!(h.clone().verify(mac.as_ref()).is_ok());
                    assert_eq!(h.finalize().as_ref(), mac.as_ref());
                }
            }
        }
    };
}

use streaming_hmac;

#[cfg(test)]
mod tests {
    use super::{Hmac, InvalidMac};
    use crate::hashes::sha256::Sha256;

    /// `verify` accepts the MAC and rejects any other, including a changed
    /// byte anywhere, a truncated MAC and a longer one.
    #[test]
    fn verify() {
        let (key, data) = (b"key", b"data");
        let mac = Hmac::<Sha256>::mac(key, data);
        let check = |m: &[u8]| {
            let mut h = Hmac::<Sha256>::new(key);
            h.update(data);
            h.verify(m)
        };
        assert_eq!(check(&mac), Ok(()));
        for i in 0..mac.len() {
            let mut bad = mac;
            bad[i] ^= 1;
            assert_eq!(check(&bad), Err(InvalidMac));
        }
        assert_eq!(check(&mac[..16]), Err(InvalidMac));
        let mut longer = [0u8; 33];
        longer[..32].copy_from_slice(&mac);
        assert_eq!(check(&longer), Err(InvalidMac));
    }
}
