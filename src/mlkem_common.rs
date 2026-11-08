//! What ML-KEM-768 and ML-KEM-1024 share: their API, defined once by
//! `ml_kem!`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

/// Defines the API of one ML-KEM parameter set: its `EncapsulationKey` and
/// `DecapsulationKey`, over the dispatchers of its verified `check_ek`,
/// `keygen`, `encaps` and `decaps` functions (`_auto`, which run the best
/// implementation the CPU supports), its sizes, and the number of `SampleNTT` calls in
/// each operation with the bound on the probability that one reaches its
/// loop's bound (for the comments). Encapsulation with a key that keeps the
/// hash `H(ek)` (one from key generation) is `encaps_h`, which takes it;
/// with one that does not (one from `from_bytes`), `encaps`, which computes
/// it. `from_bytes` does not compute
/// `H(ek)` itself so that `encaps` can: on AArch64, its paired instances hash
/// it in Keccak lanes the matrix sampling leaves idle, almost for free.
/// On x86-64 and AArch64 each operation wipes what it writes of `scratch`
/// itself; elsewhere it may write all of it, which the callers wipe.
macro_rules! ml_kem {
    (
        name: $name:literal,
        encapsulation_key: $EncapsulationKey:ident,
        decapsulation_key: $DecapsulationKey:ident,
        check_ek: $check_ek:path,
        keygen: $keygen:path,
        encaps: $encaps:path,
        decaps: $decaps:path,
        encaps_h: $encaps_h:path,
        ek: $ek:literal,
        dk: $dk:literal,
        ct: $ct:literal,
        scratch: $scratch:literal $(,)?
    ) => {
        use $crate::error::{InvalidKey, MlKemError};
        use $crate::zeroize::zeroize;

        /// The working space of the assembly functions, aligned to a cache line:
        /// their vector loads and stores of it are then never split across
        /// two (wherever the stack frame puts it, which made the instances
        /// up to about 5% slower).
        #[repr(C, align(64))]
        struct Scratch([u64; $scratch]);

        #[doc = concat!("An ", $name, " encapsulation key, which passed the check of FIPS 203 §7.2.")]
        #[derive(Clone)]
        pub struct $EncapsulationKey {
            bytes: [u8; $ek],
            /// `H(ek)`, which encapsulation takes when the key keeps it (a
            /// key from key generation); without it (a key from
            /// `from_bytes`), encapsulation computes it.
            h: Option<[u8; 32]>,
        }

        /// Two keys are equal if their bytes are (`h` is their hash, if kept).
        impl PartialEq for $EncapsulationKey {
            fn eq(&self, other: &Self) -> bool {
                self.bytes == other.bytes
            }
        }

        impl Eq for $EncapsulationKey {}

        impl core::fmt::Debug for $EncapsulationKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($EncapsulationKey)).finish_non_exhaustive()
            }
        }

        impl $EncapsulationKey {
            /// The size of an encapsulation key, in bytes.
            pub const SIZE: usize = $ek;
            /// The size of a ciphertext, in bytes.
            pub const CIPHERTEXT_SIZE: usize = $ct;
            /// The size of a shared secret key, in bytes.
            pub const SHARED_KEY_SIZE: usize = 32;

            /// The encapsulation key `bytes`, if it passes the encapsulation
            /// key check of FIPS 203 §7.2 (every integer it encodes is less
            /// than `q`); [`InvalidKey`] otherwise.
            pub fn from_bytes(bytes: &[u8; $ek]) -> Result<Self, InvalidKey> {
                // SAFETY: `bytes` is valid for reads of its size, and a Rust
                // object, so it does not overlap the stack or wrap around the
                // end of the address space. The dispatcher calls only an
                // implementation the CPU has the features of.
                let r = unsafe { $check_ek(bytes) };
                if r == 1 {
                    Ok($EncapsulationKey { bytes: *bytes, h: None })
                } else {
                    Err(InvalidKey)
                }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $ek] {
                &self.bytes
            }

            /// `ML-KEM.Encaps` (FIPS 203 Algorithm 20): a shared secret key
            /// and its ciphertext, with 32 bytes of randomness from the
            /// operating system.
            pub fn encapsulate(&self) -> Result<([u8; 32], [u8; $ct]), MlKemError> {
                let mut m = [0u8; 32];
                getrandom::fill(&mut m).map_err(|_| MlKemError::Randomness)?;
                let r = self.encapsulate_internal(&m);
                zeroize(&mut m);
                r
            }

            /// `ML-KEM.Encaps_internal(ek, m)` (FIPS 203 Algorithm 17), with
            /// the randomness `m`: for known-answer tests only. FIPS 203 §6
            /// allows this function only for testing; `m` must otherwise be
            /// fresh random bytes from an approved RBG, which
            /// [`encapsulate`](Self::encapsulate) draws.
            #[doc(hidden)]
            pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; $ct]), MlKemError> {
                let mut key = [0u8; 32];
                let mut ct = [0u8; $ct];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.bytes`, `h`, `m`, `key`, `ct` and
                // `scratch` are valid for reads (and, for the last three,
                // writes) of their sizes; they are distinct Rust objects, so
                // they do not overlap each other or the stack, or wrap around
                // the end of the address space. `self.bytes` passed the
                // encapsulation key check, and `h`, if the key keeps it, is
                // its SHA3-256 hash `H(ek)`: the key generation writes it in
                // the decapsulation key, from which `from_seed` takes it. The
                // dispatchers call only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    let (ek, s) = (&self.bytes, scratch.as_mut_ptr().cast());
                    match &self.h {
                        Some(h) => $encaps_h(ek, h, m, &mut key, &mut ct, s),
                        None => $encaps(ek, m, &mut key, &mut ct, s),
                    }
                };
                // On x86-64 and AArch64 the verified function wiped what it
                // wrote of `scratch`. Elsewhere, wipe all of it, which the operation may
                // have written, on both success and failure before inspecting
                // the return status.
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>());
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    zeroize(&mut ct);
                    return Err(MlKemError::SampleBound);
                    // NO-COVERAGE-END
                }
                Ok((key, ct))
            }
        }

        #[doc = concat!(
            "An ", $name, " decapsulation key, kept as the seed `d ‖ z` it is generated from, \
            with the keys it expands to. The seed and the expanded key are destroyed when it is \
            dropped."
        )]
        pub struct $DecapsulationKey {
            seed: [u8; 64],
            ek: $EncapsulationKey,
            dk: [u8; $dk],
        }

        impl core::fmt::Debug for $DecapsulationKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($DecapsulationKey)).finish_non_exhaustive()
            }
        }

        impl Drop for $DecapsulationKey {
            fn drop(&mut self) {
                zeroize(&mut self.seed);
                zeroize(&mut self.dk);
            }
        }

        impl $DecapsulationKey {
            /// The size of a seed, in bytes.
            pub const SEED_SIZE: usize = 64;

            /// The key pair of the seed `d ‖ z` (`d` its first 32 bytes, `z`
            /// the last 32): `ML-KEM.KeyGen_internal(d, z)` (FIPS 203
            /// Algorithm 16). The seed must be 64 random bytes from an
            /// approved RBG (FIPS 203 §3.3, Algorithm 19), or a seed so
            /// generated before.
            pub fn from_seed(seed: &[u8; 64]) -> Result<Self, MlKemError> {
                let mut key = $DecapsulationKey {
                    seed: *seed,
                    ek: $EncapsulationKey { bytes: [0; $ek], h: None },
                    dk: [0; $dk],
                };
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. The dispatcher calls only an
                // implementation the CPU has the features of.
                let r = unsafe { $keygen(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr().cast()) };
                // On x86-64 and AArch64 the verified function wiped what it
                // wrote of `scratch`. Elsewhere, wipe all of it, which the operation may
                // have written, on both success and failure before inspecting
                // the return status.
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>());
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives; dropping `key`
                    // destroys it.
                    // NO-COVERAGE-START
                    return Err(MlKemError::SampleBound);
                    // NO-COVERAGE-END
                }
                // `H(ek)`, which the decapsulation key holds before `z`
                // (FIPS 203 Algorithm 16; `VG.Spec.MlKem.keyGenInternal_h`).
                let mut h = [0u8; 32];
                h.copy_from_slice(&key.dk[$dk - 64..$dk - 32]);
                key.ek.h = Some(h);
                Ok(key)
            }

            /// The seed `d ‖ z`.
            pub fn seed(&self) -> &[u8; 64] {
                &self.seed
            }

            /// The encapsulation key.
            pub fn encapsulation_key(&self) -> &$EncapsulationKey {
                &self.ek
            }

            /// `ML-KEM.Decaps` (FIPS 203 Algorithm 21): the shared secret key
            /// of the ciphertext `ct`, which is the implicit rejection key
            /// `J(z ‖ ct)` if `ct` is not a ciphertext of this key (in
            /// constant time: nothing tells whether it was rejected).
            pub fn decapsulate(&self, ct: &[u8; $ct]) -> Result<[u8; 32], MlKemError> {
                let mut key = [0u8; 32];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each
                // other or the stack, or wrap around the end of the address
                // space. `self.dk` was written by the key generation. The
                // dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe { $decaps(&self.dk, ct, &mut key, scratch.as_mut_ptr().cast()) };
                // On x86-64 and AArch64 the verified function wiped what it
                // wrote of `scratch`. Elsewhere, wipe all of it, which the operation may
                // have written, on both success and failure before inspecting
                // the return status.
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>());
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    return Err(MlKemError::SampleBound);
                    // NO-COVERAGE-END
                }
                Ok(key)
            }
        }
    };
}

pub(crate) use ml_kem;
