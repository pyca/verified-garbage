//! What ML-KEM-768 and ML-KEM-1024 (`crate::mlkem768`, `crate::mlkem1024`)
//! share: their `Error`, and their API, defined once by `ml_kem!` for each
//! parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

/// Why an operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A `SampleNTT` reached the bound on its loop's iterations (FIPS 203
    /// Appendix B), which happens with probability less than 2⁻²⁶¹ for each
    /// call: less than 2⁻²⁵⁸ in an ML-KEM-768 operation (9 calls) and 2⁻²⁵⁷
    /// in an ML-KEM-1024 one (16 calls).
    SampleBound,
    /// The encapsulation key failed the check of FIPS 203 §7.2.
    InvalidKey,
    /// The operating system's random number generator failed.
    Randomness,
}

crate::error::impl_error! {
    Error {
        SampleBound => "ML-KEM sampling loop reached its bound",
        InvalidKey => "invalid ML-KEM encapsulation key",
        Randomness => "ML-KEM random number generator failed",
    }
}

/// The implementations key generation, encapsulation and decapsulation
/// follow: each has an instance calling each of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The target's baseline ISA (on x86-64, `SampleNTT` on one seed at a
    /// time; elsewhere, one entry of the matrix at a time), with scalar
    /// Keccak.
    Scalar,
    /// AArch64 with the SHA-3 extension: paired SHAKE with
    /// `vg_keccak_f1600_x2_sha3`, and arithmetic with NEON, hashing one
    /// state at a time with the scalar permutation `vg_keccak_f1600` (the
    /// `_x2_sha3` instances): faster on Arm's cores, such as Neoverse N2.
    #[cfg(target_arch = "aarch64")]
    X2Sha3,
    /// The same, hashing one state at a time with the SHA-3 extension's
    /// permutation `vg_keccak_f1600_sha3` (the `_x2_sha3_keccak_sha3`
    /// instances): faster on Apple's cores.
    #[cfg(target_arch = "aarch64")]
    X2Sha3KeccakSha3,
    /// AVX2: four instances of SHAKE128 at once.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// Four-way SHAKE with AVX-512VL quadword rotates.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// Select the best implementation supported by all three KEM operations,
    /// on a CPU with the features `f`, which is one of Apple's if `apple`.
    /// On x86-64, prefer the AVX-512VL sampler, then AVX2. On AArch64, with
    /// the SHA-3 extension, paired SHAKE, with the single-state permutation
    /// that is faster on the CPU: no CPU feature tells which, so the SHA-3
    /// extension's on Apple's cores, and the scalar one elsewhere (1.79
    /// times as fast as the SHA-3 extension's on Arm's Neoverse N2).
    // Each target uses only some of the arguments.
    #[allow(unused_variables)]
    pub(crate) fn select(
        f: verified_garbage_cpu::Features,
        avx2: verified_garbage_cpu::Features,
        avx512: verified_garbage_cpu::Features,
        sha3: verified_garbage_cpu::Features,
        apple: bool,
    ) -> Backend {
        #[cfg(target_arch = "aarch64")]
        if f.contains(sha3) {
            return if apple {
                Backend::X2Sha3KeccakSha3
            } else {
                Backend::X2Sha3
            };
        }
        #[cfg(target_arch = "x86_64")]
        if f.contains(avx512) {
            return Backend::Avx512;
        }
        #[cfg(target_arch = "x86_64")]
        if f.contains(avx2) {
            return Backend::Avx2;
        }
        Backend::Scalar
    }
}

/// Defines the API of one ML-KEM parameter set: its `EncapsulationKey` and
/// `DecapsulationKey`, over its verified `check_ek`, `keygen`, `encaps` and
/// `decaps` functions (and their instances on AArch64 with the SHA-3
/// extension and on x86-64 with AVX2 and AVX-512, with the features they
/// need), its sizes, and the number of `SampleNTT` calls in
/// each operation with the bound on the probability that one reaches its
/// loop's bound (for the comments). On x86-64, encapsulation with a key that
/// keeps the hash `H(ek)` (one from key generation) is `encaps_h` (and its
/// instances), which takes it; with one that does not (one from
/// `from_bytes`), `encaps` (and its instances), which computes it. On
/// x86-64, `scratch_written` gives how many bytes of `scratch` the AVX2 and
/// AVX-512 instances of each may write (their `_SCRATCH_WRITTEN`), if fewer
/// than all of it; the callers wipe only those.
macro_rules! ml_kem {
    (@written) => {
        (core::mem::size_of::<Scratch>(), core::mem::size_of::<Scratch>())
    };
    (@written $w:expr) => {
        $w
    };
    (
        name: $name:literal,
        encapsulation_key: $EncapsulationKey:ident,
        decapsulation_key: $DecapsulationKey:ident,
        check_ek: $check_ek:path,
        keygen: $keygen:path,
        encaps: $encaps:path,
        decaps: $decaps:path,
        encaps_h: $encaps_h:path,
        keygen_x2_sha3: ($keygen_x2_sha3:path, $keygen_x2_sha3_features:path),
        encaps_x2_sha3: ($encaps_x2_sha3:path, $encaps_x2_sha3_features:path),
        decaps_x2_sha3: ($decaps_x2_sha3:path, $decaps_x2_sha3_features:path),
        keygen_x2_sha3_keccak_sha3: ($keygen_x2_sha3_keccak_sha3:path, $keygen_x2_sha3_keccak_sha3_features:path $(,)?),
        encaps_x2_sha3_keccak_sha3: ($encaps_x2_sha3_keccak_sha3:path, $encaps_x2_sha3_keccak_sha3_features:path $(,)?),
        decaps_x2_sha3_keccak_sha3: ($decaps_x2_sha3_keccak_sha3:path, $decaps_x2_sha3_keccak_sha3_features:path $(,)?),
        keygen_avx2: ($keygen_avx2:path, $keygen_avx2_features:path),
        keygen_avx512: ($keygen_avx512:path, $keygen_avx512_features:path),
        encaps_h_avx2: ($encaps_h_avx2:path, $encaps_h_avx2_features:path),
        encaps_h_avx512: ($encaps_h_avx512:path, $encaps_h_avx512_features:path),
        encaps_avx2: ($encaps_avx2:path, $encaps_avx2_features:path),
        encaps_avx512: ($encaps_avx512:path, $encaps_avx512_features:path),
        decaps_avx2: ($decaps_avx2:path, $decaps_avx2_features:path),
        decaps_avx512: ($decaps_avx512:path, $decaps_avx512_features:path),
        check_ek_avx2: ($check_ek_avx2:path, $check_ek_avx2_features:path),
        ek: $ek:literal,
        dk: $dk:literal,
        ct: $ct:literal,
        scratch: $scratch:literal
        $(, scratch_written: {
            keygen: $keygen_written:expr,
            encaps_h: $encaps_h_written:expr,
            encaps: $encaps_written:expr,
            decaps: $decaps_written:expr $(,)?
        })? $(,)?
    ) => {
        pub use $crate::mlkem_common::Error;
        use $crate::mlkem_common::Backend;
        use $crate::zeroize::zeroize;

        /// The features of the instances of key generation, encapsulation and
        /// decapsulation of each implementation but the baseline's.
        #[cfg(target_arch = "x86_64")]
        const AVX2: &[verified_garbage_cpu::Features] = &[
            $keygen_avx2_features, $encaps_h_avx2_features, $encaps_avx2_features, $decaps_avx2_features,
            $check_ek_avx2_features,
        ];
        #[cfg(not(target_arch = "x86_64"))]
        const AVX2: &[verified_garbage_cpu::Features] = &[];
        #[cfg(target_arch = "x86_64")]
        const AVX512: &[verified_garbage_cpu::Features] = &[
            $keygen_avx512_features, $encaps_h_avx512_features, $encaps_avx512_features, $decaps_avx512_features,
            $check_ek_avx2_features,
        ];
        #[cfg(not(target_arch = "x86_64"))]
        const AVX512: &[verified_garbage_cpu::Features] = &[];
        #[cfg(target_arch = "aarch64")]
        const SHA3: &[verified_garbage_cpu::Features] = &[
            $keygen_x2_sha3_features, $encaps_x2_sha3_features, $decaps_x2_sha3_features,
            $keygen_x2_sha3_keccak_sha3_features, $encaps_x2_sha3_keccak_sha3_features,
            $decaps_x2_sha3_keccak_sha3_features,
        ];
        #[cfg(not(target_arch = "aarch64"))]
        const SHA3: &[verified_garbage_cpu::Features] = &[];

        /// The implementation to call: the best one whose instances of key
        /// generation, encapsulation and decapsulation the CPU can all run.
        fn backend() -> Backend {
            Backend::select(
                $crate::cpu::detected(),
                const { verified_garbage_cpu::Features::all(AVX2) },
                const { verified_garbage_cpu::Features::all(AVX512) },
                const { verified_garbage_cpu::Features::all(SHA3) },
                cfg!(target_vendor = "apple"),
            )
        }

        /// The working space of the assembly functions.
        type Scratch = [u64; $scratch];

        /// How many bytes of `scratch` the AVX2 and AVX-512 instances of
        /// each operation may write (`Artifact.written`).
        #[cfg(target_arch = "x86_64")]
        const KEYGEN_WRITTEN: (usize, usize) = $crate::mlkem_common::ml_kem!(@written $($keygen_written)?);
        #[cfg(target_arch = "x86_64")]
        const ENCAPS_H_WRITTEN: (usize, usize) = $crate::mlkem_common::ml_kem!(@written $($encaps_h_written)?);
        #[cfg(target_arch = "x86_64")]
        const ENCAPS_WRITTEN: (usize, usize) = $crate::mlkem_common::ml_kem!(@written $($encaps_written)?);
        #[cfg(target_arch = "x86_64")]
        const DECAPS_WRITTEN: (usize, usize) = $crate::mlkem_common::ml_kem!(@written $($decaps_written)?);

        /// The bytes of `scratch` that `backend`'s instance of an operation,
        /// whose AVX2 and AVX-512 instances write `written`, may write.
        #[cfg(target_arch = "x86_64")]
        fn scratch_written(backend: Backend, written: (usize, usize)) -> usize {
            match backend {
                Backend::Scalar => core::mem::size_of::<Scratch>(),
                Backend::Avx2 => written.0,
                Backend::Avx512 => written.1,
            }
        }

        #[doc = concat!("An ", $name, " encapsulation key, which passed the check of FIPS 203 §7.2.")]
        #[derive(Clone)]
        pub struct $EncapsulationKey {
            bytes: [u8; $ek],
            /// `H(ek)`, which encapsulation takes on x86-64 when the key
            /// keeps it (a key from key generation); without it (a key from
            /// `from_bytes`), encapsulation computes it.
            #[cfg(target_arch = "x86_64")]
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
            /// than `q`); [`Error::InvalidKey`] otherwise.
            pub fn from_bytes(bytes: &[u8; $ek]) -> Result<Self, Error> {
                // SAFETY: `bytes` is valid for reads of its size, and a Rust
                // object, so it does not overlap the stack or wrap around the
                // end of the address space. The CPU has the features of
                // `backend()`, which include those of `$check_ek_avx2`.
                #[cfg(target_arch = "x86_64")]
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $check_ek(bytes),
                        Backend::Avx2 | Backend::Avx512 => $check_ek_avx2(bytes),
                    }
                };
                // SAFETY: as above.
                #[cfg(not(target_arch = "x86_64"))]
                let r = unsafe { $check_ek(bytes) };
                if r == 1 {
                    Ok($EncapsulationKey {
                        bytes: *bytes,
                        #[cfg(target_arch = "x86_64")]
                        h: None,
                    })
                } else {
                    Err(Error::InvalidKey)
                }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $ek] {
                &self.bytes
            }

            /// `ML-KEM.Encaps` (FIPS 203 Algorithm 20): a shared secret key
            /// and its ciphertext, with 32 bytes of randomness from the
            /// operating system.
            pub fn encapsulate(&self) -> Result<([u8; 32], [u8; $ct]), Error> {
                let mut m = [0u8; 32];
                getrandom::fill(&mut m).map_err(|_| Error::Randomness)?;
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
            pub fn encapsulate_internal(&self, m: &[u8; 32]) -> Result<([u8; 32], [u8; $ct]), Error> {
                // SAFETY: `backend()` chose an implementation whose features
                // the CPU has.
                unsafe { self.encapsulate_with(m, backend()) }
            }

            /// `encapsulate_internal`, with the implementation `backend`.
            ///
            /// # Safety
            ///
            /// The CPU has the features of `backend`'s instances.
            unsafe fn encapsulate_with(
                &self, m: &[u8; 32], backend: Backend,
            ) -> Result<([u8; 32], [u8; $ct]), Error> {
                let mut key = [0u8; 32];
                let mut ct = [0u8; $ct];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.bytes`, `h` (on x86-64), `m`, `key`, `ct` and
                // `scratch` are valid for reads (and, for the last three,
                // writes) of their sizes; they are distinct Rust objects, so
                // they do not overlap each other or the stack, or wrap around
                // the end of the address space. `self.bytes` passed the
                // encapsulation key check, and `h`, if the key keeps it, is
                // its SHA3-256 hash `H(ek)`: the key generation writes it in
                // the decapsulation key, from which `from_seed` takes it. The
                // caller ensures the CPU has the features of `backend`.
                #[cfg(not(target_arch = "x86_64"))]
                let r = unsafe {
                    match backend {
                        Backend::Scalar => $encaps(&self.bytes, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3 => $encaps_x2_sha3(&self.bytes, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3KeccakSha3 => {
                            $encaps_x2_sha3_keccak_sha3(&self.bytes, m, &mut key, &mut ct, scratch.as_mut_ptr())
                        }
                    }
                };
                // SAFETY: as above.
                #[cfg(target_arch = "x86_64")]
                let r = unsafe {
                    let (ek, s) = (&self.bytes, scratch.as_mut_ptr());
                    match (backend, &self.h) {
                        (Backend::Scalar, Some(h)) => $encaps_h(ek, h, m, &mut key, &mut ct, s),
                        (Backend::Scalar, None) => $encaps(ek, m, &mut key, &mut ct, s),
                        (Backend::Avx2, Some(h)) => $encaps_h_avx2(ek, h, m, &mut key, &mut ct, s),
                        (Backend::Avx2, None) => $encaps_avx2(ek, m, &mut key, &mut ct, s),
                        (Backend::Avx512, Some(h)) => $encaps_h_avx512(ek, h, m, &mut key, &mut ct, s),
                        (Backend::Avx512, None) => $encaps_avx512(ek, m, &mut key, &mut ct, s),
                    }
                };
                // The bytes of `scratch` the operation may have written: on
                // x86-64 those its instance's `_SCRATCH_WRITTEN` gives
                // (`Artifact.written`), elsewhere all of it.
                #[cfg(target_arch = "x86_64")]
                let written = scratch_written(backend, if self.h.is_some() { ENCAPS_H_WRITTEN } else { ENCAPS_WRITTEN });
                #[cfg(not(target_arch = "x86_64"))]
                let written = core::mem::size_of::<Scratch>();
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized, and `written`
                // does not exceed it. Wipe on both success and failure before
                // inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), written);
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    zeroize(&mut ct);
                    return Err(Error::SampleBound);
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
            pub fn from_seed(seed: &[u8; 64]) -> Result<Self, Error> {
                // SAFETY: `backend()` chose an implementation whose features
                // the CPU has.
                unsafe { Self::from_seed_with(seed, backend()) }
            }

            /// `from_seed`, with the implementation `backend`.
            ///
            /// # Safety
            ///
            /// The CPU has the features of `backend`'s instances.
            unsafe fn from_seed_with(seed: &[u8; 64], backend: Backend) -> Result<Self, Error> {
                let mut key = $DecapsulationKey {
                    seed: *seed,
                    ek: $EncapsulationKey {
                        bytes: [0; $ek],
                        #[cfg(target_arch = "x86_64")]
                        h: None,
                    },
                    dk: [0; $dk],
                };
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. The caller ensures the CPU has the
                // features of `backend`.
                let r = unsafe {
                    match backend {
                        Backend::Scalar => $keygen(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3 => $keygen_x2_sha3(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3KeccakSha3 => {
                            $keygen_x2_sha3_keccak_sha3(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr())
                        }
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $keygen_avx2(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx512 => $keygen_avx512(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                    }
                };
                // The bytes of `scratch` the operation may have written: on
                // x86-64 those its instance's `_SCRATCH_WRITTEN` gives
                // (`Artifact.written`), elsewhere all of it.
                #[cfg(target_arch = "x86_64")]
                let written = scratch_written(backend, KEYGEN_WRITTEN);
                #[cfg(not(target_arch = "x86_64"))]
                let written = core::mem::size_of::<Scratch>();
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized, and `written`
                // does not exceed it. Wipe on both success and failure before
                // inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), written);
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives; dropping `key`
                    // destroys it.
                    // NO-COVERAGE-START
                    return Err(Error::SampleBound);
                    // NO-COVERAGE-END
                }
                // `H(ek)`, which the decapsulation key holds before `z`
                // (FIPS 203 Algorithm 16).
                #[cfg(target_arch = "x86_64")]
                {
                    let mut h = [0u8; 32];
                    h.copy_from_slice(&key.dk[$dk - 64..$dk - 32]);
                    key.ek.h = Some(h);
                }
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
            pub fn decapsulate(&self, ct: &[u8; $ct]) -> Result<[u8; 32], Error> {
                // SAFETY: `backend()` chose an implementation whose features
                // the CPU has.
                unsafe { self.decapsulate_with(ct, backend()) }
            }

            /// `decapsulate`, with the implementation `backend`.
            ///
            /// # Safety
            ///
            /// The CPU has the features of `backend`'s instances.
            unsafe fn decapsulate_with(&self, ct: &[u8; $ct], backend: Backend) -> Result<[u8; 32], Error> {
                let mut key = [0u8; 32];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each
                // other or the stack, or wrap around the end of the address
                // space. `self.dk` was written by the key generation. The
                // caller ensures the CPU has the features of `backend`.
                let r = unsafe {
                    match backend {
                        Backend::Scalar => $decaps(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3 => $decaps_x2_sha3(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::X2Sha3KeccakSha3 => {
                            $decaps_x2_sha3_keccak_sha3(&self.dk, ct, &mut key, scratch.as_mut_ptr())
                        }
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $decaps_avx2(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx512 => $decaps_avx512(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                    }
                };
                // The bytes of `scratch` the operation may have written: on
                // x86-64 those its instance's `_SCRATCH_WRITTEN` gives
                // (`Artifact.written`), elsewhere all of it.
                #[cfg(target_arch = "x86_64")]
                let written = scratch_written(backend, DECAPS_WRITTEN);
                #[cfg(not(target_arch = "x86_64"))]
                let written = core::mem::size_of::<Scratch>();
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized, and `written`
                // does not exceed it. Wipe on both success and failure before
                // inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), written);
                }
                if r != 1 {
                    // A `SampleNTT` reaches its bound with the probability
                    // the module's documentation gives.
                    // NO-COVERAGE-START
                    zeroize(&mut key);
                    return Err(Error::SampleBound);
                    // NO-COVERAGE-END
                }
                Ok(key)
            }
        }

        #[cfg(all(test, target_arch = "aarch64"))]
        mod backend_tests {
            use super::{Backend, $DecapsulationKey, SHA3};

            /// With the SHA-3 extension, both paired instances (whichever
            /// `backend()` chooses, which the known-answer tests run) agree
            /// with the baseline's on keys, shared keys and ciphertexts, and
            /// on the implicit rejection of a modified ciphertext.
            #[test]
            fn paired_instances_agree() {
                if !$crate::cpu::detected().contains(const { verified_garbage_cpu::Features::all(SHA3) }) {
                    return;
                }
                for i in 0..2u8 {
                    let seed: [u8; 64] = core::array::from_fn(|j| (j as u8).wrapping_mul(29) ^ i);
                    let m: [u8; 32] = core::array::from_fn(|j| (j as u8).wrapping_mul(13) ^ i);
                    // SAFETY: the baseline needs no feature.
                    let base = unsafe { $DecapsulationKey::from_seed_with(&seed, Backend::Scalar) }.unwrap();
                    let ek = base.encapsulation_key();
                    // SAFETY: as above.
                    let (k, mut ct) = unsafe { ek.encapsulate_with(&m, Backend::Scalar) }.unwrap();
                    for backend in [Backend::X2Sha3, Backend::X2Sha3KeccakSha3] {
                        // SAFETY: the CPU has the SHA-3 extension, which
                        // every paired instance needs (`SHA3`).
                        let dk = unsafe { $DecapsulationKey::from_seed_with(&seed, backend) }.unwrap();
                        assert!(dk.ek == base.ek && dk.dk == base.dk, "{backend:?}");
                        // SAFETY: as above.
                        assert_eq!(unsafe { ek.encapsulate_with(&m, backend) }.unwrap(), (k, ct));
                        // SAFETY: as above.
                        assert_eq!(unsafe { dk.decapsulate_with(&ct, backend) }.unwrap(), k);
                    }
                    ct[i as usize] ^= 1;
                    // SAFETY: as above.
                    let rejected = unsafe { base.decapsulate_with(&ct, Backend::Scalar) }.unwrap();
                    assert_ne!(rejected, k);
                    for backend in [Backend::X2Sha3, Backend::X2Sha3KeccakSha3] {
                        // SAFETY: as above.
                        assert_eq!(unsafe { base.decapsulate_with(&ct, backend) }.unwrap(), rejected);
                    }
                }
            }
        }
    };
}

pub(crate) use ml_kem;

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::Backend;
    use verified_garbage_cpu::{Features, feature};

    #[test]
    fn selects_complete_feature_sets() {
        let avx2 = Features(feature::AVX | feature::AVX2);
        let avx512 = Features(feature::AVX | feature::AVX2 | feature::AVX512F | feature::AVX512VL);
        let sha3 = Features(0);
        for apple in [false, true] {
            assert_eq!(
                Backend::select(avx512, avx2, avx512, sha3, apple),
                Backend::Avx512
            );
        }
        for features in [
            avx2,
            Features(feature::AVX | feature::AVX2 | feature::AVX512F),
            Features(feature::AVX | feature::AVX2 | feature::AVX512VL),
        ] {
            assert_eq!(
                Backend::select(features, avx2, avx512, sha3, false),
                Backend::Avx2
            );
        }
        for features in [
            Features(0),
            Features(feature::AVX | feature::AVX512F | feature::AVX512VL),
        ] {
            assert_eq!(
                Backend::select(features, avx2, avx512, sha3, false),
                Backend::Scalar
            );
        }
    }
}

#[cfg(all(test, target_arch = "aarch64"))]
mod aarch64_tests {
    use super::Backend;
    use verified_garbage_cpu::{Features, feature};

    #[test]
    fn selects_complete_feature_sets() {
        let empty = Features(0);
        let required = Features(feature::NEON | feature::SHA3);
        // The SHA-3 extension's single-state permutation on Apple's cores,
        // the scalar one elsewhere.
        assert_eq!(
            Backend::select(required, empty, empty, required, true),
            Backend::X2Sha3KeccakSha3
        );
        assert_eq!(
            Backend::select(required, empty, empty, required, false),
            Backend::X2Sha3
        );
        for available in [empty, Features(feature::NEON), Features(feature::SHA3)] {
            for apple in [false, true] {
                assert_eq!(
                    Backend::select(available, empty, empty, required, apple),
                    Backend::Scalar
                );
            }
        }
    }
}
