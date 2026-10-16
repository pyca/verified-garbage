//! What ML-KEM-768 and ML-KEM-1024 (`crate::mlkem768`, `crate::mlkem1024`)
//! share: their `Error`, and their API, defined once by `ml_kem!` for each
//! parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
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
    /// Paired AArch64 SHAKE and arithmetic with NEON and SHA-3.
    #[cfg(target_arch = "aarch64")]
    PairedSha3,
    /// AVX2: four instances of SHAKE128 at once.
    #[cfg(target_arch = "x86_64")]
    Avx2,
    /// Four-way SHAKE with AVX-512VL quadword rotates.
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl Backend {
    /// Select the best implementation supported by all three KEM operations.
    /// On x86-64, prefer the AVX-512VL sampler, then AVX2. On AArch64,
    /// select paired SHAKE independently of standalone hashing.
    // Each target uses only some of the arguments.
    #[allow(unused_variables)]
    pub(crate) fn select(
        f: crate::cpu::Features,
        avx2: crate::cpu::Features,
        avx512: crate::cpu::Features,
        sha3: crate::cpu::Features,
    ) -> Backend {
        #[cfg(target_arch = "aarch64")]
        if f.contains(sha3) {
            return Backend::PairedSha3;
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
/// `decaps` functions (and their SHA-3 and AVX2 instances, with the
/// features they need), its sizes, and the number of `SampleNTT` calls in
/// each operation with the bound on the probability that one reaches its
/// loop's bound (for the comments). On x86-64, encapsulation is `encaps_h`
/// (and its instances), which takes the hash `H(ek)` the key keeps.
macro_rules! ml_kem {
    (
        name: $name:literal,
        encapsulation_key: $EncapsulationKey:ident,
        decapsulation_key: $DecapsulationKey:ident,
        check_ek: $check_ek:path,
        keygen: $keygen:path,
        encaps: $encaps:path,
        decaps: $decaps:path,
        keygen_sha3: ($keygen_sha3:path, $keygen_sha3_features:path),
        encaps_h: $encaps_h:path,
        encaps_sha3: ($encaps_sha3:path, $encaps_sha3_features:path),
        decaps_sha3: ($decaps_sha3:path, $decaps_sha3_features:path),
        keygen_paired_sha3: ($keygen_paired_sha3:path, $keygen_paired_sha3_features:path),
        encaps_paired_sha3: ($encaps_paired_sha3:path, $encaps_paired_sha3_features:path),
        decaps_paired_sha3: ($decaps_paired_sha3:path, $decaps_paired_sha3_features:path),
        keygen_avx2: ($keygen_avx2:path, $keygen_avx2_features:path),
        keygen_avx512: ($keygen_avx512:path, $keygen_avx512_features:path),
        encaps_h_avx2: ($encaps_h_avx2:path, $encaps_h_avx2_features:path),
        encaps_h_avx512: ($encaps_h_avx512:path, $encaps_h_avx512_features:path),
        decaps_avx2: ($decaps_avx2:path, $decaps_avx2_features:path),
        decaps_avx512: ($decaps_avx512:path, $decaps_avx512_features:path),
        ek: $ek:literal,
        dk: $dk:literal,
        ct: $ct:literal,
        scratch: $scratch:literal $(,)?
    ) => {
        pub use $crate::mlkem_common::Error;
        use $crate::mlkem_common::Backend;
        use $crate::zeroize::zeroize;

        /// The implementation to call: the best one whose instances of key
        /// generation, encapsulation and decapsulation the CPU can all run.
        fn backend() -> Backend {
            #[cfg(target_arch = "x86_64")]
            const AVX2: &[$crate::cpu::Features] =
                &[$keygen_avx2_features, $encaps_h_avx2_features, $decaps_avx2_features];
            #[cfg(not(target_arch = "x86_64"))]
            const AVX2: &[$crate::cpu::Features] = &[];
            #[cfg(target_arch = "x86_64")]
            const AVX512: &[$crate::cpu::Features] =
                &[$keygen_avx512_features, $encaps_h_avx512_features, $decaps_avx512_features];
            #[cfg(not(target_arch = "x86_64"))]
            const AVX512: &[$crate::cpu::Features] = &[];
            #[cfg(target_arch = "aarch64")]
            const SHA3: &[$crate::cpu::Features] =
                &[$keygen_paired_sha3_features, $encaps_paired_sha3_features, $decaps_paired_sha3_features];
            #[cfg(not(target_arch = "aarch64"))]
            const SHA3: &[$crate::cpu::Features] = &[];
            Backend::select(
                $crate::cpu::detected(),
                const { $crate::cpu::Features::all(AVX2) },
                const { $crate::cpu::Features::all(AVX512) },
                const { $crate::cpu::Features::all(SHA3) },
            )
        }

        /// The working space of the assembly functions.
        type Scratch = [u64; $scratch];

        #[doc = concat!("An ", $name, " encapsulation key, which passed the check of FIPS 203 §7.2.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $EncapsulationKey {
            bytes: [u8; $ek],
            /// `H(ek)`, which encapsulation takes on x86-64.
            #[cfg(target_arch = "x86_64")]
            h: [u8; 32],
        }

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
                // end of the address space.
                if unsafe { $check_ek(bytes) } == 1 {
                    Ok($EncapsulationKey {
                        bytes: *bytes,
                        #[cfg(target_arch = "x86_64")]
                        h: $crate::hashes::sha3::Sha3_256::digest(bytes),
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
                let mut key = [0u8; 32];
                let mut ct = [0u8; $ct];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.bytes`, `self.h` (on x86-64), `m`, `key`,
                // `ct` and `scratch` are valid for reads (and, for the last
                // three, writes) of their sizes; they are distinct Rust
                // objects, so they do not overlap each other or the stack, or
                // wrap around the end of the address space. `self.bytes`
                // passed the encapsulation key check, and `self.h` is its
                // SHA3-256 hash `H(ek)`: `from_bytes` computes it, and the
                // key generation writes it in the decapsulation key, from
                // which `from_seed` takes it. `backend()` chose an
                // implementation whose features the CPU has.
                let r = unsafe {
                    match backend() {
                        #[cfg(not(target_arch = "x86_64"))]
                        Backend::Scalar => $encaps(&self.bytes, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Scalar => $encaps_h(&self.bytes, &self.h, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::PairedSha3 => $encaps_paired_sha3(&self.bytes, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $encaps_h_avx2(&self.bytes, &self.h, m, &mut key, &mut ct, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx512 => {
                            $encaps_h_avx512(&self.bytes, &self.h, m, &mut key, &mut ct, scratch.as_mut_ptr())
                        }
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized. Wipe on both
                // success and failure before inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(
                        scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>(),
                    );
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
                let mut key = $DecapsulationKey {
                    seed: *seed,
                    ek: $EncapsulationKey {
                        bytes: [0; $ek],
                        #[cfg(target_arch = "x86_64")]
                        h: [0; 32],
                    },
                    dk: [0; $dk],
                };
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `seed`, `key.ek.bytes`, `key.dk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `backend()` chose an implementation
                // whose features the CPU has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $keygen(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::PairedSha3 => $keygen_paired_sha3(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $keygen_avx2(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx512 => $keygen_avx512(seed, &mut key.ek.bytes, &mut key.dk, scratch.as_mut_ptr()),
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized. Wipe on both
                // success and failure before inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(
                        scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>(),
                    );
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
                key.ek.h.copy_from_slice(&key.dk[$dk - 64..$dk - 32]);
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
                let mut key = [0u8; 32];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.dk`, `ct`, `key` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each
                // other or the stack, or wrap around the end of the address
                // space. `self.dk` was written by the key generation.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $decaps(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::PairedSha3 => $decaps_paired_sha3(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $decaps_avx2(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx512 => $decaps_avx512(&self.dk, ct, &mut key, scratch.as_mut_ptr()),
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized. Wipe on both
                // success and failure before inspecting the return status.
                unsafe {
                    $crate::zeroize::zeroize_raw(
                        scratch.as_mut_ptr().cast(), core::mem::size_of::<Scratch>(),
                    );
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
        mod sha3_variant_tests {
            use super::*;
            use $crate::mlkem_common::aarch64_tests::{array, vectors};

            // Exercise the retained single-state SHA-3 implementation against
            // published ACVP answers, independently of production dispatch.
            #[test]
            fn legacy_sha3_keygen_acvp() {
                if !$crate::cpu::detected().contains($keygen_sha3_features) {
                    return;
                }
                for v in vectors($name, None) {
                    let mut seed = [0; 64];
                    seed[..32].copy_from_slice(&array::<32>(&v["d"]));
                    seed[32..].copy_from_slice(&array::<32>(&v["z"]));
                    let mut ek = [0; $ek];
                    let mut dk = [0; $dk];
                    let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                    // SAFETY: CPU features were checked. All buffers have the
                    // generated function's sizes and are separate allocations.
                    assert_eq!(unsafe { $keygen_sha3(&seed, &mut ek, &mut dk, scratch.as_mut_ptr()) }, 1);
                    assert_eq!(ek, array::<$ek>(&v["ek"]));
                    assert_eq!(dk, array::<$dk>(&v["dk"]));
                    let key = $DecapsulationKey::from_seed(&seed).unwrap();
                    assert_eq!(key.encapsulation_key().as_bytes(), &ek);
                    assert_eq!(key.dk, dk);
                }
            }

            #[test]
            fn legacy_sha3_encapsulation_acvp() {
                if !$crate::cpu::detected().contains($encaps_sha3_features) {
                    return;
                }
                for v in vectors($name, Some("encapsulation")) {
                    let ek = array::<$ek>(&v["ek"]);
                    let m = array::<32>(&v["m"]);
                    let mut key = [0; 32];
                    let mut ct = [0; $ct];
                    let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                    // SAFETY: Features were checked; published valid key and
                    // distinct buffers meet the generated function's contract.
                    assert_eq!(unsafe { $encaps_sha3(&ek, &m, &mut key, &mut ct, scratch.as_mut_ptr()) }, 1);
                    assert_eq!(key, array::<32>(&v["k"]));
                    assert_eq!(ct, array::<$ct>(&v["c"]));
                    assert_eq!($EncapsulationKey::from_bytes(&ek).unwrap().encapsulate_internal(&m).unwrap(), (key, ct));
                }
            }

            #[test]
            fn legacy_sha3_decapsulation_acvp() {
                let features = $crate::cpu::detected();
                if !features.contains($decaps_sha3_features) || !features.contains($decaps_paired_sha3_features) {
                    return;
                }
                for v in vectors($name, Some("decapsulation")) {
                    let dk = array::<$dk>(&v["dk"]);
                    let ct = array::<$ct>(&v["c"]);
                    let mut key = [0; 32];
                    let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                    // SAFETY: Features were checked; the published valid
                    // expanded key and distinct buffers satisfy the contract.
                    assert_eq!(unsafe { $decaps_sha3(&dk, &ct, &mut key, scratch.as_mut_ptr()) }, 1);
                    assert_eq!(key, array::<32>(&v["k"]));
                    let mut paired_key = [0; 32];
                    // SAFETY: The complete paired feature set was checked;
                    // buffers satisfy the same verified input contract.
                    assert_eq!(unsafe { $decaps_paired_sha3(&dk, &ct, &mut paired_key, scratch.as_mut_ptr()) }, 1);
                    assert_eq!(paired_key, key);
                }
            }
        }
    };
}

pub(crate) use ml_kem;

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::Backend;
    use crate::cpu::Features;

    #[test]
    fn selects_complete_feature_sets() {
        let avx2 = Features::of(&["avx", "avx2"]);
        let avx512 = Features::of(&["avx", "avx2", "avx512f", "avx512vl"]);
        let sha3 = Features::of(&[]);
        assert_eq!(Backend::select(avx512, avx2, avx512, sha3), Backend::Avx512);
        for features in [
            avx2,
            Features::of(&["avx", "avx2", "avx512f"]),
            Features::of(&["avx", "avx2", "avx512vl"]),
        ] {
            assert_eq!(Backend::select(features, avx2, avx512, sha3), Backend::Avx2);
        }
        for features in [
            Features::of(&[]),
            Features::of(&["avx", "avx512f", "avx512vl"]),
        ] {
            assert_eq!(
                Backend::select(features, avx2, avx512, sha3),
                Backend::Scalar
            );
        }
    }
}

#[cfg(all(test, target_arch = "aarch64"))]
pub(crate) mod aarch64_tests {
    extern crate std;
    pub(crate) fn array<const N: usize>(value: &serde_json::Value) -> [u8; N] {
        let text = value.as_str().unwrap();
        assert_eq!(text.len(), 2 * N);
        core::array::from_fn(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).unwrap())
    }

    pub(crate) fn vectors(name: &str, function: Option<&str>) -> std::vec::Vec<serde_json::Value> {
        let text = if function.is_none() {
            include_str!("../vectors/nist-acvp/ML-KEM-keyGen-FIPS203/internalProjection.json")
        } else {
            include_str!("../vectors/nist-acvp/ML-KEM-encapDecap-FIPS203/internalProjection.json")
        };
        let file: serde_json::Value = serde_json::from_str(text).unwrap();
        let selected: std::vec::Vec<_> = file["testGroups"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|g| {
                g["parameterSet"].as_str() == Some(name) && g["function"].as_str() == function
            })
            .flat_map(|g| g["tests"].as_array().unwrap().iter().cloned())
            .collect();
        assert!(
            !selected.is_empty(),
            "missing ACVP vectors for {name} {function:?}"
        );
        selected
    }

    use super::Backend;
    use crate::cpu::Features;

    #[test]
    fn selects_complete_feature_sets() {
        let empty = Features::of(&[]);
        let required = Features::of(&["neon", "sha3"]);
        assert_eq!(
            Backend::select(required, empty, empty, required),
            Backend::PairedSha3
        );
        for available in [empty, Features::of(&["neon"]), Features::of(&["sha3"])] {
            assert_eq!(
                Backend::select(available, empty, empty, required),
                Backend::Scalar
            );
        }
    }
}
