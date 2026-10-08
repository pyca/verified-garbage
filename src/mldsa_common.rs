//! What ML-DSA-44, ML-DSA-65 and ML-DSA-87 (`crate::mldsa44`,
//! `crate::mldsa65`, `crate::mldsa87`) share: their API, defined once by
//! `ml_dsa!` for each parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm"
))]

/// The implementations of ML-DSA's verified functions: their instances for
/// the polynomial arithmetic and Keccak they call (`Generic/MlDsaArith/` and
/// their accelerated Keccak implementation).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The target's baseline ISA (on x86-64, SSE2 polynomial arithmetic),
    /// with scalar Keccak.
    Scalar,
    /// AArch64 with the SHA-3 extension, for Keccak.
    #[cfg(target_arch = "aarch64")]
    Sha3,
    /// x86-64 with AVX2, for the polynomial arithmetic.
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

impl Backend {
    /// Select independently of standalone hashing: paired ML-DSA sampling has
    /// different performance characteristics from a single Keccak stream.
    #[cfg_attr(not(any(target_arch = "x86_64", target_arch = "aarch64")), allow(unused_variables))]
    pub(crate) fn select(f: crate::cpu::Features, required: crate::cpu::Features) -> Backend {
        #[cfg(target_arch = "aarch64")]
        if f.contains(required) {
            return Backend::Sha3;
        }
        #[cfg(target_arch = "x86_64")]
        if f.contains(required) {
            return Backend::Avx2;
        }
        Backend::Scalar
    }
}

/// Defines the API of one ML-DSA parameter set: its `Error`, `SigningKey`
/// and `VerifyingKey`, over its verified `keygen`, `sign_message` and
/// `verify_message` functions, its `sign` and `verify` functions (which take
/// `μ`, for known-answer tests) and its sizes.
macro_rules! ml_dsa {
    (
        name: $name:literal,
        signing_key: $SigningKey:ident,
        verifying_key: $VerifyingKey:ident,
        keygen: $keygen:path,
        sign: $sign:path,
        verify: $verify:path,
        sign_message: $sign_message:path,
        verify_message: $verify_message:path,
        keygen_sha3: ($keygen_sha3:path, $keygen_sha3_features:path),
        sign_sha3: ($sign_sha3:path, $sign_sha3_features:path),
        verify_sha3: ($verify_sha3:path, $verify_sha3_features:path),
        sign_message_sha3: ($sign_message_sha3:path, $sign_message_sha3_features:path),
        verify_message_cached_sha3: ($verify_message_cached_sha3:path, $verify_message_cached_sha3_features:path),
        keygen_avx2: ($keygen_avx2:path, $keygen_avx2_features:path),
        sign_avx2: ($sign_avx2:path, $sign_avx2_features:path),
        verify_avx2: ($verify_avx2:path, $verify_avx2_features:path),
        sign_message_avx2: ($sign_message_avx2:path, $sign_message_avx2_features:path),
        verify_message_avx2: ($verify_message_avx2:path, $verify_message_avx2_features:path),
        pk: $pk:literal,
        sk: $sk:literal,
        sig: $sig:literal,
        scratch: $scratch:literal,
        message_scratch: $message_scratch:literal $(,)?
    ) => {
        use $crate::zeroize::zeroize;
        use $crate::mldsa_common::Backend;

        /// Select from the generated requirements of every accelerated caller.
        fn backend() -> Backend {
            #[cfg(target_arch = "aarch64")]
            const REQUIRED: &[$crate::cpu::Features] = &[
                $keygen_sha3_features,
                $sign_sha3_features,
                $verify_sha3_features,
                $sign_message_sha3_features,
                $verify_message_cached_sha3_features,
            ];
            #[cfg(target_arch = "x86_64")]
            const REQUIRED: &[$crate::cpu::Features] = &[
                $keygen_avx2_features,
                $sign_avx2_features,
                $verify_avx2_features,
                $sign_message_avx2_features,
                $verify_message_avx2_features,
            ];
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            const REQUIRED: &[$crate::cpu::Features] = &[];
            Backend::select(
                $crate::cpu::detected(),
                const { $crate::cpu::Features::all(REQUIRED) },
            )
        }

        /// Why an operation failed.
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Error {
            /// A loop reached its bound (FIPS 204 Appendix C), which happens
            /// with probability about 2⁻²⁵⁶ or less.
            LoopBound,
            /// The context string is longer than 255 bytes (FIPS 204
            /// Algorithms 2 and 3).
            ContextTooLong,
            /// The signature is not valid.
            InvalidSignature,
            /// The operating system's random number generator failed.
            Randomness,
        }

        /// The working space of the assembly functions on `μ`.
        type Scratch = [u64; $scratch];

        /// The working space of the assembly functions on messages.
        type MessageScratch = [u64; $message_scratch];

        #[doc = concat!("An ", $name, " public key.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $VerifyingKey {
            bytes: [u8; $pk],
            // Constructors maintain tr = SHAKE256(bytes, 64).
            #[cfg(target_arch = "aarch64")]
            tr: [u8; 64],
        }

        impl core::fmt::Debug for $VerifyingKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($VerifyingKey)).finish_non_exhaustive()
            }
        }

        impl $VerifyingKey {
            /// The size of a public key, in bytes.
            pub const SIZE: usize = $pk;
            /// The size of a signature, in bytes.
            pub const SIGNATURE_SIZE: usize = $sig;

            /// The public key `bytes` (every byte string of this size is
            /// one).
            pub fn from_bytes(bytes: &[u8; $pk]) -> Self {
                $VerifyingKey {
                    bytes: *bytes,
                    #[cfg(target_arch = "aarch64")]
                    tr: {
                        let mut tr = [0; 64];
                        $crate::hashes::sha3::Shake256::digest(bytes, &mut tr);
                        tr
                    },
                }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $pk] {
                &self.bytes
            }

            /// `ML-DSA.Verify(pk, M, σ, ctx)` (FIPS 204 Algorithm 3):
            /// whether `sig` is a valid signature of the message `msg` with
            /// the context string `ctx`. Fails with
            /// [`Error::InvalidSignature`] if it is not (or, with probability
            /// about 2⁻²⁵⁶ or less, if a loop reaches its bound), and
            /// [`Error::ContextTooLong`] if `ctx` is longer than 255 bytes.
            pub fn verify(&self, msg: &[u8], ctx: &[u8], sig: &[u8; $sig]) -> Result<(), Error> {
                let mut scratch: MessageScratch = [0; $message_scratch];
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.bytes`, `sig` and `scratch` are valid for
                // reads (and, for `scratch`, writes) of their sizes, and
                // `msg` and `ctx` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // Backend selection checks the generated CPU feature requirements.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $verify_message(&self.bytes, m, m_len, c, c_len, sig, &mut scratch),
                        #[cfg(target_arch = "aarch64")]
                        // Both constructors establish tr = SHAKE256(bytes, 64);
                        // the key and digest remain private and immutable.
                        Backend::Sha3 => $verify_message_cached_sha3(&self.bytes, m, m_len, c, c_len, sig, &mut scratch, &self.tr),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_message_avx2(&self.bytes, m, m_len, c, c_len, sig, &mut scratch),
                    }
                };
                match r {
                    1 => Ok(()),
                    2 => Err(Error::ContextTooLong),
                    _ => Err(Error::InvalidSignature),
                }
            }

            /// `ML-DSA.Verify_internal` (FIPS 204 Algorithm 8) with the
            /// message representative `mu` = `μ` given: for known-answer
            /// tests.
            #[doc(hidden)]
            pub fn verify_internal(&self, mu: &[u8; 64], sig: &[u8; $sig]) -> Result<(), Error> {
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.bytes`, `mu`, `sig` and `scratch` are valid
                // for reads (and, for `scratch`, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $verify(&self.bytes, mu, sig, &mut scratch),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $verify_sha3(&self.bytes, mu, sig, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_avx2(&self.bytes, mu, sig, &mut scratch),
                    }
                };
                if r == 1 { Ok(()) } else { Err(Error::InvalidSignature) }
            }
        }

        #[doc = concat!(
            "An ", $name, " private key, kept as the 32-byte seed `ξ` it is generated from \
            (FIPS 204 §3.6.3), with the keys it expands to. The seed and the expanded key are \
            destroyed when it is dropped."
        )]
        pub struct $SigningKey {
            seed: [u8; 32],
            vk: $VerifyingKey,
            sk: [u8; $sk],
        }

        impl core::fmt::Debug for $SigningKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($SigningKey)).finish_non_exhaustive()
            }
        }

        impl Drop for $SigningKey {
            fn drop(&mut self) {
                zeroize(&mut self.seed);
                zeroize(&mut self.sk);
            }
        }

        impl $SigningKey {
            /// The size of a seed, in bytes.
            pub const SEED_SIZE: usize = 32;

            /// The key pair of the seed `ξ`: `ML-DSA.KeyGen_internal(ξ)`
            /// (FIPS 204 Algorithm 6). The seed must be 32 random bytes from
            /// an approved RBG (FIPS 204 §3.6.1, Algorithm 1), or a seed so
            /// generated before.
            pub fn from_seed(seed: &[u8; 32]) -> Result<Self, Error> {
                let mut key = $SigningKey {
                    seed: *seed,
                    vk: $VerifyingKey {
                        bytes: [0; $pk],
                        #[cfg(target_arch = "aarch64")]
                        tr: [0; 64],
                    },
                    sk: [0; $sk],
                };
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `seed`, `key.vk.bytes`, `key.sk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `seed` is the caller's seed.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $keygen(seed, &mut key.vk.bytes, &mut key.sk, &mut scratch),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $keygen_sha3(seed, &mut key.vk.bytes, &mut key.sk, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $keygen_avx2(seed, &mut key.vk.bytes, &mut key.sk, &mut scratch),
                    }
                };
                zeroize(&mut scratch);
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less; dropping `key` destroys it.
                    // NO-COVERAGE-START
                    return Err(Error::LoopBound);
                    // NO-COVERAGE-END
                }
                // keyGenInternal encodes SHAKE256(pk, 64) at sk[64..128].
                // Initialize the cache only after successful key generation.
                #[cfg(target_arch = "aarch64")]
                key.vk.tr.copy_from_slice(&key.sk[64..128]);
                Ok(key)
            }

            /// The seed `ξ`.
            pub fn seed(&self) -> &[u8; 32] {
                &self.seed
            }

            /// The public key.
            pub fn verifying_key(&self) -> &$VerifyingKey {
                &self.vk
            }

            /// `ML-DSA.Sign(sk, M, ctx)` (FIPS 204 Algorithm 2), hedged: a
            /// signature of the message `msg` with the context string `ctx`,
            /// with 32 bytes of randomness from the operating system. Fails
            /// with [`Error::ContextTooLong`] if `ctx` is longer than 255
            /// bytes.
            pub fn sign(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], Error> {
                let mut rnd = [0u8; 32];
                if getrandom::fill(&mut rnd).is_err() {
                    // The operating system's generator does not fail in the
                    // tests.
                    // NO-COVERAGE-START
                    return Err(Error::Randomness);
                    // NO-COVERAGE-END
                }
                let r = self.sign_with(msg, ctx, &rnd);
                zeroize(&mut rnd);
                r
            }

            /// The deterministic variant of `ML-DSA.Sign(sk, M, ctx)` (FIPS
            /// 204 Algorithm 2, with `rnd` = 32 zero bytes). FIPS 204 §3.4
            /// recommends the hedged [`sign`](Self::sign) where side channels
            /// are a concern.
            pub fn sign_deterministic(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], Error> {
                self.sign_with(msg, ctx, &[0; 32])
            }

            fn sign_with(&self, msg: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Result<[u8; $sig], Error> {
                let mut sig = [0u8; $sig];
                let mut scratch: MessageScratch = [0; $message_scratch];
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.sk`, `rnd`, `sig` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes, and
                // `msg` and `ctx` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // `self.sk` was written by the key generation.
                // Backend selection checks the generated CPU feature requirements.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => {
                            $sign_message(&self.sk, m, m_len, c, c_len, rnd, &mut sig, &mut scratch)
                        }
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => {
                            $sign_message_sha3(&self.sk, m, m_len, c, c_len, rnd, &mut sig, &mut scratch)
                        }
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => {
                            $sign_message_avx2(&self.sk, m, m_len, c, c_len, rnd, &mut sig, &mut scratch)
                        }
                    }
                };
                zeroize(&mut scratch);
                match r {
                    1 => Ok(sig),
                    2 => Err(Error::ContextTooLong),
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    _ => {
                        zeroize(&mut sig);
                        Err(Error::LoopBound)
                    }
                    // NO-COVERAGE-END
                }
            }

            /// `ML-DSA.Sign_internal` (FIPS 204 Algorithm 7) with the
            /// message representative `mu` = `μ` and the randomness `rnd`
            /// given: for known-answer tests only. `rnd` must otherwise be
            /// fresh random bytes, which [`sign`](Self::sign) draws.
            #[doc(hidden)]
            pub fn sign_internal(&self, mu: &[u8; 64], rnd: &[u8; 32]) -> Result<[u8; $sig], Error> {
                let mut sig = [0u8; $sig];
                let mut scratch: Scratch = [0; $scratch];
                // SAFETY: `self.sk`, `mu`, `rnd`, `sig` and `scratch` are
                // valid for reads (and, for the last two, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `self.sk` was written by the key
                // generation.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $sign(&self.sk, mu, rnd, &mut sig, &mut scratch),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $sign_sha3(&self.sk, mu, rnd, &mut sig, &mut scratch),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $sign_avx2(&self.sk, mu, rnd, &mut sig, &mut scratch),
                    }
                };
                zeroize(&mut scratch);
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    zeroize(&mut sig);
                    return Err(Error::LoopBound);
                    // NO-COVERAGE-END
                }
                Ok(sig)
            }
        }
    };
}

pub(crate) use ml_dsa;

#[cfg(all(test, target_arch = "aarch64"))]
#[path = "mldsa_fused_tests.rs"]
mod fused_tests;

#[cfg(test)]
mod tests {
    use crate::mldsa44::{Error, SigningKey44};

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn accelerated_dispatch_requires_all_features() {
        use super::Backend;
        use crate::cpu::Features;
        let required = Features::of(&["sha3", "sha2"]);
        assert_eq!(Backend::select(Features::of(&[]), required), Backend::Scalar);
        assert_eq!(Backend::select(Features::of(&["sha3"]), required), Backend::Scalar);
        assert_eq!(Backend::select(required, required), Backend::Sha3);
    }


    #[cfg(target_arch = "aarch64")]
    #[test]
    fn fused_dots_match_canonical_reference() {
        use crate::arch::mldsa::{vg_mldsa_dot_inverse4, vg_mldsa_dot_inverse5,
            vg_mldsa_dot_inverse7, vg_mldsa_inv_ntt};
        const Q: u32 = 8_380_417;
        fn check<const N: usize>(kernel: unsafe extern "C" fn(
            *mut [u32; 256], *const [u32; N], *const [u32; N], *mut [u64; 128])) {
            for case in 0..4 {
                let a: [u32; N] = core::array::from_fn(|i| match case {
                    0 => 0,
                    1 => 3 * Q - 1,
                    2 => if i % 2 == 0 { Q } else { 2 * Q - 1 },
                    _ => ((i as u64 * 1_103_515_245 + 12_345) % u64::from(3 * Q)) as u32,
                });
                let b: [u32; N] = core::array::from_fn(|i| match case {
                    0 => 3 * Q - 1,
                    1 => 3 * Q - 1,
                    2 => if i % 3 == 0 { 0 } else { 3 * Q - 1 },
                    _ => ((i as u64 * 2_654_435_761 + 91) % u64::from(3 * Q)) as u32,
                });
                let before_a = a;
                let before_b = b;
                let mut reference: [u32; 256] = core::array::from_fn(|i| {
                    let sum: u64 = (0..N / 256).map(|j|
                        u64::from(a[j * 256 + i] % Q) * u64::from(b[j * 256 + i] % Q)).sum();
                    (sum % u64::from(Q)) as u32
                });
                let mut scratch = [0u64; 128];
                let mut output = [u32::MAX; 256];
                // SAFETY: independent correctly sized buffers; reference is canonical,
                // fused inputs are below 3q; kernels use baseline AArch64 instructions.
                unsafe {
                    vg_mldsa_inv_ntt(&mut reference, &mut scratch);
                    kernel(&mut output, &a, &b, &mut scratch);
                }
                assert_eq!(output, reference, "count={} case={case}", N / 256);
                assert!(output.iter().all(|&x| x < Q));
                assert_eq!(a, before_a);
                assert_eq!(b, before_b);
            }
        }
        check(vg_mldsa_dot_inverse4);
        check(vg_mldsa_dot_inverse5);
        check(vg_mldsa_dot_inverse7);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn optimized_transforms_match_canonical_reference() {
        use crate::arch::mldsa::{
            vg_mldsa_montgomery_inv_ntt, vg_mldsa_ntt,
            vg_mldsa_ntt_positive, vg_mldsa_ntt_positive_from,
        };
        const Q: u32 = 8_380_417;
        const R: u64 = 4_193_792;
        for case in 0..4 {
            let input = core::array::from_fn(|i| match case {
                0 => 0,
                1 => Q - 1,
                2 => if i % 2 == 0 { 0 } else { Q - 1 },
                _ => ((i as u64 * 1_103_515_245 + 12_345) % u64::from(Q)) as u32,
            });
            let mut reference = input;
            let mut positive = input;
            let mut separate = [u32::MAX; 256];
            let mut scratch = [0u64; 128];
            // SAFETY: canonical inputs, separate correctly sized buffers,
            // and AArch64 baseline instructions only.
            unsafe {
                vg_mldsa_ntt(&mut reference, &mut scratch);
                vg_mldsa_ntt_positive(&mut positive);
                vg_mldsa_ntt_positive_from(&mut separate, &input);
            }
            assert_eq!(positive, separate);
            for i in 0..256 {
                assert!(positive[i] < 3 * Q);
                assert_eq!(positive[i] % Q, reference[i]);
            }
            // SAFETY: the reference transform produces canonical coefficients.
            unsafe { vg_mldsa_montgomery_inv_ntt(&mut reference, &mut scratch) };
            for i in 0..256 {
                assert_eq!(reference[i], (u64::from(input[i]) * R % u64::from(Q)) as u32);
            }
        }
    }

    // Compare both key constructors with the original raw-key entry. In
    // SHA3-enabled test runs the wrapper takes the cached-digest path.
    macro_rules! cached_verification_matches_raw {
        ($test:ident, $module:ident, $signing:ident, $verifying:ident, $raw:ident, $scratch:literal) => {
            #[test]
            fn $test() {
                use crate::$module::{Error, $signing, $verifying};
                for seed in 0..4 {
                    let key = $signing::from_seed(&[seed; 32]).unwrap();
                    let imported = $verifying::from_bytes(key.verifying_key().as_bytes());
                    assert_eq!(&imported, key.verifying_key());
                    for ctx in [&[][..], &[3; 255][..]] {
                        let msg = [seed; 137];
                        let sig = key.sign_deterministic(&msg, ctx).unwrap();
                        for vk in [key.verifying_key(), &imported, &imported.clone()] {
                            for corrupt in [false, true] {
                                let mut candidate = sig;
                                if corrupt { candidate[0] ^= 1; }
                                let mut scratch = [0u64; $scratch];
                                // SAFETY: valid, nonoverlapping buffers with the
                                // exact generated sizes; the scalar entry needs
                                // no optional CPU features.
                                let raw = unsafe {
                                    crate::arch::$module::$raw(vk.as_bytes(), msg.as_ptr(), msg.len(),
                                        ctx.as_ptr(), ctx.len(), &candidate, &mut scratch)
                                };
                                let expected = if raw == 1 { Ok(()) } else { Err(Error::InvalidSignature) };
                                assert_eq!(vk.verify(&msg, ctx, &candidate), expected);
                            }
                        }
                    }
                }
            }
        };
    }

    cached_verification_matches_raw!(cached44_matches_raw, mldsa44, SigningKey44, VerifyingKey44,
        vg_mldsa44_verify_message, 9856);
    cached_verification_matches_raw!(cached65_matches_raw, mldsa65, SigningKey65, VerifyingKey65,
        vg_mldsa65_verify_message, 13056);
    cached_verification_matches_raw!(cached87_matches_raw, mldsa87, SigningKey87, VerifyingKey87,
        vg_mldsa87_verify_message, 18176);

    #[test]
    fn context_too_long() {
        let key = SigningKey44::from_seed(&[7; 32]).unwrap();
        let sig = key.sign_deterministic(b"msg", &[0; 255]).unwrap();
        let vk = key.verifying_key();
        assert_eq!(vk.verify(b"msg", &[0; 255], &sig), Ok(()));
        assert_eq!(key.sign(b"msg", &[0; 256]), Err(Error::ContextTooLong));
        assert_eq!(
            vk.verify(b"msg", &[0; 256], &sig),
            Err(Error::ContextTooLong)
        );
    }
}
