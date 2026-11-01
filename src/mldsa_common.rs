//! What ML-DSA-44, ML-DSA-65 and ML-DSA-87 (`crate::mldsa44`,
//! `crate::mldsa65`, `crate::mldsa87`) share: their API, defined once by
//! `ml_dsa!` for each parameter set's verified functions and sizes.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

/// The implementations of ML-DSA's verified functions: each variant but
/// `Scalar` is the one with its suffix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    /// The baseline implementation.
    Scalar,
    /// `_sha3`.
    #[cfg(target_arch = "aarch64")]
    Sha3,
    /// `_avx2`.
    #[cfg(target_arch = "x86_64")]
    Avx2,
}

impl Backend {
    /// Chosen by the features `required` of ML-DSA's own variants, not with
    /// `crate::hashes::sha3::Backend`: their speed is not the standalone
    /// hash functions'.
    #[cfg_attr(
        not(any(target_arch = "x86_64", target_arch = "aarch64")),
        allow(unused_variables)
    )]
    pub(crate) fn select(
        f: verified_garbage_cpu::Features,
        required: verified_garbage_cpu::Features,
    ) -> Backend {
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
/// `verify_message` functions (on x86-64 and AArch64, `verify_message_cached`,
/// which takes the hash `tr` of the public key the `VerifyingKey` keeps), its
/// `sign` and `verify` functions (which take a precomputed `μ`)
/// and its sizes.
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
        verify_message_cached: $verify_message_cached:path,
        keygen_sha3: ($keygen_sha3:path, $keygen_sha3_features:path),
        sign_sha3: ($sign_sha3:path, $sign_sha3_features:path),
        verify_sha3: ($verify_sha3:path, $verify_sha3_features:path),
        sign_message_sha3: ($sign_message_sha3:path, $sign_message_sha3_features:path),
        verify_message_cached_sha3: ($verify_message_cached_sha3:path, $verify_message_cached_sha3_features:path),
        keygen_avx2: ($keygen_avx2:path, $keygen_avx2_features:path),
        sign_avx2: ($sign_avx2:path, $sign_avx2_features:path),
        verify_avx2: ($verify_avx2:path, $verify_avx2_features:path),
        sign_message_avx2: ($sign_message_avx2:path, $sign_message_avx2_features:path),
        verify_message_cached_avx2: ($verify_message_cached_avx2:path, $verify_message_cached_avx2_features:path),
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
            const REQUIRED: &[verified_garbage_cpu::Features] = &[
                $keygen_sha3_features,
                $sign_sha3_features,
                $verify_sha3_features,
                $sign_message_sha3_features,
                $verify_message_cached_sha3_features,
            ];
            #[cfg(target_arch = "x86_64")]
            const REQUIRED: &[verified_garbage_cpu::Features] = &[
                $keygen_avx2_features,
                $sign_avx2_features,
                $verify_avx2_features,
                $sign_message_avx2_features,
                $verify_message_cached_avx2_features,
            ];
            #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
            const REQUIRED: &[verified_garbage_cpu::Features] = &[];
            Backend::select(
                $crate::cpu::detected(),
                const { verified_garbage_cpu::Features::all(REQUIRED) },
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

        $crate::error::impl_error! {
            Error {
                LoopBound => concat!($name, " loop reached its bound"),
                ContextTooLong => concat!($name, " context is longer than 255 bytes"),
                InvalidSignature => concat!("invalid ", $name, " signature"),
                Randomness => concat!($name, " random number generator failed"),
            }
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
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
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
                    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
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
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<MessageScratch>::uninit();
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.bytes`, `sig` and `scratch` are valid for
                // reads (and, for `scratch`, writes) of their sizes, and
                // `msg` and `ctx` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // Backend selection checks the generated CPU feature requirements.
                let r = unsafe {
                    match backend() {
                        #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
                        Backend::Scalar => $verify_message(&self.bytes, m, m_len, c, c_len, sig, scratch.as_mut_ptr()),
                        // Both constructors establish tr = SHAKE256(bytes, 64);
                        // the key and digest remain private and immutable.
                        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
                        Backend::Scalar => $verify_message_cached(&self.bytes, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $verify_message_cached_sha3(&self.bytes, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_message_cached_avx2(&self.bytes, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr),
                    }
                };
                match r {
                    1 => Ok(()),
                    2 => Err(Error::ContextTooLong),
                    _ => Err(Error::InvalidSignature),
                }
            }

            /// Verify a signature of the 64-byte message representative `mu`
            /// using FIPS 204 Algorithm 8, with `μ` already computed.
            /// For pure ML-DSA, compute `mu = SHAKE256(tr || 0x00 ||
            /// len(ctx) || ctx || msg, 64)`, where `tr = SHAKE256(pk, 64)`
            /// and `len(ctx)` is one byte (at most 255). This method does
            /// not hash the message or apply context formatting.
            /// Returns [`Error::InvalidSignature`] if verification fails.
            pub fn verify_mu(&self, mu: &[u8; 64], sig: &[u8; $sig]) -> Result<(), Error> {
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `self.bytes`, `mu`, `sig` and `scratch` are valid
                // for reads (and, for `scratch`, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $verify(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $verify_sha3(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_avx2(&self.bytes, mu, sig, scratch.as_mut_ptr()),
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
                        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
                        tr: [0; 64],
                    },
                    sk: [0; $sk],
                };
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
                // SAFETY: `seed`, `key.vk.bytes`, `key.sk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `seed` is the caller's seed.
                // `backend()` chose an implementation whose features the CPU
                // has.
                let r = unsafe {
                    match backend() {
                        Backend::Scalar => $keygen(seed, &mut key.vk.bytes, &mut key.sk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $keygen_sha3(seed, &mut key.vk.bytes, &mut key.sk, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $keygen_avx2(seed, &mut key.vk.bytes, &mut key.sk, scratch.as_mut_ptr()),
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                unsafe { $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of_val(&scratch)) };
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less; dropping `key` destroys it.
                    // NO-COVERAGE-START
                    return Err(Error::LoopBound);
                    // NO-COVERAGE-END
                }
                // keyGenInternal encodes SHAKE256(pk, 64) at sk[64..128].
                // Initialize the cache only after successful key generation.
                #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
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
                getrandom::fill(&mut rnd).map_err(|_| Error::Randomness)?;
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
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<MessageScratch>::uninit();
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
                            $sign_message(&self.sk, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr())
                        }
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => {
                            $sign_message_sha3(&self.sk, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr())
                        }
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => {
                            $sign_message_avx2(&self.sk, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr())
                        }
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                unsafe { $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of_val(&scratch)) };
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

            /// Sign the 64-byte message representative `mu` using FIPS 204
            /// Algorithm 7, with `μ` already computed. For pure ML-DSA,
            /// compute `mu = SHAKE256(tr || 0x00 || len(ctx) || ctx || msg, 64)`,
            /// where `tr = SHAKE256(pk, 64)` and `len(ctx)` is one byte
            /// (at most 255). This method does not hash the message or
            /// apply context formatting.
            ///
            /// Supply 32 fresh random bytes from an approved RBG as `rnd`
            /// for hedged signing, or all zeros for deterministic signing.
            /// FIPS 204 §3.4 recommends hedged signing where side channels
            /// are a concern. Returns [`Error::LoopBound`] if a loop reaches
            /// its bound.
            pub fn sign_mu(&self, mu: &[u8; 64], rnd: &[u8; 32]) -> Result<[u8; $sig], Error> {
                let mut sig = [0u8; $sig];
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = core::mem::MaybeUninit::<Scratch>::uninit();
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
                        Backend::Scalar => $sign(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $sign_sha3(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $sign_avx2(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                    }
                };
                // SAFETY: the entire scratch allocation is writable, including
                // bytes the operation may not have initialized.
                unsafe { $crate::zeroize::zeroize_raw(scratch.as_mut_ptr().cast(), core::mem::size_of_val(&scratch)) };
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

#[cfg(test)]
mod tests {
    use crate::mldsa44::{Error, SigningKey44};

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn accelerated_dispatch_requires_all_features() {
        use super::Backend;
        use verified_garbage_cpu::{Features, feature};
        let required = Features(feature::SHA3 | feature::SHA2);
        assert_eq!(Backend::select(Features(0), required), Backend::Scalar);
        assert_eq!(
            Backend::select(Features(feature::SHA3), required),
            Backend::Scalar
        );
        assert_eq!(Backend::select(required, required), Backend::Sha3);
    }

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
