//! What ML-DSA-44, ML-DSA-65 and ML-DSA-87 share: their API, defined once by
//! `ml_dsa!`.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

/// Defines the API of one ML-DSA parameter set: its `SigningKey` and
/// `VerifyingKey`, whose functions fail with `crate::error::MlDsaError`,
/// over the dispatchers (`_auto`, which run the best implementation the CPU
/// supports) of its verified `keygen`, `sign_message` and
/// `verify_message_cached` functions (which takes the hash `tr` of the public key the
/// `VerifyingKey` keeps, from `keygen` or from `pk_tr`), its `sign` and
/// `verify` functions (which take a precomputed `μ`) and its sizes; and its
/// `PreparedSigningKey` and `PreparedVerifyingKey`, which on AArch64, 32-bit
/// ARM, x86-64, x86, RISC-V and PPC64LE keep the prepared key that
/// `prepare_sign` and `prepare_verify` write and sign and verify with it
/// (`sign_message_prepared`, `verify_message_prepared`), and elsewhere sign
/// and verify as the keys they were prepared from do.
macro_rules! ml_dsa {
    (
        name: $name:literal,
        signing_key: $SigningKey:ident,
        verifying_key: $VerifyingKey:ident,
        prepared_signing_key: $PreparedSigningKey:ident,
        prepared_verifying_key: $PreparedVerifyingKey:ident,
        keygen: $keygen:path,
        sign: $sign:path,
        verify: $verify:path,
        sign_message: $sign_message:path,
        verify_message_cached: $verify_message_cached:path,
        pk_tr: $pk_tr:path,
        prepare_sign: $prepare_sign:path,
        prepare_verify: $prepare_verify:path,
        sign_message_prepared: $sign_message_prepared:path,
        verify_message_prepared: $verify_message_prepared:path,
        pk: $pk:literal,
        sk: $sk:literal,
        sig: $sig:literal,
        prepared_sk: $prepared_sk:literal,
        prepared_pk: $prepared_pk:literal,
        scratch: $scratch:literal,
        message_scratch: $message_scratch:literal $(,)?
    ) => {
        use $crate::zeroize::zeroize;
        use $crate::error::{InvalidSignature, MlDsaError};

        /// The working space of the assembly functions on `μ`.
        type Scratch = [u64; $scratch];

        /// The working space of the assembly functions on messages.
        type MessageScratch = [u64; $message_scratch];

        #[doc = concat!("An ", $name, " public key.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct $VerifyingKey {
            bytes: [u8; $pk],
            // Constructors maintain tr = H(bytes, 64), from the verified
            // `pk_tr` or `keygen`.
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
                let dit = $crate::dit::public($crate::dit::Why::PublicKey);
                let mut tr = [0; 64];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                // SAFETY: `bytes`, `tr` and `scratch` are valid for reads
                // (and, for `tr` and `scratch`, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                // The dispatcher calls only an implementation the CPU has the
                // features of. `pk_tr` writes `tr = H(bytes, 64)`
                // (`VG.Spec.MlDsa.pkTrContract`), which
                // `verify_message_cached` requires.
                unsafe {
                    $pk_tr(dit, bytes, &mut tr, scratch.0.as_mut_ptr())
                }
                $VerifyingKey { bytes: *bytes, tr }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; $pk] {
                &self.bytes
            }

            /// `ML-DSA.Verify(pk, M, σ, ctx)` (FIPS 204 Algorithm 3):
            /// whether `sig` is a valid signature of the message `msg` with
            /// the context string `ctx`. Fails with [`InvalidSignature`] if
            /// it is not (or, with probability about 2⁻²⁵⁶ or less, if a loop
            /// reaches its bound), or if `ctx` is longer than 255 bytes, for
            /// which nothing is a valid signature (Algorithm 3 returns an
            /// error).
            pub fn verify(&self, msg: &[u8], ctx: &[u8], sig: &[u8; $sig]) -> Result<(), InvalidSignature> {
                let dit = $crate::dit::public($crate::dit::Why::Verify);
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<MessageScratch>::uninit());
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.bytes`, `sig` and `scratch` are valid for
                // reads (and, for `scratch`, writes) of their sizes, and
                // `msg` and `ctx` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    $verify_message_cached(dit, &self.bytes, m, m_len, c, c_len, sig, scratch.0.as_mut_ptr(), &self.tr)
                };
                // 2 is a context longer than 255 bytes.
                if r == 1 { Ok(()) } else { Err(InvalidSignature) }
            }

            /// Verify a signature of the 64-byte message representative `mu`
            /// using FIPS 204 Algorithm 8, with `μ` already computed.
            /// For pure ML-DSA, compute `mu = SHAKE256(tr || 0x00 ||
            /// len(ctx) || ctx || msg, 64)`, where `tr = SHAKE256(pk, 64)`
            /// and `len(ctx)` is one byte (at most 255). This method does
            /// not hash the message or apply context formatting.
            /// Returns [`InvalidSignature`] if verification fails.
            pub fn verify_mu(&self, mu: &[u8; 64], sig: &[u8; $sig]) -> Result<(), InvalidSignature> {
                let dit = $crate::dit::public($crate::dit::Why::Verify);
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                // SAFETY: `self.bytes`, `mu`, `sig` and `scratch` are valid
                // for reads (and, for `scratch`, writes) of their sizes; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    $verify(dit, &self.bytes, mu, sig, scratch.0.as_mut_ptr())
                };
                if r == 1 { Ok(()) } else { Err(InvalidSignature) }
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
            pub fn from_seed(seed: &[u8; 32]) -> Result<Self, MlDsaError> {
                $crate::dit::enter!(dit);
                let mut key = $SigningKey {
                    seed: *seed,
                    vk: $VerifyingKey {
                        bytes: [0; $pk],
                        tr: [0; 64],
                    },
                    sk: [0; $sk],
                };
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                // SAFETY: `seed`, `key.vk.bytes`, `key.sk` and `scratch` are
                // valid for reads (and, for the last three, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `seed` is the caller's seed.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    $keygen(dit, seed, &mut key.vk.bytes, &mut key.sk, scratch.0.as_mut_ptr())
                };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less; dropping `key` destroys it.
                    // NO-COVERAGE-START
                    return Err(MlDsaError::LoopBound);
                    // NO-COVERAGE-END
                }
                // keyGenInternal encodes SHAKE256(pk, 64) at sk[64..128]
                // (`VG.Spec.MlDsa.keyGenInternal_tr`).
                // Initialize the cache only after successful key generation.
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
            /// with [`MlDsaError::ContextTooLong`] if `ctx` is longer than 255
            /// bytes.
            pub fn sign(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], MlDsaError> {
                let mut rnd = [0u8; 32];
                getrandom::fill(&mut rnd).map_err(|_| MlDsaError::Randomness)?;
                let r = self.sign_with(msg, ctx, &rnd);
                zeroize(&mut rnd);
                r
            }

            /// The deterministic variant of `ML-DSA.Sign(sk, M, ctx)` (FIPS
            /// 204 Algorithm 2, with `rnd` = 32 zero bytes). FIPS 204 §3.4
            /// recommends the hedged [`sign`](Self::sign) where side channels
            /// are a concern.
            pub fn sign_deterministic(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], MlDsaError> {
                self.sign_with(msg, ctx, &[0; 32])
            }

            fn sign_with(&self, msg: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Result<[u8; $sig], MlDsaError> {
                $crate::dit::enter!(dit);
                let mut sig = [0u8; $sig];
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<MessageScratch>::uninit());
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.sk`, `rnd`, `sig` and `scratch` are valid for
                // reads (and, for the last two, writes) of their sizes, and
                // `msg` and `ctx` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // `self.sk` was written by the key generation.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    $sign_message(dit, &self.sk, m, m_len, c, c_len, rnd, &mut sig, scratch.0.as_mut_ptr())
                };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                match r {
                    1 => Ok(sig),
                    2 => Err(MlDsaError::ContextTooLong),
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    _ => {
                        zeroize(&mut sig);
                        Err(MlDsaError::LoopBound)
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
            /// are a concern. Returns [`MlDsaError::LoopBound`] if a loop
            /// reaches its bound.
            pub fn sign_mu(&self, mu: &[u8; 64], rnd: &[u8; 32]) -> Result<[u8; $sig], MlDsaError> {
                $crate::dit::enter!(dit);
                let mut sig = [0u8; $sig];
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                // SAFETY: `self.sk`, `mu`, `rnd`, `sig` and `scratch` are
                // valid for reads (and, for the last two, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end of
                // the address space. `self.sk` was written by the key
                // generation.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe {
                    $sign(dit, &self.sk, mu, rnd, &mut sig, scratch.0.as_mut_ptr())
                };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                if r != 1 {
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    zeroize(&mut sig);
                    return Err(MlDsaError::LoopBound);
                    // NO-COVERAGE-END
                }
                Ok(sig)
            }

        }

        impl $VerifyingKey {
            /// This key, prepared for many verifications: see
            #[doc = concat!("[`", stringify!($PreparedVerifyingKey), "`].")]
            pub fn prepare(self) -> $PreparedVerifyingKey {
                let dit = $crate::dit::public($crate::dit::Why::PublicKey);
                let mut prepared = $crate::align::CacheAligned([0u8; $prepared_pk]);
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut work = $crate::align::CacheAligned(core::mem::MaybeUninit::<[u64; 128]>::uninit());
                // SAFETY: `self.bytes`, `prepared` and `work` are valid
                // for reads (and, for the last two, writes) of their
                // sizes; they are distinct Rust objects, so they do not
                // overlap each other or the stack, or wrap around the end
                // of the address space. `prepare_verify` writes the
                // prepared key of `self.bytes` to `prepared`
                // (`VG.Spec.MlDsa.preparePublicKeyContract`).
                unsafe { $prepare_verify(dit, &self.bytes, &mut prepared.0, work.0.as_mut_ptr()) };
                $PreparedVerifyingKey { prepared, key: self }
            }
        }

        #[doc = concat!(
            "An ", $name, " public key prepared for many verifications ([`",
            stringify!($VerifyingKey), "::prepare`]), which may make each faster than \
            [`", stringify!($VerifyingKey), "::verify`]'s: for a key that verifies a stream of \
            signatures. It is immutable, so threads can share it. It holds ",
            stringify!($prepared_pk), " more bytes than the key."
        )]
        pub struct $PreparedVerifyingKey {
            // The prepared key of `key.bytes`, which `prepare_verify` wrote
            // (`VG.Spec.MlDsa.PreparedPublicKey`), never changed since.
            prepared: $crate::align::CacheAligned<[u8; $prepared_pk]>,
            key: $VerifyingKey,
        }

        impl core::fmt::Debug for $PreparedVerifyingKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($PreparedVerifyingKey)).finish_non_exhaustive()
            }
        }

        impl $PreparedVerifyingKey {
            /// The key it was prepared from.
            pub fn verifying_key(&self) -> &$VerifyingKey {
                &self.key
            }

            #[doc = concat!("What [`", stringify!($VerifyingKey), "::verify`] says of the key it was prepared from.")]
            pub fn verify(&self, msg: &[u8], ctx: &[u8], sig: &[u8; $sig]) -> Result<(), InvalidSignature> {
                let dit = $crate::dit::public($crate::dit::Why::Verify);
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<MessageScratch>::uninit());
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.prepared`, `sig`, `scratch` and
                // `self.key.tr` are valid for reads (and, for `scratch`,
                // writes) of their sizes, and `msg` and `ctx` for reads of
                // their lengths; they are distinct Rust objects, so they
                // do not overlap each other or the stack, or wrap around
                // the end of the address space. `self.prepared` is the
                // prepared key of `self.key.bytes`, and `self.key.tr` is
                // H(self.key.bytes, 64), from its constructors.
                // The dispatcher calls only an implementation the CPU has
                // the features of.
                let r = unsafe {
                    $verify_message_prepared(dit, &self.prepared.0, m, m_len, c, c_len, sig, scratch.0.as_mut_ptr(), &self.key.tr)
                };
                // 2 is a context longer than 255 bytes.
                if r == 1 { Ok(()) } else { Err(InvalidSignature) }
            }
        }

        impl $SigningKey {
            /// This key, prepared for many signatures: see
            #[doc = concat!("[`", stringify!($PreparedSigningKey), "`].")]
            pub fn prepare(self) -> $PreparedSigningKey {
                $crate::dit::enter!(dit);
                let mut prepared = $crate::align::CacheAligned([0u8; $prepared_sk]);
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut work = $crate::align::CacheAligned(core::mem::MaybeUninit::<[u64; 128]>::uninit());
                // SAFETY: `self.sk`, `prepared` and `work` are valid for
                // reads (and, for the last two, writes) of their sizes;
                // they are distinct Rust objects, so they do not overlap
                // each other or the stack, or wrap around the end of the
                // address space. `prepare_sign` writes the prepared key of
                // `self.sk` to `prepared`
                // (`VG.Spec.MlDsa.prepareSecretKeyContract`).
                unsafe { $prepare_sign(dit, &self.sk, &mut prepared.0, work.0.as_mut_ptr()) };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut work));
                $PreparedSigningKey { prepared, key: self }
            }
        }

        #[doc = concat!(
            "An ", $name, " private key prepared for many signatures ([`",
            stringify!($SigningKey), "::prepare`]), which may make each faster than \
            [`", stringify!($SigningKey), "::sign`]'s: for a key that signs a stream of \
            messages. It is immutable, so threads can share it, and is destroyed when it is \
            dropped. It holds ", stringify!($prepared_sk), " more bytes than the key."
        )]
        pub struct $PreparedSigningKey {
            // The prepared key of `key.sk`, which `prepare_sign` wrote
            // (`VG.Spec.MlDsa.PreparedSecretKey`), never changed since.
            prepared: $crate::align::CacheAligned<[u8; $prepared_sk]>,
            key: $SigningKey,
        }

        impl core::fmt::Debug for $PreparedSigningKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($PreparedSigningKey)).finish_non_exhaustive()
            }
        }

        impl Drop for $PreparedSigningKey {
            fn drop(&mut self) {
                zeroize(&mut self.prepared.0);
            }
        }

        impl $PreparedSigningKey {
            /// The key it was prepared from.
            pub fn signing_key(&self) -> &$SigningKey {
                &self.key
            }

            #[doc = concat!("What [`", stringify!($SigningKey), "::sign`] gives with the key it was prepared from.")]
            pub fn sign(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], MlDsaError> {
                let mut rnd = [0u8; 32];
                getrandom::fill(&mut rnd).map_err(|_| MlDsaError::Randomness)?;
                let r = self.sign_with(msg, ctx, &rnd);
                zeroize(&mut rnd);
                r
            }

            #[doc = concat!("What [`", stringify!($SigningKey), "::sign_deterministic`] gives with the key it was prepared from.")]
            pub fn sign_deterministic(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], MlDsaError> {
                self.sign_with(msg, ctx, &[0; 32])
            }

            fn sign_with(&self, msg: &[u8], ctx: &[u8], rnd: &[u8; 32]) -> Result<[u8; $sig], MlDsaError> {
                $crate::dit::enter!(dit);
                let mut sig = [0u8; $sig];
                // The verified contracts accept arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<MessageScratch>::uninit());
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.prepared`, `rnd`, `sig` and `scratch` are
                // valid for reads (and, for the last two, writes) of their
                // sizes, and `msg` and `ctx` for reads of their lengths; they
                // are distinct Rust objects, so they do not overlap each other
                // or the stack, or wrap around the end of the address space.
                // `self.prepared` is the prepared key of `self.key.sk`, which
                // the key generation wrote. The dispatcher calls only an
                // implementation the CPU has the features of.
                let r = unsafe {
                    $sign_message_prepared(dit, &self.prepared.0, m, m_len, c, c_len, rnd, &mut sig, scratch.0.as_mut_ptr())
                };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                match r {
                    1 => Ok(sig),
                    2 => Err(MlDsaError::ContextTooLong),
                    // A loop reaches its bound with probability about 2^-256
                    // or less.
                    // NO-COVERAGE-START
                    _ => {
                        zeroize(&mut sig);
                        Err(MlDsaError::LoopBound)
                    }
                    // NO-COVERAGE-END
                }
            }
        }
    };
}

pub(crate) use ml_dsa;

#[cfg(test)]
mod tests {
    use crate::error::{InvalidSignature, MlDsaError};
    use crate::mldsa44::SigningKey44;

    #[test]
    fn context_too_long() {
        let key = SigningKey44::from_seed(&[7; 32]).unwrap();
        let sig = key.sign_deterministic(b"msg", &[0; 255]).unwrap();
        let vk = key.verifying_key();
        assert_eq!(vk.verify(b"msg", &[0; 255], &sig), Ok(()));
        assert_eq!(key.sign(b"msg", &[0; 256]), Err(MlDsaError::ContextTooLong));
        assert_eq!(vk.verify(b"msg", &[0; 256], &sig), Err(InvalidSignature));
    }
}
