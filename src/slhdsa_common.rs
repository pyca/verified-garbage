//! What the SLH-DSA parameter sets share: their API, defined once by
//! `slh_dsa!`.

#![cfg(target_arch = "x86_64")]

/// Defines the API of one SLH-DSA parameter set: its `SigningKey` and
/// `VerifyingKey`, over the dispatchers (`_auto`, which run the best
/// implementation the CPU supports) of its verified `keygen`, `sign` and
/// `verify` functions, and its sizes.
macro_rules! slh_dsa {
    (
        name: $name:literal,
        keygen: $keygen:path,
        sign: $sign:path,
        verify: $verify:path,
        n: $n:literal,
        sig: $sig:literal $(,)?
    ) => {
        use $crate::error::{InvalidSignature, SlhDsaError};
        use $crate::zeroize::zeroize;

        /// The working space of the assembly functions.
        type Scratch = [u64; 8192];

        /// The size of a public key, `PK.seed ‖ PK.root`.
        const PK: usize = 2 * $n;
        /// The size of a private key, `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`.
        const SK: usize = 4 * $n;

        #[doc = concat!("An ", $name, " public key.")]
        #[derive(Clone, PartialEq, Eq)]
        pub struct VerifyingKey {
            bytes: [u8; PK],
        }

        impl core::fmt::Debug for VerifyingKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct("VerifyingKey").finish_non_exhaustive()
            }
        }

        impl VerifyingKey {
            /// The size of a public key, in bytes.
            pub const SIZE: usize = PK;
            /// The size of a signature, in bytes.
            pub const SIGNATURE_SIZE: usize = $sig;

            /// The public key `PK.seed ‖ PK.root` (every byte string of
            /// this size is one).
            pub fn from_bytes(bytes: &[u8; PK]) -> Self {
                VerifyingKey { bytes: *bytes }
            }

            /// The bytes of the key.
            pub fn as_bytes(&self) -> &[u8; PK] {
                &self.bytes
            }

            /// `slh_verify(M, SIG, ctx, PK)` (FIPS 205 Algorithm 24):
            /// whether `sig` is a valid signature of the message `msg` with
            /// the context string `ctx`. Fails with [`InvalidSignature`] if
            /// it is not, if `sig` is not of `SIGNATURE_SIZE` bytes, or if
            /// `ctx` is longer than 255 bytes, for which nothing is a valid
            /// signature.
            pub fn verify(&self, msg: &[u8], ctx: &[u8], sig: &[u8]) -> Result<(), InvalidSignature> {
                let dit = $crate::dit::public($crate::dit::Why::Verify);
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                let (m, m_len, c, c_len, s, s_len) =
                    (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len(), sig.as_ptr(), sig.len());
                // SAFETY: `self.bytes` and `scratch` are valid for reads
                // (and, for `scratch`, writes) of their sizes, and `msg`,
                // `ctx` and `sig` for reads of their lengths; they are
                // distinct Rust objects, so they do not overlap each other or
                // the stack, or wrap around the end of the address space.
                // The dispatcher calls only an implementation the CPU has the
                // features of.
                let r = unsafe { $verify(dit, &self.bytes, m, m_len, c, c_len, s, s_len, scratch.0.as_mut_ptr()) };
                if r == 1 { Ok(()) } else { Err(InvalidSignature) }
            }
        }

        #[doc = concat!(
            "An ", $name, " private key, `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` (FIPS 205 §9.1), \
            destroyed when it is dropped."
        )]
        pub struct SigningKey {
            sk: [u8; SK],
        }

        impl core::fmt::Debug for SigningKey {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct("SigningKey").finish_non_exhaustive()
            }
        }

        impl Drop for SigningKey {
            fn drop(&mut self) {
                zeroize(&mut self.sk);
            }
        }

        impl SigningKey {
            /// The size of a private key, in bytes.
            pub const SIZE: usize = SK;
            /// The size of each seed, and of the signing randomness, in bytes.
            pub const SEED_SIZE: usize = $n;

            /// `slh_keygen()` (FIPS 205 Algorithm 21): a key pair of seeds
            /// from the operating system's random number generator.
            pub fn generate() -> Result<Self, SlhDsaError> {
                let mut seeds = [0u8; 3 * $n];
                getrandom::fill(&mut seeds).map_err(|_| SlhDsaError::Randomness)?;
                let key = Self::from_seeds(&seeds);
                zeroize(&mut seeds);
                Ok(key)
            }

            /// `slh_keygen_internal(SK.seed, SK.prf, PK.seed)` (FIPS 205
            /// Algorithm 18): the key pair of the seeds
            /// `SK.seed ‖ SK.prf ‖ PK.seed`, `n` bytes each, which must be
            /// random bytes from an approved RBG (FIPS 205 §3.1), or seeds so
            /// generated before.
            pub fn from_seeds(seeds: &[u8; 3 * $n]) -> Self {
                $crate::dit::enter!(dit);
                let mut key = SigningKey { sk: [0; SK] };
                let mut pk = [0u8; PK];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                // SAFETY: `seeds`, `key.sk`, `pk` and `scratch` are valid for
                // reads (and, for the last three, writes) of their sizes;
                // they are distinct Rust objects, so they do not overlap each
                // other or the stack, or wrap around the end of the address
                // space. The dispatcher calls only an implementation the CPU
                // has the features of.
                unsafe { $keygen(dit, seeds, &mut key.sk, &mut pk, scratch.0.as_mut_ptr()) };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                key
            }

            /// The private key `SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root` as
            /// FIPS 205 encodes it, which must have been written by key
            /// generation (this one, or another implementation's).
            pub fn from_bytes(bytes: &[u8; SK]) -> Self {
                SigningKey { sk: *bytes }
            }

            /// The bytes of the private key.
            pub fn as_bytes(&self) -> &[u8; SK] {
                &self.sk
            }

            /// The public key, the private key's last `2n` bytes.
            pub fn verifying_key(&self) -> VerifyingKey {
                let mut bytes = [0u8; PK];
                bytes.copy_from_slice(&self.sk[2 * $n..]);
                VerifyingKey { bytes }
            }

            /// `slh_sign(M, ctx, SK)` (FIPS 205 Algorithm 22), hedged: a
            /// signature of the message `msg` with the context string
            /// `ctx`, with `n` bytes of randomness from the operating
            /// system. Fails with [`SlhDsaError::ContextTooLong`] if `ctx`
            /// is longer than 255 bytes.
            pub fn sign(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], SlhDsaError> {
                let mut addrnd = [0u8; $n];
                getrandom::fill(&mut addrnd).map_err(|_| SlhDsaError::Randomness)?;
                let r = self.sign_with(msg, ctx, addrnd.as_ptr());
                zeroize(&mut addrnd);
                r
            }

            /// The deterministic variant of `slh_sign(M, ctx, SK)` (FIPS
            /// 205 Algorithm 22, with `PK.seed` for `addrnd`). FIPS 205
            /// §3.2 recommends the hedged [`sign`](Self::sign) where side
            /// channels are a concern.
            pub fn sign_deterministic(&self, msg: &[u8], ctx: &[u8]) -> Result<[u8; $sig], SlhDsaError> {
                self.sign_with(msg, ctx, self.sk[2 * $n..].as_ptr())
            }

            /// `slh_sign(M, ctx, SK)` with the randomness `addrnd` (FIPS
            /// 205 Algorithm 22, line 5), which must be fresh random bytes
            /// from an approved RBG: for known-answer tests.
            pub fn sign_with_randomness(&self, msg: &[u8], ctx: &[u8], addrnd: &[u8; $n]) -> Result<[u8; $sig], SlhDsaError> {
                self.sign_with(msg, ctx, addrnd.as_ptr())
            }

            /// Signing with the `n` bytes at `addrnd` (the caller's
            /// randomness, or `PK.seed` in `self.sk`).
            fn sign_with(&self, msg: &[u8], ctx: &[u8], addrnd: *const u8) -> Result<[u8; $sig], SlhDsaError> {
                $crate::dit::enter!(dit);
                let mut sig = [0u8; $sig];
                // The verified contract accepts arbitrary initial scratch bytes.
                let mut scratch = $crate::align::CacheAligned(core::mem::MaybeUninit::<Scratch>::uninit());
                let (m, m_len, c, c_len) = (msg.as_ptr(), msg.len(), ctx.as_ptr(), ctx.len());
                // SAFETY: `self.sk`, `sig` and `scratch` are valid for reads
                // (and, for the last two, writes) of their sizes, `msg` and
                // `ctx` for reads of their lengths, and `addrnd` for reads of
                // `n` bytes (the caller's array, or bytes `2n` to `3n - 1` of
                // `self.sk`); `sig` and `scratch` are distinct Rust objects
                // from the others, so they do not overlap them or the stack,
                // or wrap around the end of the address space. `self.sk` was
                // written by key generation. The dispatcher calls only an
                // implementation the CPU has the features of.
                let r = unsafe {
                    $sign(dit, &self.sk, m, m_len, c, c_len, addrnd.cast::<[u8; $n]>(), &mut sig, scratch.0.as_mut_ptr())
                };
                $crate::zeroize::zeroize(core::slice::from_mut(&mut scratch));
                match r {
                    1 => Ok(sig),
                    // The contract leaves `sig` as it was: zeros.
                    _ => Err(SlhDsaError::ContextTooLong),
                }
            }
        }
    };
}

pub(crate) use slh_dsa;
