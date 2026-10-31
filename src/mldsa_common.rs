// UNPROVED automatic prepared-key experiment; AArch64 only. Do not ship.
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
    #[cfg_attr(
        not(any(target_arch = "x86_64", target_arch = "aarch64")),
        allow(unused_variables)
    )]
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
/// `verify_message` functions (on x86-64 and AArch64, `verify_message_cached`,
/// which takes the hash `tr` of the public key the `VerifyingKey` keeps), its
/// `sign` and `verify` functions (which take a precomputed `μ`)
/// and its sizes.
// UNPROVED EXPERIMENT: Rust publication protocol, not a verified prepared-key API.
#[cfg(all(target_arch = "aarch64", feature = "alloc"))]
pub(crate) mod auto_cache {
    use alloc::{
        alloc::{Layout, alloc_zeroed},
        boxed::Box,
    };
    use core::{
        marker::PhantomData,
        ptr,
        sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
    };

    pub(crate) const AFTER: usize = match option_env!("VG_MLDSA_CACHE_AFTER") {
        Some(s) => match s.as_bytes() {
            b"0" => 0,
            b"1" => 1,
            b"4" => 4,
            _ => 2,
        },
        None => 2,
    };

    #[repr(C, align(16))]
    pub(crate) struct Prepared<const N: usize, const SECRET: bool> {
        pub(crate) bytes: [u8; N],
    }
    impl<const N: usize, const SECRET: bool> Prepared<N, SECRET> {
        pub(crate) fn allocate() -> Option<Box<Self>> {
            // SAFETY: nonzero sized/aligned array object. Zero is a valid value of
            // every byte; Box takes ownership only when allocation succeeded.
            let p = unsafe { alloc_zeroed(Layout::new::<Self>()).cast::<Self>() };
            if p.is_null() {
                None
            } else {
                Some(unsafe { Box::from_raw(p) })
            }
        }
    }
    impl<const N: usize, const SECRET: bool> Drop for Prepared<N, SECRET> {
        fn drop(&mut self) {
            if SECRET {
                crate::zeroize::zeroize(&mut self.bytes);
            }
        }
    }

    pub(crate) struct Cache<T> {
        pointer: AtomicPtr<T>,
        uses: AtomicUsize,
        // AtomicPtr alone would permit non-Send/non-Sync T. Ownership ties our
        // auto traits and drop checking to the published allocation's contents.
        owned: PhantomData<Box<T>>,
    }
    impl<T> Cache<T> {
        pub(crate) fn new() -> Self {
            Self {
                pointer: AtomicPtr::new(ptr::null_mut()),
                uses: AtomicUsize::new(0),
                owned: PhantomData,
            }
        }
        pub(crate) fn get(&self, build: impl FnOnce() -> Option<Box<T>>) -> Option<&T> {
            if AFTER == 0 {
                return None;
            }
            let p = self.pointer.load(Ordering::Acquire);
            if !p.is_null() {
                // SAFETY: publication releases a complete immutable Box. It is
                // freed only by Drop, excluded by our shared borrow of self.
                return Some(unsafe { &*p });
            }
            let mut uses = self.uses.load(Ordering::Relaxed);
            loop {
                // Reaching AFTER also claims initialization. Other callers do
                // not wait, allocate, or retry a failed/panicking preparation.
                if uses >= AFTER {
                    return None;
                }
                match self.uses.compare_exchange_weak(
                    uses,
                    uses + 1,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(current) => uses = current,
                }
            }
            if uses + 1 < AFTER {
                return None;
            }
            let p = Box::into_raw(build()?);
            self.pointer.store(p, Ordering::Release);
            // SAFETY: as above; this caller owns the initialization claim.
            Some(unsafe { &*p })
        }
    }
    // Cached values/usage counts are performance hints, not key identity.
    // Clones start cold; they never copy or share secret cache allocations.
    impl<T> Clone for Cache<T> {
        fn clone(&self) -> Self {
            Self::new()
        }
    }
    impl<T> PartialEq for Cache<T> {
        fn eq(&self, _: &Self) -> bool {
            true
        }
    }
    impl<T> Eq for Cache<T> {}
    impl<T> Drop for Cache<T> {
        fn drop(&mut self) {
            let p = *self.pointer.get_mut();
            if !p.is_null() {
                // SAFETY: exclusive access excludes all outstanding borrows.
                unsafe {
                    drop(Box::from_raw(p));
                }
            }
        }
    }
    #[cfg(all(test, feature = "std"))]
    mod tests {
        use super::*;
        use std::{
            alloc::{GlobalAlloc, System},
            sync::{Arc, Barrier},
            thread,
        };
        static TARGET: AtomicPtr<u8> = AtomicPtr::new(ptr::null_mut());
        static WIPED: AtomicUsize = AtomicUsize::new(0);
        struct ObserveFree;
        #[global_allocator]
        static ALLOCATOR: ObserveFree = ObserveFree;
        unsafe impl GlobalAlloc for ObserveFree {
            unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
                unsafe { System.alloc(layout) }
            }
            unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
                if TARGET
                    .compare_exchange(p, ptr::null_mut(), Ordering::AcqRel, Ordering::Relaxed)
                    .is_ok()
                {
                    // The allocation is still owned here, after its value's
                    // Drop and before its storage is released to System.
                    let bytes = unsafe { core::slice::from_raw_parts(p, layout.size()) };
                    WIPED.store(
                        if bytes.iter().all(|&b| b == 0) { 1 } else { 2 },
                        Ordering::Release,
                    );
                }
                unsafe {
                    System.dealloc(p, layout);
                }
            }
        }
        #[test]
        fn mldsa_cache_promotes_once_and_clone_starts_cold() {
            assert_eq!(AFTER, 2, "protocol tests use second-use policy");
            let cache = Cache::new();
            assert!(
                cache
                    .get(|| panic!("first use must stay compact"))
                    .is_none()
            );
            assert_eq!(cache.get(|| Some(Box::new(42))), Some(&42));
            assert_eq!(cache.get(|| panic!("already initialized")), Some(&42));
            assert!(cache.clone().get(|| panic!("clone starts cold")).is_none());
        }
        #[test]
        fn mldsa_cache_failed_preparation_falls_back_permanently() {
            let cache = Cache::<usize>::new();
            assert!(cache.get(|| panic!("first use")).is_none());
            assert!(cache.get(|| None).is_none());
            assert!(cache.get(|| panic!("must not retry allocation")).is_none());
        }
        #[test]
        fn mldsa_cache_panicking_preparation_does_not_block_later_calls() {
            let cache = Cache::<usize>::new();
            assert!(cache.get(|| None).is_none());
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    cache.get(|| panic!("simulated initializer panic"));
                }))
                .is_err()
            );
            assert!(cache.get(|| panic!("must not retry")).is_none());
        }
        #[test]
        fn mldsa_cache_readers_do_not_wait_for_initializer() {
            let cache = Arc::new(Cache::new());
            let started = Arc::new(Barrier::new(2));
            let release = Arc::new(Barrier::new(2));
            assert!(cache.get(|| None).is_none());
            let builder = {
                let (cache, started, release) = (cache.clone(), started.clone(), release.clone());
                thread::spawn(move || {
                    assert_eq!(
                        cache.get(|| {
                            started.wait();
                            release.wait();
                            Some(Box::new(99))
                        }),
                        Some(&99)
                    );
                })
            };
            started.wait();
            // This has to complete before the initializer is released.
            assert!(cache.get(|| panic!("only one builder")).is_none());
            release.wait();
            builder.join().unwrap();
            thread::scope(|scope| {
                for _ in 0..16 {
                    let cache = &cache;
                    scope.spawn(move || {
                        for _ in 0..1000 {
                            assert_eq!(cache.get(|| panic!("published")), Some(&99));
                        }
                    });
                }
            });
        }
        #[test]
        fn mldsa_cache_secret_is_zero_at_deallocation() {
            let cache = Cache::new();
            assert!(cache.get(|| None).is_none());
            let prepared = cache
                .get(|| {
                    let mut value = Prepared::<32, true>::allocate()?;
                    value.bytes.fill(0x5a);
                    Some(value)
                })
                .unwrap();
            TARGET.store(
                core::ptr::from_ref(prepared).cast_mut().cast(),
                Ordering::Release,
            );
            drop(cache);
            assert_eq!(WIPED.load(Ordering::Acquire), 1);
            assert!(TARGET.load(Ordering::Acquire).is_null());
        }
    }
}

macro_rules! ml_dsa {
    (
        name: $name:literal,
        signing_key: $SigningKey:ident,
        verifying_key: $VerifyingKey:ident,
        sign_prepared: $sign_prepared:path,
        verify_prepared: $verify_prepared:path,
        sign_message_prepared: $sign_message_prepared:path,
        verify_message_prepared: $verify_message_prepared:path,
        sign_prepared_sha3: $sign_prepared_sha3:path,
        verify_prepared_sha3: $verify_prepared_sha3:path,
        sign_message_prepared_sha3: $sign_message_prepared_sha3:path,
        verify_message_prepared_sha3: $verify_message_prepared_sha3:path,
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
        k: $k:literal,
    l: $l:literal,
    eta: $eta:literal,
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
                $verify_message_cached_avx2_features,
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
            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            cache: $crate::mldsa_common::auto_cache::Cache<$crate::mldsa_common::auto_cache::Prepared<{ $pk + 1024 * $k }, false>>,
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

            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            fn prepared(&self) -> Option<&$crate::mldsa_common::auto_cache::Prepared<{ $pk + 1024 * $k }, false>> {
                self.cache.get(|| {
                    let mut prepared = $crate::mldsa_common::auto_cache::Prepared::allocate()?;
                    prepared.bytes[..$pk].copy_from_slice(&self.bytes);
                    let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                    for i in 0..$k {
                        // UNPROVED: composing existing unpack/NTT, new layout not yet proved.
                        unsafe {
                            let input = prepared.bytes.as_ptr().add(32 + 320 * i).cast();
                            let output = prepared.bytes.as_mut_ptr().add($pk + 1024 * i).cast();
                            $crate::arch::mldsa::vg_mldsa_unpack_t1(input, output);
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                    unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
                    Some(prepared)
                })
            }

            /// The size of a public key, in bytes.
            pub const SIZE: usize = $pk;
            /// The size of a signature, in bytes.
            pub const SIGNATURE_SIZE: usize = $sig;

            /// The public key `bytes` (every byte string of this size is
            /// one).
            pub fn from_bytes(bytes: &[u8; $pk]) -> Self {
                $VerifyingKey {
                    bytes: *bytes,
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    cache: $crate::mldsa_common::auto_cache::Cache::new(),
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
                if ctx.len() > 255 { return Err(Error::ContextTooLong); }
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
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    { if let Some(prepared) = self.prepared() {
                            let key = prepared.bytes.as_ptr().cast();
                            match backend() {
                                Backend::Scalar => $verify_message_prepared(key, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr),
                                Backend::Sha3 => $verify_message_prepared_sha3(key, m, m_len, c, c_len, sig, scratch.as_mut_ptr(), &self.tr),
                            }
                        } else {
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
                 } }
                    #[cfg(not(all(target_arch = "aarch64", feature = "alloc")))]
                    {
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
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    { if let Some(prepared) = self.prepared() {
                            let key = prepared.bytes.as_ptr().cast();
                            match backend() {
                                Backend::Scalar => $verify_prepared(key, mu, sig, scratch.as_mut_ptr()),
                                Backend::Sha3 => $verify_prepared_sha3(key, mu, sig, scratch.as_mut_ptr()),
                            }
                        } else {
                    match backend() {
                        Backend::Scalar => $verify(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $verify_sha3(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_avx2(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                    }
                 } }
                    #[cfg(not(all(target_arch = "aarch64", feature = "alloc")))]
                    {
                    match backend() {
                        Backend::Scalar => $verify(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $verify_sha3(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $verify_avx2(&self.bytes, mu, sig, scratch.as_mut_ptr()),
                    }
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
            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            cache: $crate::mldsa_common::auto_cache::Cache<$crate::mldsa_common::auto_cache::Prepared<{ $sk + 1024 * ($l + 2 * $k) }, true>>,
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

            #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
            fn prepared(&self) -> Option<&$crate::mldsa_common::auto_cache::Prepared<{ $sk + 1024 * ($l + 2 * $k) }, true>> {
                self.cache.get(|| {
                    let mut prepared = $crate::mldsa_common::auto_cache::Prepared::allocate()?;
                    prepared.bytes[..$sk].copy_from_slice(&self.sk);
                    let mut work = core::mem::MaybeUninit::<[u64; 128]>::uninit();
                    let slen = if $eta == 2 { 96 } else { 128 };
                    for i in 0..($l + 2 * $k) {
                        let (offset, len, a, b) = if i < $l + $k {
                            (128 + slen * i, slen, $eta, $eta)
                        } else {
                            (128 + slen * ($l + $k) + 416 * (i - $l - $k), 416, 4095, 4096)
                        };
                        // UNPROVED: composing existing unpack/NTT, new layout not yet proved.
                        unsafe {
                            let input = prepared.bytes.as_ptr().add(offset);
                            let output = prepared.bytes.as_mut_ptr().add($sk + 1024 * i).cast();
                            $crate::arch::mldsa::vg_mldsa_bit_unpack(input, len, a, b, output);
                            $crate::arch::mldsa::vg_mldsa_ntt(output, work.as_mut_ptr());
                        }
                    }
                    unsafe { $crate::zeroize::zeroize_raw(work.as_mut_ptr().cast(), 1024); }
                    Some(prepared)
                })
            }

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
                        #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                        cache: $crate::mldsa_common::auto_cache::Cache::new(),
                        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
                        tr: [0; 64],
                    },
                    sk: [0; $sk],
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    cache: $crate::mldsa_common::auto_cache::Cache::new(),
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
                if ctx.len() > 255 { return Err(Error::ContextTooLong); }
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
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    { if let Some(prepared) = self.prepared() {
                            let key = prepared.bytes.as_ptr().cast();
                            match backend() {
                                Backend::Scalar => $sign_message_prepared(key, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr()),
                                Backend::Sha3 => $sign_message_prepared_sha3(key, m, m_len, c, c_len, rnd, &mut sig, scratch.as_mut_ptr()),
                            }
                        } else {
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
                 } }
                    #[cfg(not(all(target_arch = "aarch64", feature = "alloc")))]
                    {
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
                    #[cfg(all(target_arch = "aarch64", feature = "alloc"))]
                    { if let Some(prepared) = self.prepared() {
                            let key = prepared.bytes.as_ptr().cast();
                            match backend() {
                                Backend::Scalar => $sign_prepared(key, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                                Backend::Sha3 => $sign_prepared_sha3(key, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                            }
                        } else {
                    match backend() {
                        Backend::Scalar => $sign(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $sign_sha3(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $sign_avx2(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                    }
                 } }
                    #[cfg(not(all(target_arch = "aarch64", feature = "alloc")))]
                    {
                    match backend() {
                        Backend::Scalar => $sign(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "aarch64")]
                        Backend::Sha3 => $sign_sha3(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                        #[cfg(target_arch = "x86_64")]
                        Backend::Avx2 => $sign_avx2(&self.sk, mu, rnd, &mut sig, scratch.as_mut_ptr()),
                    }
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
        use crate::cpu::Features;
        let required = Features::of(&["sha3", "sha2"]);
        assert_eq!(
            Backend::select(Features::of(&[]), required),
            Backend::Scalar
        );
        assert_eq!(
            Backend::select(Features::of(&["sha3"]), required),
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
