//! Immutable, lazily prepared ML-DSA key polynomials.

use alloc::{
    alloc::{Layout, alloc_zeroed},
    boxed::Box,
};
use core::{
    marker::PhantomData,
    ptr,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

#[repr(C, align(64))]
pub(crate) struct Prepared<const N: usize, const SECRET: bool> {
    pub(crate) bytes: [u8; N],
}
impl<const N: usize, const SECRET: bool> Prepared<N, SECRET> {
    pub(crate) fn allocate() -> Option<Box<Self>> {
        const {
            assert!(N > 0);
        }
        // SAFETY: nonzero sized/aligned array object. Zero is a valid value of
        // every byte; Box takes ownership only when allocation succeeded.
        let p = unsafe { alloc_zeroed(Layout::new::<Self>()).cast::<Self>() };
        if p.is_null() {
            None
        } else {
            // SAFETY: p is the unique allocation returned for this layout.
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
    #[cfg(all(test, feature = "std"))]
    pub(crate) fn ready(&self) -> bool {
        !self.pointer.load(Ordering::Acquire).is_null()
    }
    pub(crate) fn get(&self, build: impl FnOnce() -> Option<Box<T>>) -> Option<&T> {
        let p = self.pointer.load(Ordering::Acquire);
        if !p.is_null() {
            // SAFETY: publication releases a complete immutable Box. It is
            // freed only by Drop, excluded by our shared borrow of self.
            return Some(unsafe { &*p });
        }
        // First use stays compact. Exactly one later caller can claim
        // preparation; a busy, failed, or panicking builder is never retried.
        if self
            .uses
            .compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
        {
            return None;
        }
        if self
            .uses
            .compare_exchange(1, 2, Ordering::Relaxed, Ordering::Relaxed)
            .is_err()
        {
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
    static FAIL_SIZE: AtomicUsize = AtomicUsize::new(0);
    static WIPED: AtomicUsize = AtomicUsize::new(0);
    struct ObserveFree;
    #[global_allocator]
    static ALLOCATOR: ObserveFree = ObserveFree;
    unsafe impl GlobalAlloc for ObserveFree {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            unsafe { System.alloc(layout) }
        }
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            if FAIL_SIZE
                .compare_exchange(layout.size(), 0, Ordering::AcqRel, Ordering::Relaxed)
                .is_ok()
            {
                return ptr::null_mut();
            }
            unsafe { System.alloc_zeroed(layout) }
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
        let cache = Cache::new();
        assert!(
            cache
                .get(|| panic!("first use must stay compact"))
                .is_none()
        );
        assert!(!cache.ready());
        assert_eq!(cache.get(|| Some(Box::new(42))), Some(&42));
        assert!(cache.ready());
        assert!(cache == cache.clone());
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
    fn mldsa_cache_allocation_failure_is_fallible() {
        type Public = Prepared<31337, false>;
        FAIL_SIZE.store(Layout::new::<Public>().size(), Ordering::Release);
        assert!(Public::allocate().is_none());
        assert_eq!(FAIL_SIZE.load(Ordering::Acquire), 0);
        let value = Public::allocate().unwrap();
        assert!(value.bytes.iter().all(|&b| b == 0));
        drop(value);
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
