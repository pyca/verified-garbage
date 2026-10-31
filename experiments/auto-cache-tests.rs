    #[cfg(all(test, feature = "std"))]
    mod tests {
        use super::*;
        use std::{alloc::{GlobalAlloc, System}, sync::{Arc, Barrier}, thread};
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
                if TARGET.compare_exchange(p, ptr::null_mut(), Ordering::AcqRel, Ordering::Relaxed).is_ok() {
                    // The allocation is still owned here, after its value's
                    // Drop and before its storage is released to System.
                    let bytes = unsafe { core::slice::from_raw_parts(p, layout.size()) };
                    WIPED.store(if bytes.iter().all(|&b| b == 0) { 1 } else { 2 }, Ordering::Release);
                }
                unsafe { System.dealloc(p, layout); }
            }
        }
        #[test]
        fn mldsa_cache_promotes_once_and_clone_starts_cold() {
            assert_eq!(AFTER, 2, "protocol tests use second-use policy");
            let cache = Cache::new();
            assert!(cache.get(|| panic!("first use must stay compact")).is_none());
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
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                cache.get(|| panic!("simulated initializer panic"));
            })).is_err());
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
                    assert_eq!(cache.get(|| {
                        started.wait(); release.wait(); Some(Box::new(99))
                    }), Some(&99));
                })
            };
            started.wait();
            // This has to complete before the initializer is released.
            assert!(cache.get(|| panic!("only one builder")).is_none());
            release.wait(); builder.join().unwrap();
            thread::scope(|scope| {
                for _ in 0..16 {
                    let cache = &cache;
                    scope.spawn(move || {
                        for _ in 0..1000 { assert_eq!(cache.get(|| panic!("published")), Some(&99)); }
                    });
                }
            });
        }
        #[test]
        fn mldsa_cache_secret_is_zero_at_deallocation() {
            let cache = Cache::new();
            assert!(cache.get(|| None).is_none());
            let prepared = cache.get(|| {
                let mut value = Prepared::<32, true>::allocate()?;
                value.bytes.fill(0x5a);
                Some(value)
            }).unwrap();
            TARGET.store(core::ptr::from_ref(prepared).cast_mut().cast(), Ordering::Release);
            drop(cache);
            assert_eq!(WIPED.load(Ordering::Acquire), 1);
            assert!(TARGET.load(Ordering::Acquire).is_null());
        }
    }
