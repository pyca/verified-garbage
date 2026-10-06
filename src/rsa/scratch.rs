//! One exclusively owned, wiped verification buffer retained per public key.

use crate::zeroize::zeroize;
use alloc::{boxed::Box, vec, vec::Vec};
use core::{
    fmt,
    ops::{Deref, DerefMut},
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

pub(crate) struct VerifyScratch(AtomicPtr<Vec<u64>>);

impl VerifyScratch {
    pub(super) fn new() -> Self {
        Self(AtomicPtr::new(ptr::null_mut()))
    }

    pub(crate) fn take(&self, words: usize) -> ScratchLease<'_> {
        let pointer = self.0.swap(ptr::null_mut(), Ordering::Acquire);
        let mut buffer = if pointer.is_null() {
            Box::new(vec![0; words])
        } else {
            // SAFETY: swap removes the only pointer from the pool, transferring
            // ownership of the Box installed by a previous lease's release CAS.
            unsafe { Box::from_raw(pointer) }
        };
        buffer.resize(words, 0);
        ScratchLease {
            pool: self,
            buffer: Some(buffer),
        }
    }
}

// The cache does not contribute to a key's value or to a cloned key's storage.
impl Clone for VerifyScratch {
    fn clone(&self) -> Self {
        Self::new()
    }
}
impl fmt::Debug for VerifyScratch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VerifyScratch")
    }
}
impl PartialEq for VerifyScratch {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for VerifyScratch {}

impl Drop for VerifyScratch {
    fn drop(&mut self) {
        let pointer = *self.0.get_mut();
        if !pointer.is_null() {
            // SAFETY: exclusive access to the pool excludes outstanding leases;
            // a non-null pointer owns a Box installed by ScratchLease::drop.
            unsafe {
                drop(Box::from_raw(pointer));
            }
        }
    }
}

pub(crate) struct ScratchLease<'a> {
    pool: &'a VerifyScratch,
    buffer: Option<Box<Vec<u64>>>,
}
impl Deref for ScratchLease<'_> {
    type Target = [u64];
    fn deref(&self) -> &[u64] {
        self.buffer.as_ref().unwrap()
    }
}
impl DerefMut for ScratchLease<'_> {
    fn deref_mut(&mut self) -> &mut [u64] {
        self.buffer.as_mut().unwrap()
    }
}
impl Drop for ScratchLease<'_> {
    fn drop(&mut self) {
        let mut buffer = self.buffer.take().unwrap();
        // Wipe before publishing the buffer or freeing a concurrent caller's
        // surplus buffer, including when unwinding out of verification.
        zeroize(&mut buffer);
        let pointer = Box::into_raw(buffer);
        if self
            .pool
            .0
            .compare_exchange(
                ptr::null_mut(),
                pointer,
                Ordering::Release,
                Ordering::Relaxed,
            )
            .is_err()
        {
            // SAFETY: failed CAS did not publish this pointer. This lease still
            // owns it; the buffer already present belongs to another lease.
            unsafe {
                drop(Box::from_raw(pointer));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;

    #[test]
    fn wiped_reuse_and_resize() {
        let pool = VerifyScratch::new();
        let pointer = {
            let mut lease = pool.take(32);
            lease.fill(u64::MAX);
            lease.as_ptr()
        };
        let lease = pool.take(32);
        assert_eq!(lease.as_ptr(), pointer);
        assert!(lease.iter().all(|&x| x == 0));
        drop(lease);
        let lease = pool.take(64);
        assert_eq!(lease.len(), 64);
        assert!(lease.iter().all(|&x| x == 0));
    }

    #[test]
    fn overlapping_leases_are_independent() {
        let pool = VerifyScratch::new();
        let mut a = pool.take(32);
        let mut b = pool.take(32);
        assert_ne!(a.as_ptr(), b.as_ptr());
        a.fill(7);
        b.fill(11);
        assert!(a.iter().all(|&x| x == 7));
        drop(a);
        assert!(b.iter().all(|&x| x == 11));
        drop(b);
        assert!(pool.take(32).iter().all(|&x| x == 0));
    }
    #[test]
    fn concurrent_leases_are_wiped() {
        let pool = VerifyScratch::new();
        std::thread::scope(|scope| {
            for id in 1..=8 {
                let pool = &pool;
                scope.spawn(move || {
                    for _ in 0..100 {
                        let mut lease = pool.take(32);
                        assert!(lease.iter().all(|&x| x == 0));
                        lease.fill(id);
                        std::thread::yield_now();
                        assert!(lease.iter().all(|&x| x == id));
                    }
                });
            }
        });
        assert!(pool.take(32).iter().all(|&x| x == 0));
    }

    #[test]
    fn unwinding_wipes_before_reuse() {
        let pool = VerifyScratch::new();
        let result = std::panic::catch_unwind(|| {
            let mut lease = pool.take(32);
            lease.fill(u64::MAX);
            panic!("exercise lease cleanup");
        });
        assert!(result.is_err());
        assert!(pool.take(32).iter().all(|&x| x == 0));
    }
}
