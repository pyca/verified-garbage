//! A domain's public key-generation data, computed at the domain's first key
//! generation and shared by its clones.

// Verified code writes the representation and its metadata: the Rust neither
// recognizes groups nor derives an exponent width from private bytes.

use crate::arch::dispatch::ffdh::vg_ffdh_generate_key_precompute_auto;
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use core::{
    fmt, ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

/// The words `vg_ffdh_generate_key_precompute` writes for a domain accepted
/// by `vg_ffdh_check_domain` (`p_len` bytes of p, the domain `2 p_len` or
/// `3 p_len` bytes): canonical `VG.Spec.Ffdh.generationPrecompute` words.
fn precompute(dit: crate::dit::Dit<'_>, domain: &[u8], p_len: usize) -> Vec<u64> {
    let mut words = alloc::vec![0; 3 + 34 * p_len.div_ceil(8)];
    let mut scratch = crate::rsa::Scratch::new(16 * p_len + 32);
    // SAFETY: the domain was accepted by vg_ffdh_check_domain. Its
    // length is 2*p_len or 3*p_len, p_len is in 64..=1024, words has
    // exactly 3+34*ceil(p_len/8) entries and scratch has 16*p_len+32
    // words. These are disjoint Rust allocations. The dispatcher calls
    // only an implementation the CPU has the features of.
    let ok = unsafe {
        vg_ffdh_generate_key_precompute_auto(
            dit,
            words.as_mut_ptr(),
            words.len(),
            domain.as_ptr(),
            domain.len(),
            p_len,
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    assert_eq!(ok, 1);
    words
}

/// Where the words are published, once computed.
struct Cell(AtomicPtr<Vec<u64>>);

impl Drop for Cell {
    fn drop(&mut self) {
        let pointer = *self.0.get_mut();
        if !pointer.is_null() {
            // SAFETY: exclusive access to `self` excludes any borrow of the
            // words; a pointer that is not null owns the `Box` that
            // `install` published.
            unsafe {
                drop(Box::from_raw(pointer));
            }
        }
    }
}

/// Canonical `VG.Spec.Ffdh.generationPrecompute` words, computed at the
/// first call of `words` and shared by every clone.
#[derive(Clone)]
pub(super) struct Precomputed(Arc<Cell>);

impl Precomputed {
    pub(super) fn new() -> Self {
        Self(Arc::new(Cell(AtomicPtr::new(ptr::null_mut()))))
    }

    /// The words of `domain`, a domain accepted by `vg_ffdh_check_domain`
    /// with a `p_len`-byte p and the same at every call, computed if no call
    /// has yet.
    pub(super) fn words(&self, dit: crate::dit::Dit<'_>, domain: &[u8], p_len: usize) -> &[u64] {
        let pointer = self.0.0.load(Ordering::Acquire);
        if pointer.is_null() {
            self.install(precompute(dit, domain, p_len))
        } else {
            // SAFETY: a pointer that is not null owns the `Box` that `install`
            // published, which is freed only when the last clone is dropped.
            unsafe { &*pointer }
        }
    }

    /// `words`, published, or the words another call published first
    /// (computed from the same domain).
    fn install(&self, words: Vec<u64>) -> &[u64] {
        let ours = Box::into_raw(Box::new(words));
        match self
            .0
            .0
            .compare_exchange(ptr::null_mut(), ours, Ordering::AcqRel, Ordering::Acquire)
        {
            // SAFETY: `ours` is published, and freed only when the last clone
            // is dropped.
            Ok(_) => unsafe { &*ours },
            Err(theirs) => {
                // SAFETY: the failed exchange did not publish `ours`, which
                // this call still owns; `theirs` is published, as above.
                unsafe {
                    drop(Box::from_raw(ours));
                    &*theirs
                }
            }
        }
    }

    /// Whether the words are computed.
    #[cfg(test)]
    pub(super) fn computed(&self) -> bool {
        !self.0.0.load(Ordering::Acquire).is_null()
    }

    #[cfg(test)]
    pub(super) fn shares_allocation(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl fmt::Debug for Precomputed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Precomputed")
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::Precomputed;

    /// A call that loses the race to publish its words takes the winner's.
    #[test]
    fn first_published_words_win() {
        let pre = Precomputed::new();
        let first = pre.install(alloc::vec![1, 2]).as_ptr();
        assert_eq!(pre.install(alloc::vec![3, 4]), &[1, 2]);
        assert_eq!(pre.install(alloc::vec![3, 4]).as_ptr(), first);
        assert_eq!(std::format!("{pre:?}"), "Precomputed");
    }
}
