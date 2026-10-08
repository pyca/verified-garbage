//! The values of a public key's modulus that its operations take
//! (`VG.Spec.Rsa.publicPrecompute`), computed by the verified
//! `vg_rsa_public_precompute` at the key's first operation, as OpenSSL and
//! AWS-LC set up their Montgomery values at a key's first operation: loading
//! a key only checks it.

use super::{Backend, scratch_words};
use alloc::{boxed::Box, vec, vec::Vec};
use core::{
    fmt, ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

use crate::arch::rsa::vg_rsa_public_precompute;
#[cfg(target_arch = "x86_64")]
use crate::arch::rsa::vg_rsa_public_precompute_adx;
use crate::cpu::detected;

/// The words of a modulus' precomputed values for an `n_len`-byte modulus
/// (`VG.Spec.Rsa.precomputedWords`).
pub(super) fn precomputed_words(n_len: usize) -> usize {
    2 * n_len.div_ceil(8)
}

/// Whether `n` is a modulus that `vg_rsa_public_precompute` accepts
/// (`VG.Spec.Rsa.modulusValid`): from 64 to 1024 bytes, odd, its first byte
/// not zero, and at least `2^511`, which for 64 bytes is a first byte of at
/// least `0x80`.
pub(super) fn modulus_valid(n: &[u8]) -> bool {
    let k = n.len();
    (64..=1024).contains(&k) && n[k - 1] & 1 == 1 && n[0] != 0 && (k > 64 || n[0] >= 0x80)
}

/// What `vg_rsa_public_precompute` writes for `n` and returns, computed in
/// `scratch`, which has at least `scratch_words(n.len())` words.
fn precompute(n: &[u8], scratch: &mut [u64]) -> (Vec<u64>, u32) {
    let k = n.len();
    assert!((64..=1024).contains(&k) && scratch.len() >= scratch_words(k));
    let mut pre = vec![0u64; precomputed_words(k)];
    let f = match Backend::select(detected()) {
        Backend::Baseline => vg_rsa_public_precompute,
        // `select` chose it because the CPU has the features it needs.
        #[cfg(target_arch = "x86_64")]
        Backend::Adx | Backend::Ifma => vg_rsa_public_precompute_adx,
    };
    // SAFETY: each pointer is valid for its length (`pre` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations (`scratch` borrowed exclusively); the check
    // above gives `64 ≤ n_len ≤ 1024` and `scratch_len ≥ 16 n_len`, and
    // `pre_len = 2 ⌈n_len / 8⌉`; and the CPU has the features of the
    // function `select` chose.
    let r = unsafe {
        f(
            pre.as_mut_ptr(),
            pre.len(),
            n.as_ptr(),
            k,
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    (pre, r)
}

/// The precomputed values of a key's modulus, once an operation has
/// computed them.
pub(crate) struct Precomputed(AtomicPtr<Vec<u64>>);

impl Precomputed {
    pub(super) fn new() -> Self {
        Self(AtomicPtr::new(ptr::null_mut()))
    }

    /// The values of `n`, a modulus that `modulus_valid` accepts and the
    /// same at every call, computed in `scratch` (at least
    /// `scratch_words(n.len())` words, left holding only values of `n`) if
    /// no call has yet.
    pub(crate) fn get(&self, n: &[u8], scratch: &mut [u64]) -> &[u64] {
        let pointer = self.0.load(Ordering::Acquire);
        if pointer.is_null() {
            let (pre, r) = precompute(n, scratch);
            // `vg_rsa_public_precompute` refuses only moduli that
            // `modulus_valid` refuses (`VG.Spec.Rsa.modulusValid`).
            assert_eq!(r, 1);
            self.install(pre)
        } else {
            // SAFETY: a pointer that is not null owns the `Box` that `install`
            // published, which is freed only when `self` is dropped.
            unsafe { &*pointer }
        }
    }

    /// `pre`, published as the values, or the values another call published
    /// first (computed from the same modulus).
    fn install(&self, pre: Vec<u64>) -> &[u64] {
        let ours = Box::into_raw(Box::new(pre));
        match self
            .0
            .compare_exchange(ptr::null_mut(), ours, Ordering::AcqRel, Ordering::Acquire)
        {
            // SAFETY: `ours` is published, and freed only when `self` is
            // dropped.
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
}

// The values are a function of the modulus: they do not contribute to a key's
// value, and a clone takes them if they are computed.
impl Clone for Precomputed {
    fn clone(&self) -> Self {
        let pointer = self.0.load(Ordering::Acquire);
        let clone = Self::new();
        if !pointer.is_null() {
            // SAFETY: as in `get`.
            clone.install(unsafe { &*pointer }.clone());
        }
        clone
    }
}
impl fmt::Debug for Precomputed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Precomputed")
    }
}
impl PartialEq for Precomputed {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for Precomputed {}

impl Drop for Precomputed {
    fn drop(&mut self) {
        let pointer = *self.0.get_mut();
        if !pointer.is_null() {
            // SAFETY: exclusive access to `self` excludes any borrow of the
            // values; a pointer that is not null owns the `Box` that
            // `install` published.
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

    /// An odd `k`-byte number with the first byte `first`.
    fn number(k: usize, first: u8) -> Vec<u8> {
        let mut n = vec![0x5a; k];
        n[0] = first;
        n[k - 1] = 0x5b;
        n
    }

    /// `modulus_valid` accepts exactly the moduli `vg_rsa_public_precompute`
    /// accepts, at the edges of each condition.
    #[test]
    fn validity_matches_precompute() {
        let mut even = number(65, 1);
        even[64] = 0x5a;
        let cases = [
            (number(64, 0x80), true),
            (number(64, 0x7f), false),
            (number(64, 0xff), true),
            (number(65, 1), true),
            (number(65, 0), false),
            (number(1024, 1), true),
            (number(1024, 0), false),
            (even, false),
        ];
        for (n, valid) in cases {
            assert_eq!(modulus_valid(&n), valid);
            let mut scratch = vec![0; scratch_words(n.len())];
            let (pre, r) = precompute(&n, &mut scratch);
            assert_eq!(r, u32::from(valid));
            assert_eq!(pre.iter().any(|&w| w != 0), valid);
        }
        for n in [vec![], number(63, 0x80), number(1025, 0x80)] {
            assert!(!modulus_valid(&n));
        }
    }

    #[test]
    fn computed_once_and_shared_by_clones() {
        let n = number(64, 0x80);
        let mut scratch = vec![0; scratch_words(64)];
        let pre = Precomputed::new();
        let empty = pre.clone();
        assert!(empty.0.load(Ordering::Relaxed).is_null());
        let values = pre.get(&n, &mut scratch).to_vec();
        assert_eq!(values, precompute(&n, &mut scratch).0);
        let first = pre.get(&n, &mut scratch).as_ptr();
        assert_eq!(pre.get(&n, &mut scratch).as_ptr(), first);
        let clone = pre.clone();
        assert!(!clone.0.load(Ordering::Relaxed).is_null());
        assert_eq!(clone.get(&n, &mut scratch), &values[..]);
        assert_eq!(empty.get(&n, &mut scratch), &values[..]);
        assert_eq!(pre, empty);
        assert_eq!(std::format!("{pre:?}"), "Precomputed");
    }

    /// A call that loses the race to publish its values takes the winner's.
    #[test]
    fn first_published_values_win() {
        let pre = Precomputed::new();
        let first = pre.install(vec![1, 2]).as_ptr();
        assert_eq!(pre.install(vec![3, 4]), &[1, 2]);
        assert_eq!(pre.install(vec![3, 4]).as_ptr(), first);
    }

    #[test]
    fn concurrent_first_operations_agree() {
        let n = number(128, 0xc5);
        let mut scratch = vec![0; scratch_words(128)];
        let expected = precompute(&n, &mut scratch).0;
        let pre = Precomputed::new();
        std::thread::scope(|scope| {
            for _ in 0..4 {
                scope.spawn(|| {
                    let mut scratch = vec![0; scratch_words(128)];
                    assert_eq!(pre.get(&n, &mut scratch), &expected[..]);
                });
            }
        });
    }
}
