//! The values of a private key that its operations take
//! (`VG.Spec.Rsa.privatePrecompute`), computed by the verified
//! `vg_rsa_private_precompute` at the key's first private operation, as
//! [`Precomputed`](super::precomputed) does for a public key: loading a key
//! only checks it. They include `R_p mod p` and `R_q mod q`, secrets of the
//! key, and are wiped when the key is dropped.

#![cfg(target_arch = "x86_64")]

use alloc::{boxed::Box, vec, vec::Vec};
use core::{
    ptr,
    sync::atomic::{AtomicPtr, Ordering},
};

use super::precomputed::precomputed_words;
use super::scratch_words;
use crate::arch::rsa::vg_rsa_private_precompute;

/// The words of a prime factor's value for a `len`-byte factor
/// (`VG.Spec.Rsa.primeWords`).
fn prime_words(len: usize) -> usize {
    len.div_ceil(8).max(2)
}

/// The words of a private key's precomputed values for an `n_len`-byte
/// modulus and `p_len`- and `q_len`-byte factors
/// (`VG.Spec.Rsa.privatePrecomputedWords`).
pub(super) fn private_precomputed_words(n_len: usize, p_len: usize, q_len: usize) -> usize {
    precomputed_words(n_len) + prime_words(p_len) + prime_words(q_len)
}

/// What `vg_rsa_private_precompute` writes for `(n, p, q)` and returns,
/// computed in `scratch`, which has at least `scratch_words(n.len())` words.
fn precompute(n: &[u8], p: &[u8], q: &[u8], scratch: &mut [u64]) -> (Vec<u64>, u32) {
    let k = n.len();
    assert!(
        (64..=1024).contains(&k)
            && (1..k).contains(&p.len())
            && (1..k).contains(&q.len())
            && scratch.len() >= scratch_words(k)
    );
    let mut pre = vec![0u64; private_precomputed_words(k, p.len(), q.len())];
    // SAFETY: each pointer is valid for its length (`pre` and `scratch` for
    // writes), and none overlaps another or wraps around, as they are
    // distinct Rust allocations (`scratch` borrowed exclusively); the check
    // above gives `64 ≤ n_len ≤ 1024`, `1 ≤ p_len < n_len`,
    // `1 ≤ q_len < n_len` and `scratch_len ≥ 16 n_len + 32`, and `pre_len`
    // is `private_precomputed_words(n_len, p_len, q_len)`.
    let r = unsafe {
        vg_rsa_private_precompute(
            pre.as_mut_ptr(),
            pre.len(),
            n.as_ptr(),
            k,
            p.as_ptr(),
            p.len(),
            q.as_ptr(),
            q.len(),
            scratch.as_mut_ptr(),
            scratch.len(),
        )
    };
    (pre, r)
}

/// A private key's precomputed values, once an operation has computed them.
pub(crate) struct PrivatePrecomputed(AtomicPtr<Vec<u64>>);

impl PrivatePrecomputed {
    pub(super) fn new() -> Self {
        Self(AtomicPtr::new(ptr::null_mut()))
    }

    /// The values of `(n, p, q)`, a key that `vg_rsa_check_crt_key`
    /// accepted (so a valid modulus with `p q = n`), the same at every call,
    /// computed in `scratch` (at least `scratch_words(n.len())` words, which
    /// then hold the key's values) if no call has yet.
    pub(crate) fn get(&self, n: &[u8], p: &[u8], q: &[u8], scratch: &mut [u64]) -> &[u64] {
        let pointer = self.0.load(Ordering::Acquire);
        if pointer.is_null() {
            let (pre, r) = precompute(n, p, q, scratch);
            // `vg_rsa_private_precompute` refuses only invalid moduli and
            // factors whose product is not `n`, which `vg_rsa_check_crt_key`
            // refuses.
            assert_eq!(r, 1);
            self.install(pre)
        } else {
            // SAFETY: a pointer that is not null owns the `Box` that `install`
            // published, which is freed only when `self` is dropped.
            unsafe { &*pointer }
        }
    }

    /// `pre`, published as the values, or the values another call published
    /// first (computed from the same key), wiping `pre` then.
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
                    let mut ours = Box::from_raw(ours);
                    crate::zeroize::zeroize(&mut ours[..]);
                    &*theirs
                }
            }
        }
    }
}

impl Drop for PrivatePrecomputed {
    fn drop(&mut self) {
        let pointer = *self.0.get_mut();
        if !pointer.is_null() {
            // SAFETY: exclusive access to `self` excludes any borrow of the
            // values; a pointer that is not null owns the `Box` that
            // `install` published.
            let mut pre = unsafe { Box::from_raw(pointer) };
            crate::zeroize::zeroize(&mut pre[..]);
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::rsa::tests::composite_key;

    #[test]
    fn computed_once() {
        let (key, _) = composite_key();
        let [n, _, _, p, q, ..] = key.components();
        let mut scratch = vec![0; scratch_words(n.len())];
        let pre = PrivatePrecomputed::new();
        let values = pre.get(n, p, q, &mut scratch).to_vec();
        assert_eq!(values, precompute(n, p, q, &mut scratch).0);
        assert_eq!(
            values.len(),
            private_precomputed_words(n.len(), p.len(), q.len())
        );
        let first = pre.get(n, p, q, &mut scratch).as_ptr();
        assert_eq!(pre.get(n, p, q, &mut scratch).as_ptr(), first);
    }

    /// A call that loses the race to publish its values takes the winner's.
    #[test]
    fn first_published_values_win() {
        let pre = PrivatePrecomputed::new();
        let first = pre.install(vec![1, 2]).as_ptr();
        assert_eq!(pre.install(vec![3, 4]), &[1, 2]);
        assert_eq!(pre.install(vec![3, 4]).as_ptr(), first);
    }

    /// The factors' words: at least 2, as `vg_rsa_private_precompute` lays
    /// them out.
    #[test]
    fn words() {
        assert_eq!(prime_words(1), 2);
        assert_eq!(prime_words(16), 2);
        assert_eq!(prime_words(17), 3);
        assert_eq!(private_precomputed_words(256, 128, 128), 64 + 16 + 16);
    }

    #[test]
    fn concurrent_first_operations_agree() {
        let (key, _) = composite_key();
        let [n, _, _, p, q, ..] = key.components();
        let mut scratch = vec![0; scratch_words(n.len())];
        let expected = precompute(n, p, q, &mut scratch).0;
        let pre = PrivatePrecomputed::new();
        std::thread::scope(|scope| {
            for _ in 0..4 {
                scope.spawn(|| {
                    let mut scratch = vec![0; scratch_words(n.len())];
                    assert_eq!(pre.get(n, p, q, &mut scratch), &expected[..]);
                });
            }
        });
    }
}
