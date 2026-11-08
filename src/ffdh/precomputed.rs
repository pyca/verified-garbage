//! A domain's public key-generation data, computed once after the domain is
//! checked.

// Verified code writes the representation and its metadata: the Rust neither
// recognizes groups nor derives an exponent width from private bytes.

use crate::arch::dispatch::ffdh::vg_ffdh_generate_key_precompute_auto;
use alloc::sync::Arc;

/// Canonical `VG.Spec.Ffdh.generationPrecompute` words shared by every clone.
#[derive(Clone, Debug)]
pub(super) struct Precomputed(Arc<[u64]>);

impl Precomputed {
    pub(super) fn new(
        dit: crate::dit::Dit<'_>,
        domain: &[u8],
        p_len: usize,
        scratch: &mut [u64],
    ) -> Self {
        let mut words = alloc::vec![0; 3 + 34 * p_len.div_ceil(8)];
        // SAFETY: the domain was accepted by vg_ffdh_check_domain. Its
        // length is 2*p_len or 3*p_len, p_len is in 64..=1024, words has
        // exactly 3+34*ceil(p_len/8) entries and scratch has at least
        // 16*p_len+32 words. These are disjoint Rust allocations. The
        // dispatcher calls only an implementation the CPU has the features of.
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
        Self(words.into())
    }

    pub(super) fn words(&self) -> &[u64] {
        &self.0
    }

    /// Public maximum encoding length, not the private scalar's actual length.
    pub(super) fn exponent_len(&self) -> usize {
        self.0[1] as usize
    }

    #[cfg(test)]
    pub(super) fn shares_allocation(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
