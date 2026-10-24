//! Immutable public key-generation data, initialized once after domain checking.
//! The representation and metadata are written by verified code; Rust neither
//! recognizes groups nor derives an exponent width from private bytes.

use super::arithmetic::Backend;
use crate::cpu::detected;
use alloc::sync::Arc;

/// Canonical `VG.Spec.Ffdh.generationPrecompute` words shared by every clone.
#[derive(Clone, Debug)]
pub(super) struct Precomputed(Arc<[u64]>);

impl Precomputed {
    pub(super) fn new(domain: &[u8], p_len: usize, scratch: &mut [u64]) -> Self {
        Self::new_with_backend(domain, p_len, scratch, Backend::ffdh(detected()))
    }

    pub(super) fn new_with_backend(
        domain: &[u8],
        p_len: usize,
        scratch: &mut [u64],
        backend: Backend,
    ) -> Self {
        let mut words = alloc::vec![0; 3 + 34 * p_len.div_ceil(8)];
        let f = match backend {
            Backend::Baseline => crate::arch::ffdh::vg_ffdh_generate_key_precompute,
            #[cfg(target_arch = "arm")]
            Backend::Umaal => crate::arch::ffdh::vg_ffdh_generate_key_precompute_umaal,
        };
        // SAFETY: the domain was accepted by vg_ffdh_check_domain. Its
        // length is 2*p_len or 3*p_len, p_len is in 64..=1024, words has
        // exactly 3+34*ceil(p_len/8) entries and scratch has at least
        // 16*p_len+32 words. These are disjoint Rust allocations. Backend
        // selection ensures the CPU has the generated function's features.
        let ok = unsafe {
            f(
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
