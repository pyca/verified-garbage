//! Data independent timing (on AArch64, PSTATE.DIT, FEAT_DIT): Arm
//! guarantees the timing of the data-independent-time instructions, which
//! the proofs' leakage model assumes, only while it is on.
//!
//! The verified functions `vg_dit_enter` and `vg_dit_clear` turn it on and
//! off (`lean/VerifiedGarbage/Spec/Dit.lean`, and their effect on it,
//! `VG.Proof.Dit.AArch64.enter_dit` and `clear_dit`). For now only these
//! tests call them: they check on the CPU what the model says they do.

#![cfg(all(test, target_arch = "aarch64"))]

mod tests {
    use crate::arch::dit::{VG_DIT_ENTER_FEATURES, vg_dit_clear, vg_dit_enter};

    /// Entering turns the mode on and reports what it was; clearing turns
    /// it off. This changes PSTATE.DIT of the test's thread alone, and
    /// leaves it off.
    #[test]
    fn enter_and_clear() {
        if !verified_garbage_cpu::detected().contains(VG_DIT_ENTER_FEATURES) {
            return;
        }
        // SAFETY: the CPU has FEAT_DIT, as both functions require
        // (`VG_DIT_CLEAR_FEATURES` is the same set).
        unsafe {
            vg_dit_enter();
            assert_eq!(vg_dit_enter(), 1);
            vg_dit_clear();
            assert_eq!(vg_dit_enter(), 0);
            assert_eq!(vg_dit_enter(), 1);
            vg_dit_clear();
        }
    }
}
