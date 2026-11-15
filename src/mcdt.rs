//! Intel's mitigation of MXCSR-configuration-dependent timing (MCDT), on
//! x86-64: `vg_mcdt_enter` sets MXCSR's status flags, keeping its control
//! bits, so that it holds `0x1FBF` where the control bits are the default,
//! as Rust's are (`lean/VerifiedGarbage/Spec/Mcdt.lean`).
//!
//! For now this holds only a test that runs it on the CPU: the dispatchers
//! that call it, before the verified code that uses the instructions Intel
//! lists, come in the next change.

#![cfg(target_arch = "x86_64")]

#[cfg(test)]
mod tests {
    use crate::arch::dispatch::mcdt::vg_mcdt_enter_auto;
    use crate::dit::{Why, public};

    /// MXCSR, as `stmxcsr` stores it.
    #[allow(deprecated)]
    fn mxcsr() -> u32 {
        // SAFETY: `stmxcsr` reads MXCSR, which every x86-64 CPU has.
        unsafe { core::arch::x86_64::_mm_getcsr() }
    }

    /// With Rust's default control bits, entering leaves MXCSR `0x1FBF`
    /// and says so; entering again changes nothing.
    #[test]
    fn enter_default() {
        assert_eq!(mxcsr() & 0xFFC0, 0x1F80);
        for _ in 0..2 {
            // SAFETY: it takes no argument and writes no memory but its stack.
            assert_eq!(unsafe { vg_mcdt_enter_auto(public(Why::Test)) }, 1);
            assert_eq!(mxcsr(), 0x1FBF);
        }
    }
}
