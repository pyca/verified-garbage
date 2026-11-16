//! Intel's mitigation of MXCSR-configuration-dependent timing (MCDT), on
//! x86-64: `vg_mcdt_enter` sets MXCSR's status flags, keeping its control
//! bits, so that it holds `0x1FBF` where the control bits are the default,
//! as Rust's are (`lean/VerifiedGarbage/Spec/Mcdt.lean`).
//!
//! The generated dispatcher of every function whose code has an
//! instruction Intel lists runs it first, and panics unless MXCSR then holds
//! `0x1FBF` (`verified_garbage_cpu::mcdt_entered`; "Dispatchers" in
//! `lean/VerifiedGarbage/TCB/Rust.lean`), unless its code calls it itself
//! before them (`Rust.mcdtOpen`: Poly1305's update). This holds their tests.

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

    /// Poly1305's vector code calls `vg_mcdt_enter` itself, so its dispatcher
    /// does not: where MXCSR's control bits are not the default (here with
    /// FTZ set), `vg_mcdt_enter` returns 0 and the code absorbs every block
    /// with the scalar code instead, giving the same tag, and leaves the
    /// control bits as they were.
    #[test]
    #[allow(deprecated)]
    fn poly1305_other_control_bits() {
        let key = [7u8; 32];
        let data = [0x5au8; 1024];
        let tag = crate::poly1305::Poly1305::mac(&key, &data);
        let saved = mxcsr();
        // SAFETY: `ldmxcsr` of MXCSR with FTZ set, which no code of this test
        // depends on; restored below.
        unsafe { core::arch::x86_64::_mm_setcsr(saved | 0x8000) };
        let other = crate::poly1305::Poly1305::mac(&key, &data);
        let after = mxcsr();
        // SAFETY: restores the MXCSR read above.
        unsafe { core::arch::x86_64::_mm_setcsr(saved) };
        assert_eq!(tag, other);
        assert_eq!(after & 0xFFC0, (saved | 0x8000) & 0xFFC0);
    }

    /// A dispatcher panics where `vg_mcdt_enter` reports that MXCSR is not
    /// `0x1FBF`, which it does where its control bits are not the default.
    #[test]
    #[should_panic(expected = "MXCSR's control bits are not the default")]
    fn other_control_bits_panic() {
        verified_garbage_cpu::mcdt_entered(0);
    }
}
