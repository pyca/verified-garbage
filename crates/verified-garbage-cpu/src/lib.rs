//! The CPU features `verified-garbage` chooses among implementations by:
//! each feature's bit, sets of them, and their detection (`detected`). A
//! crate of its own so that the generated code's `_FEATURES` constants and
//! dispatchers, and the library (`src/cpu.rs`), name the same type and ask
//! the same detection.

#![no_std]

#[cfg(feature = "std")]
extern crate std;

// Public for the library's tests of it (`src/cpu.rs`), which CI runs with
// the library's: only `detected` and `requested` are this crate's interface.
#[doc(hidden)]
pub mod detect;

pub use detect::{detected, requested};

/// The bit of each feature detection knows in a [`Features`], by its Rust
/// `target_feature` name in uppercase: what the generated `_FEATURES`
/// constants, and the code choosing among implementations, are made of.
/// (Each target detects and uses only some of them.)
pub mod feature {
    pub const SSSE3: u32 = 1 << 0;
    pub const SHA: u32 = 1 << 1;
    pub const AES: u32 = 1 << 2;
    pub const PCLMULQDQ: u32 = 1 << 3;
    pub const AVX: u32 = 1 << 4;
    pub const AVX2: u32 = 1 << 5;
    pub const BMI1: u32 = 1 << 6;
    pub const BMI2: u32 = 1 << 7;
    pub const AVX512F: u32 = 1 << 8;
    pub const SHA512: u32 = 1 << 9;
    pub const SHA2: u32 = 1 << 10;
    pub const SHA3: u32 = 1 << 11;
    pub const ADX: u32 = 1 << 12;
    pub const AVX512IFMA: u32 = 1 << 13;
    pub const AVX512VL: u32 = 1 << 14;
    pub const NEON: u32 = 1 << 15;
    pub const SVE2: u32 = 1 << 16;
    pub const VAES: u32 = 1 << 17;
    pub const VPCLMULQDQ: u32 = 1 << 18;
    pub const AVX512BW: u32 = 1 << 19;
    pub const UMAAL: u32 = 1 << 20;
    pub const DIT: u32 = 1 << 21;
}

/// A set of CPU features.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Features(pub u32);

impl Features {
    /// The features in any of `sets`.
    pub const fn all(sets: &[Features]) -> Features {
        let mut acc = 0;
        let mut i = 0;
        while i < sets.len() {
            acc |= sets[i].0;
            i += 1;
        }
        Features(acc)
    }

    /// Whether every feature of `other` is in `self`.
    pub const fn contains(self, other: Features) -> bool {
        self.0 & other.0 == other.0
    }
}

/// Proof, for the lifetime `'a`, that the current thread has seen to data
/// independent timing: on AArch64, that PSTATE.DIT is on wherever the CPU
/// has it (FEAT_DIT), under which Arm guarantees the timing of the
/// data-independent-time instructions that the proofs' leakage model
/// assumes; or that what it is passed to handles only public data, whose
/// timing may depend on it.
///
/// Every verified function takes one first, so the compiler checks that
/// every path into the verified code, through a function pointer too,
/// starts from code that made one. It is a zero-sized value: passing it
/// costs nothing, and the verified functions do not read it.
///
/// It is neither `Send` nor `Sync`, as PSTATE.DIT is a thread's own.
#[derive(Clone, Copy, Debug)]
pub struct Dit<'a>(core::marker::PhantomData<(&'a (), *const ())>);

impl Dit<'_> {
    /// A token, by the caller's word.
    ///
    /// # Safety
    ///
    /// For as long as the token lives, the current thread must have data
    /// independent timing on wherever the CPU has it (on AArch64,
    /// PSTATE.DIT, FEAT_DIT), or every input of the verified functions it
    /// is passed to must be public.
    #[doc(hidden)]
    #[inline(always)]
    pub const unsafe fn assume() -> Self {
        Dit(core::marker::PhantomData)
    }
}
