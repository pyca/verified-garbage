//! The CPU features `verified-garbage` chooses among implementations by:
//! each feature's bit, sets of them, and their detection (`detected`). A
//! crate of its own so that the generated code's `_FEATURES` constants and
//! dispatchers, and the library (`src/cpu.rs`), name the same type and ask
//! the same detection.

#![no_std]

#[cfg(feature = "std")]
extern crate std;

// Public for the library's tests of it (`src/cpu.rs`), which CI runs with
// the library's: only `detected`, `requested` and `known` are this crate's
// interface.
#[doc(hidden)]
pub mod detect;

pub use detect::{Known, detected, known, requested};

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
