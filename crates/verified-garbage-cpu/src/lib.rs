//! The CPU features `verified-garbage` chooses among implementations by:
//! each feature's bit, and sets of them. A crate of its own so that the
//! generated code's `_FEATURES` constants and the library's feature
//! detection (`src/cpu.rs`, which re-exports all of this) name the same
//! type.

#![no_std]

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
    pub fn contains(self, other: Features) -> bool {
        self.0 & other.0 == other.0
    }
}
