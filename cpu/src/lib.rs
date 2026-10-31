//! The CPU features `verified-garbage` chooses among implementations by:
//! their names, and sets of them. A crate of its own so that the generated
//! code's `_FEATURES` constants and the library's feature detection
//! (`src/cpu.rs`, which re-exports all of this) name the same type.

#![no_std]

/// The features detection knows, by their Rust `target_feature` names: bit
/// `i` of a [`Features`] is `NAMES[i]`.
pub const NAMES: [&str; 21] = [
    "ssse3",
    "sha",
    "aes",
    "pclmulqdq",
    "avx",
    "avx2",
    "bmi1",
    "bmi2",
    "avx512f",
    "sha512",
    "sha2",
    "sha3",
    "adx",
    "avx512ifma",
    "avx512vl",
    "neon",
    "sve2",
    "vaes",
    "vpclmulqdq",
    "avx512bw",
    "umaal",
];

/// The bit of the feature `name` in a [`Features`]: its index in [`NAMES`],
/// which [`Features::of`] checks. A `match`, which the compiler evaluates in
/// a few steps, rather than a search of [`NAMES`]: evaluating the generated
/// `_FEATURES` constants by searching took a second of every build of the
/// crate.
const fn bit(name: &str) -> usize {
    match name.as_bytes() {
        b"ssse3" => 0,
        b"sha" => 1,
        b"aes" => 2,
        b"pclmulqdq" => 3,
        b"avx" => 4,
        b"avx2" => 5,
        b"bmi1" => 6,
        b"bmi2" => 7,
        b"avx512f" => 8,
        b"sha512" => 9,
        b"sha2" => 10,
        b"sha3" => 11,
        b"adx" => 12,
        b"avx512ifma" => 13,
        b"avx512vl" => 14,
        b"neon" => 15,
        b"sve2" => 16,
        b"vaes" => 17,
        b"vpclmulqdq" => 18,
        b"avx512bw" => 19,
        b"umaal" => 20,
        _ => panic!("a CPU feature this library does not know"),
    }
}

/// The bit of each feature of [`NAMES`] in a [`Features`], by its name in
/// uppercase (`.` and other characters not allowed in a name as `_`): what
/// the generated `_FEATURES` constants are made of, `Features(feature::AVX |
/// feature::AVX2)`. rustc evaluates every constant of the crate, and an `|`
/// of these takes it a few steps, where [`Features::of`] on the names, which
/// these constants once called, took it a tenth of a build of the crate.
pub mod feature {
    pub const SSSE3: u32 = 1 << super::bit("ssse3");
    pub const SHA: u32 = 1 << super::bit("sha");
    pub const AES: u32 = 1 << super::bit("aes");
    pub const PCLMULQDQ: u32 = 1 << super::bit("pclmulqdq");
    pub const AVX: u32 = 1 << super::bit("avx");
    pub const AVX2: u32 = 1 << super::bit("avx2");
    pub const BMI1: u32 = 1 << super::bit("bmi1");
    pub const BMI2: u32 = 1 << super::bit("bmi2");
    pub const AVX512F: u32 = 1 << super::bit("avx512f");
    pub const SHA512: u32 = 1 << super::bit("sha512");
    pub const SHA2: u32 = 1 << super::bit("sha2");
    pub const SHA3: u32 = 1 << super::bit("sha3");
    pub const ADX: u32 = 1 << super::bit("adx");
    pub const AVX512IFMA: u32 = 1 << super::bit("avx512ifma");
    pub const AVX512VL: u32 = 1 << super::bit("avx512vl");
    pub const NEON: u32 = 1 << super::bit("neon");
    pub const SVE2: u32 = 1 << super::bit("sve2");
    pub const VAES: u32 = 1 << super::bit("vaes");
    pub const VPCLMULQDQ: u32 = 1 << super::bit("vpclmulqdq");
    pub const AVX512BW: u32 = 1 << super::bit("avx512bw");
    pub const UMAAL: u32 = 1 << super::bit("umaal");
}

/// Whether two names are equal (`==` on strings, which is not `const`).
const fn eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    let mut same = a.len() == b.len();
    let mut i = 0;
    while same && i < a.len() {
        same = a[i] == b[i];
        i += 1;
    }
    same
}

/// A set of CPU features.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Features(pub u32);

impl Features {
    /// The features named in `names` (as each generated `_FEATURES`
    /// constant is made). A `const fn`, so that choosing an implementation
    /// can compare precomputed sets rather than names.
    ///
    /// # Panics
    ///
    /// If `names` has a feature not in [`NAMES`], which detection does not
    /// know. In a constant (`const { Features::of(…) }`), that fails to
    /// compile, rather than quietly never choosing the code that needs it.
    pub const fn of(names: &[&str]) -> Features {
        let mut acc = 0;
        let mut i = 0;
        while i < names.len() {
            let j = bit(names[i]);
            assert!(eq(names[i], NAMES[j]));
            acc |= 1 << j;
            i += 1;
        }
        Features(acc)
    }

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
