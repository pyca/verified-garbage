//! Detecting the CPU features: the code that the generated dispatchers
//! (`detected`, `requested`) and the library (`src/cpu.rs`) ask, and that the
//! library's tests test. Only `detected` and `requested` are its interface.

// A function that needs features beyond its target's baseline ISA has a
// generated `<NAME>_FEATURES` constant of them, which Lean checks, and may only
// be called on a CPU with all of them. They are detected once: with `cpuid` on
// x86 and x86-64; on AArch64, from the operating system with the `std`
// feature, and otherwise from the target features compiled for; on ARMv7, from
// the operating system compiled for (`umaal`, on those that run on A-profile
// cores alone). Each object chooses its implementation when it is created. A
// feature without a bit in `feature` cannot be named in a constant, so cannot
// be checked for by mistake.
//
// With the `env` Cargo feature (which the library's `cpu-features-env`
// enables), `VG_CPU_FEATURES` (`none`, or names from `NAMES`
// separated by commas) restricts the features detected, so that tests and
// benchmarks run every implementation on one machine. It can only remove
// features, and panics on a name this library does not know or the CPU does
// not have, rather than quietly test another configuration. On x86 and x86-64,
// BMI2 and ADX are detected only with AVX2, which every CPU that has them has,
// so naming either without `avx2` panics too. On AArch64 targets
// other than Apple's, the SHA-3 functions run FEAT_SHA3's Keccak only when it
// names `sha3` (`hashes::sha3::Backend::detected`).

use core::sync::atomic::{AtomicU64, Ordering};

use crate::Features;
// Each target uses only some of the features' bits, and some none.
#[allow(unused_imports)]
use crate::feature;

/// Each feature's name and bit, for reading `VG_CPU_FEATURES` and for the
/// tests: bit `i` is `NAMES[i]`'s.
pub const NAMES: [(&str, u32); 23] = [
    ("ssse3", feature::SSSE3),
    ("sha", feature::SHA),
    ("aes", feature::AES),
    ("pclmulqdq", feature::PCLMULQDQ),
    ("avx", feature::AVX),
    ("avx2", feature::AVX2),
    ("bmi1", feature::BMI1),
    ("bmi2", feature::BMI2),
    ("avx512f", feature::AVX512F),
    ("sha512", feature::SHA512),
    ("sha2", feature::SHA2),
    ("sha3", feature::SHA3),
    ("adx", feature::ADX),
    ("avx512ifma", feature::AVX512IFMA),
    ("avx512vl", feature::AVX512VL),
    ("neon", feature::NEON),
    ("sve2", feature::SVE2),
    ("vaes", feature::VAES),
    ("vpclmulqdq", feature::VPCLMULQDQ),
    ("avx512bw", feature::AVX512BW),
    ("umaal", feature::UMAAL),
    ("dit", feature::DIT),
    ("sb", feature::SB),
];

/// The detected features, with [`DETECTED_INIT`] set once they are known,
/// and in the upper half the features `VG_CPU_FEATURES` names (`named`): one
/// word, so that a thread that sees the one sees the other.
static DETECTED: AtomicU64 = AtomicU64::new(0);
const DETECTED_INIT: u64 = 1 << 30;

/// The features of this CPU, restricted by `VG_CPU_FEATURES` (see the
/// comment at the top of this file). (Detection is idempotent, so threads
/// racing to do it store the same value, and `Relaxed` is enough.)
///
/// Inlined, it is a load and a test once detection has run; the detection
/// itself is out of line (`detect`), so callers keep no registers for it.
#[inline]
pub fn detected() -> Features {
    Features(state() as u32 & !(DETECTED_INIT as u32))
}

/// Whether `VG_CPU_FEATURES` names every feature of `f`, which is not empty:
/// never without the `env` Cargo feature, or if it is unset, empty or
/// `none`. A dispatcher that chooses an implementation only for some
/// compilation targets also chooses it where this says the tests ask for
/// it (`lean/VerifiedGarbage/TCB/Rust.lean`, `Rank.vendor`).
#[inline]
pub fn requested(f: Features) -> bool {
    f.0 != 0 && (state() >> 32) as u32 & f.0 == f.0
}

/// `DETECTED`, detected if it was not yet.
#[inline]
fn state() -> u64 {
    let s = DETECTED.load(Ordering::Relaxed);
    if s & DETECTED_INIT == 0 { detect() } else { s }
}

/// Detects the features, records them for `detected` and returns them, with
/// `DETECTED_INIT` set.
#[cold]
#[inline(never)]
fn detect() -> u64 {
    let runtime = runtime();
    let s = u64::from(runtime & allowed(runtime)) | DETECTED_INIT | (u64::from(named()) << 32);
    DETECTED.store(s, Ordering::Relaxed);
    s
}

/// The features `VG_CPU_FEATURES` names.
#[cfg(feature = "env")]
fn named() -> u32 {
    named_by(&std::env::var("VG_CPU_FEATURES").unwrap_or_default())
}

/// The features `names`, a value of `VG_CPU_FEATURES`, names: none if it is
/// empty or `none` (`allowed_by` rejects any other it cannot parse).
#[cfg(feature = "env")]
pub fn named_by(names: &str) -> u32 {
    if names.is_empty() {
        0
    } else {
        parse(names).unwrap_or(0)
    }
}

/// None: without the `env` Cargo feature, nothing names features.
#[cfg(not(feature = "env"))]
fn named() -> u32 {
    0
}

/// The features `VG_CPU_FEATURES` allows on a CPU with the features
/// `runtime`.
///
/// # Panics
///
/// As [`allowed_by`].
#[cfg(feature = "env")]
pub fn allowed(runtime: u32) -> u32 {
    allowed_by(
        &std::env::var("VG_CPU_FEATURES").unwrap_or_default(),
        runtime,
    )
}

/// The features `names`, a value of `VG_CPU_FEATURES`, allows on a CPU with
/// the features `runtime`.
///
/// # Panics
///
/// If it names a feature not in [`NAMES`], or one the CPU does not have:
/// that would test or benchmark another configuration than the one named
/// (`ci/bench_compare.py` reports a benchmark run that stops here as not
/// measured).
#[cfg(feature = "env")]
pub fn allowed_by(names: &str, runtime: u32) -> u32 {
    let allowed =
        parse(names).expect("VG_CPU_FEATURES names a CPU feature this library does not know");
    // Empty, it names none, though it allows every one.
    let lacking = if names.is_empty() {
        0
    } else {
        allowed & !runtime
    };
    if lacking != 0 {
        let lacking: std::vec::Vec<&str> = (NAMES.iter())
            .filter(|(_, bit)| lacking & bit != 0)
            .map(|(name, _)| *name)
            .collect();
        panic!(
            "VG_CPU_FEATURES names {}, which this CPU does not have",
            lacking.join(",")
        );
    }
    // `decode` reports BMI2 and ADX only with AVX2, so naming either without
    // `avx2` asks for a configuration no CPU can have.
    if !names.is_empty()
        && allowed & (feature::BMI2 | feature::ADX) != 0
        && allowed & feature::AVX2 == 0
    {
        panic!("VG_CPU_FEATURES names bmi2 or adx without avx2, which no CPU has");
    }
    allowed
}

/// Every feature: without the `cpu-features-env` Cargo feature, nothing
/// restricts them.
#[cfg(not(feature = "env"))]
pub fn allowed(_: u32) -> u32 {
    u32::MAX
}

/// The features a value of `VG_CPU_FEATURES` allows (every one if it is
/// empty, none if it is `none`), or `None` if it names an unknown one.
#[cfg(feature = "env")]
pub fn parse(names: &str) -> Option<u32> {
    match names {
        "" => Some(u32::MAX),
        "none" => Some(0),
        _ => names.split(',').try_fold(0, |acc, n| {
            NAMES
                .iter()
                .find(|(m, _)| *m == n)
                .map(|(_, bit)| acc | bit)
        }),
    }
}

/// Asks the CPU (Intel SDM Vol. 2A, CPUID: leaf 1 ECX bit 9 is SSSE3, bit 25
/// AES, bit 1 PCLMULQDQ, bit 27 OSXSAVE and bit 28 AVX; leaf 7 sub-leaf 0 EBX
/// bit 29 is SHA, bit 5 AVX2, bit 3 BMI1, bit 8 BMI2, bit 16 AVX512F, bit 19
/// ADX, bit 21 AVX512_IFMA and bit 31 AVX512VL, its ECX bit 9 VAES and bit 10
/// VPCLMULQDQ, and its EAX the highest sub-leaf; leaf 7 sub-leaf 1 EAX bit 0
/// is SHA512; AMD reports them in the same bits). AVX, AVX2, SHA512, VAES and
/// VPCLMULQDQ (whose instructions are VEX.256-encoded, so also need AVX,
/// Intel SDM Vol. 2, "VSHA512RNDS2", "AESENC" and "PCLMULQDQ") also need the
/// operating system to save the `ymm` registers: XCR0 bits 1 and 2, read with
/// `xgetbv` only if OSXSAVE says it may be (Intel SDM Vol. 1, §14.3,
/// "Detection of Intel AVX Instructions"); AVX512F, AVX512_IFMA, AVX512VL and AVX512BW (whose instructions
/// are EVEX-encoded) also need the opmask and `zmm` state, XCR0 bits 5, 6 and 7
/// (§15.2, "Detection of AVX-512 Foundation Instructions", and §15.4 for the
/// other AVX-512 instruction groups).
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn runtime() -> u32 {
    #[cfg(target_arch = "x86")]
    use core::arch::x86::{__cpuid_count, _xgetbv};
    #[cfg(target_arch = "x86_64")]
    use core::arch::x86_64::{__cpuid_count, _xgetbv};
    // SAFETY: the i686 and x86-64 target baselines have `cpuid`, and leaves
    // 0 and 1; `decode` reads leaf 7 only if leaf 0 says it exists (and its
    // sub-leaf 1 only if sub-leaf 0 says that exists), and `xgetbv` only if
    // OSXSAVE says the operating system has enabled it.
    #[allow(unused_unsafe)]
    decode(
        |leaf, sub| {
            let r = unsafe { __cpuid_count(leaf, sub) };
            [r.eax, r.ebx, r.ecx, r.edx]
        },
        || unsafe { _xgetbv(0) },
    )
}

/// The features of a CPU whose `cpuid` (of a leaf and sub-leaf, as `[eax,
/// ebx, ecx, edx]`) and `xgetbv(0)` return these, as [`runtime`] reads
/// them: apart from the instructions, so that the tests run it on CPUs
/// without leaf 7 too.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn decode(cpuid: impl Fn(u32, u32) -> [u32; 4], xgetbv: impl Fn() -> u64) -> u32 {
    let max = cpuid(0, 0)[0];
    let ecx = cpuid(1, 0)[2];
    let ssse3 = (ecx >> 9) & 1;
    let aes = (ecx >> 25) & 1;
    let pclmulqdq = (ecx >> 1) & 1;
    let osxsave = (ecx >> 27) & 1 == 1;
    let xcr0 = if osxsave { xgetbv() } else { 0 };
    let ymm = u32::from(xcr0 & 0b110 == 0b110);
    let zmm = u32::from(xcr0 & 0b1110_0110 == 0b1110_0110);
    let avx = (ecx >> 28) & ymm;
    let [sub, ebx, ecx7, _] = if max >= 7 { cpuid(7, 0) } else { [0; 4] };
    let eax1 = if max >= 7 && sub >= 1 {
        cpuid(7, 1)[0]
    } else {
        0
    };
    let sha = (ebx >> 29) & 1;
    let avx2 = (ebx >> 5) & avx;
    let bmi1 = (ebx >> 3) & 1;
    // BMI2 and ADX only with AVX2: no CPU has them without it (Intel's
    // came with Haswell's AVX2 and Broadwell, AMD's with Zen), so only a
    // virtual machine or an operating system hiding AVX2 does, and it gets
    // the baseline code rather than configurations of its own to test.
    let bmi2 = (ebx >> 8) & avx2;
    let avx512f = (ebx >> 16) & avx & zmm;
    let sha512 = eax1 & avx;
    let adx = (ebx >> 19) & avx2;
    let avx512ifma = (ebx >> 21) & avx & zmm;
    let avx512vl = (ebx >> 31) & avx & zmm;
    let vaes = (ecx7 >> 9) & avx;
    let vpclmulqdq = (ecx7 >> 10) & avx;
    let avx512bw = (ebx >> 30) & avx & zmm;
    (ssse3 * feature::SSSE3)
        | (sha * feature::SHA)
        | (aes * feature::AES)
        | (pclmulqdq * feature::PCLMULQDQ)
        | (avx * feature::AVX)
        | (avx2 * feature::AVX2)
        | (bmi1 * feature::BMI1)
        | (bmi2 * feature::BMI2)
        | (avx512f * feature::AVX512F)
        | (sha512 * feature::SHA512)
        | (adx * feature::ADX)
        | (avx512ifma * feature::AVX512IFMA)
        | (avx512vl * feature::AVX512VL)
        | (vaes * feature::VAES)
        | (vpclmulqdq * feature::VPCLMULQDQ)
        | (avx512bw * feature::AVX512BW)
}

/// AArch64 feature groups, using the same Rust names as the generated
/// artifacts: `aes` covers FEAT_AES and FEAT_PMULL, `sha2` covers FEAT_SHA1
/// and FEAT_SHA256, `sha3` covers FEAT_SHA512 and FEAT_SHA3, `sve2` is
/// FEAT_SVE2, `dit` is FEAT_DIT (data independent timing, PSTATE.DIT), and
/// `sb` is FEAT_SB (the speculation barrier SB).
#[cfg(target_arch = "aarch64")]
pub fn runtime() -> u32 {
    (u32::from(aarch64_aes()) * feature::AES)
        | (u32::from(aarch64_sha2()) * feature::SHA2)
        | (u32::from(aarch64_sha3()) * feature::SHA3)
        | (u32::from(aarch64_sve2()) * feature::SVE2)
        | (u32::from(aarch64_dit()) * feature::DIT)
        | (u32::from(aarch64_sb()) * feature::SB)
        // AdvSIMD is the AArch64 baseline used by the verified ISA.
        // Keep a mask bit so tests and benchmarks can turn off the variants
        // that name it.
        | feature::NEON
}

/// Whether the CPU has FEAT_AES and FEAT_PMULL, asked of the operating
/// system through `std`, which the `std` feature links.
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_aes() -> bool {
    std::arch::is_aarch64_feature_detected!("aes")
}

/// Whether the compiler was told every CPU running this code has FEAT_AES
/// and FEAT_PMULL (as `aarch64-apple-darwin` and `-C target-feature=+aes`
/// do): without `std`, this `no_std` crate cannot ask the operating system.
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_aes() -> bool {
    cfg!(target_feature = "aes")
}

/// Whether both SHA-1 and SHA-256 instructions are available.
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_sha2() -> bool {
    std::arch::is_aarch64_feature_detected!("sha2")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_sha2() -> bool {
    cfg!(target_feature = "sha2")
}

/// Whether both SHA-512 and SHA-3 instructions are available.
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_sha3() -> bool {
    std::arch::is_aarch64_feature_detected!("sha3")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_sha3() -> bool {
    cfg!(target_feature = "sha3")
}

/// Whether the CPU has FEAT_SVE2, asked of the operating system (which also
/// says whether it has enabled SVE for this process).
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_sve2() -> bool {
    std::arch::is_aarch64_feature_detected!("sve2")
}

/// Without `std`, use only features guaranteed by the compilation target.
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_sve2() -> bool {
    cfg!(target_feature = "sve2")
}

/// Whether the CPU has FEAT_DIT, whatever `VG_CPU_FEATURES` says: data
/// independent timing chooses no implementation but is the mode every one
/// runs in (the library's `src/dit.rs`), so the tests and benchmarks of every
/// configuration run with it wherever the CPU has it. (`detected` reports it
/// as any other feature, so that `VG_CPU_FEATURES=none` reports none, and
/// the dispatchers choose the base implementations.)
#[cfg(target_arch = "aarch64")]
pub fn dit() -> bool {
    aarch64_dit()
}

/// Whether the CPU has FEAT_DIT, asked of the operating system.
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_dit() -> bool {
    std::arch::is_aarch64_feature_detected!("dit")
}

/// Without `std`, use only features guaranteed by the compilation target
/// (`aarch64-apple-darwin`'s Apple M1 baseline has FEAT_DIT).
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_dit() -> bool {
    cfg!(target_feature = "dit")
}

/// Whether the CPU has FEAT_SB, asked of the operating system.
#[cfg(all(target_arch = "aarch64", feature = "std"))]
fn aarch64_sb() -> bool {
    std::arch::is_aarch64_feature_detected!("sb")
}

/// Without `std`, use only features guaranteed by the compilation target
/// (`aarch64-apple-darwin`'s Apple M1 baseline has FEAT_SB).
#[cfg(all(target_arch = "aarch64", not(feature = "std")))]
fn aarch64_sb() -> bool {
    cfg!(target_feature = "sb")
}

/// ARMv7's `umaal`: every ARMv7-A (and ARMv8-A AArch32) core has it, and
/// the operating systems the emitter compiles code needing it for
/// (`TCB/Arm/Print.lean`'s `featureCfg`) run on those alone; the Cortex-M3,
/// which `target_arch = "arm"` also covers, lacks it (ARMv7-M has it only
/// with the DSP extension) and its long multiplies take a time that depends
/// on their operands.
#[cfg(all(
    target_arch = "arm",
    any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    )
))]
pub fn runtime() -> u32 {
    feature::UMAAL
}

/// No features are detected on the other targets: on ARMv7 without an
/// operating system that runs on A-profile cores alone, `umaal` is not
/// assumed.
#[cfg(not(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    all(
        target_arch = "arm",
        any(
            target_os = "linux",
            target_os = "android",
            target_os = "freebsd",
            target_os = "netbsd",
            target_os = "openbsd"
        )
    )
)))]
pub fn runtime() -> u32 {
    0
}
