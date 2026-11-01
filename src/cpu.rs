//! CPU features, for choosing among implementations of a primitive.
//!
//! Some artifacts use instructions beyond their target's baseline ISA. Lean
//! checks which CPU features those need, and the emitter generates a
//! [`Features`] constant of them, `<NAME>_FEATURES`, next to the function
//! (and lists them in its `# Safety` section): the function may only be
//! called on a CPU that has all of them. They are detected once: with `cpuid` on x86 and x86-64; on AArch64,
//! by asking the operating system with the `std` feature (which links
//! `std`, and which `cpu-features-env` enables), and otherwise from the
//! target features the code was compiled for; on ARMv7, from the operating
//! system the code was compiled for (`umaal`, on those that run on A-profile
//! cores alone). Each object that can use such a function chooses its
//! implementation when it is created, from the features detected. A feature
//! detection does not know (one without a bit in [`feature`]) cannot be
//! checked for: a generated constant is the union of the bits of the
//! features it names, so naming one fails to compile.
//!
//! With the `cpu-features-env` Cargo feature, the environment variable
//! `VG_CPU_FEATURES` restricts the features detected, so that tests and
//! benchmarks can run every implementation on one machine: `none`, or a
//! comma-separated list of the names in `NAMES` (e.g. `aes,pclmulqdq`).
//! Unset or empty, it restricts nothing. It can only remove features, so it
//! can never choose code the CPU cannot run, and it names only features
//! this library knows and the CPU has: anything else panics, rather than
//! quietly testing another configuration. On AArch64, standalone hashing
//! chooses FEAT_SHA3's Keccak on non-Apple targets only when this variable
//! names `sha3`, since it is not faster there. ML-DSA and ML-KEM independently select their paired
//! SHA3 implementations whenever the detected features support them.

use core::sync::atomic::{AtomicU32, Ordering};

use verified_garbage_cpu::Features;
// Each target uses only some of the features' bits, and some none.
#[allow(unused_imports)]
use verified_garbage_cpu::feature;

/// Each feature's name and bit, for reading `VG_CPU_FEATURES` and for the
/// tests: bit `i` is `NAMES[i]`'s.
#[cfg(any(test, feature = "cpu-features-env"))]
pub(crate) const NAMES: [(&str, u32); 21] = [
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
];

/// The detected features, with [`DETECTED_INIT`] set once they are known.
static DETECTED: AtomicU32 = AtomicU32::new(0);
const DETECTED_INIT: u32 = 1 << 30;

/// The features of this CPU, restricted by `VG_CPU_FEATURES` (see the
/// module's documentation). (Detection is idempotent, so threads racing to
/// do it store the same value, and `Relaxed` is enough.)
///
/// Inlined, it is a load and a test once detection has run; the detection
/// itself is out of line (`detect`), so callers keep no registers for it.
#[inline]
pub(crate) fn detected() -> Features {
    let mut f = DETECTED.load(Ordering::Relaxed);
    if f & DETECTED_INIT == 0 {
        f = detect();
    }
    Features(f & !DETECTED_INIT)
}

/// Detects the features, records them for `detected` and returns them, with
/// `DETECTED_INIT` set.
#[cold]
#[inline(never)]
fn detect() -> u32 {
    let runtime = runtime();
    let f = (runtime & allowed(runtime)) | DETECTED_INIT;
    DETECTED.store(f, Ordering::Relaxed);
    f
}

/// The features `VG_CPU_FEATURES` allows on a CPU with the features
/// `runtime`.
///
/// # Panics
///
/// As [`allowed_by`].
#[cfg(feature = "cpu-features-env")]
fn allowed(runtime: u32) -> u32 {
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
#[cfg(feature = "cpu-features-env")]
fn allowed_by(names: &str, runtime: u32) -> u32 {
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
    allowed
}

/// Every feature: without the `cpu-features-env` Cargo feature, nothing
/// restricts them.
#[cfg(not(feature = "cpu-features-env"))]
fn allowed(_: u32) -> u32 {
    u32::MAX
}

/// The features a value of `VG_CPU_FEATURES` allows (every one if it is
/// empty, none if it is `none`), or `None` if it names an unknown one.
#[cfg(feature = "cpu-features-env")]
fn parse(names: &str) -> Option<u32> {
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
fn runtime() -> u32 {
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
fn decode(cpuid: impl Fn(u32, u32) -> [u32; 4], xgetbv: impl Fn() -> u64) -> u32 {
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
    let bmi2 = (ebx >> 8) & 1;
    let avx512f = (ebx >> 16) & avx & zmm;
    let sha512 = eax1 & avx;
    let adx = (ebx >> 19) & 1;
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
/// and FEAT_SHA256, `sha3` covers FEAT_SHA512 and FEAT_SHA3, and `sve2` is
/// FEAT_SVE2.
#[cfg(target_arch = "aarch64")]
fn runtime() -> u32 {
    (u32::from(aarch64_aes()) * feature::AES)
        | (u32::from(aarch64_sha2()) * feature::SHA2)
        | (u32::from(aarch64_sha3()) * feature::SHA3)
        | (u32::from(aarch64_sve2()) * feature::SVE2)
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
fn runtime() -> u32 {
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
fn runtime() -> u32 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each name's bit is its index in `NAMES`, and no name is there twice.
    #[test]
    fn names_are_bits() {
        for (i, (name, bit)) in NAMES.iter().enumerate() {
            assert_eq!(*bit, 1 << i, "{name}");
            assert_eq!(NAMES.iter().filter(|(n, _)| n == name).count(), 1);
        }
    }

    #[test]
    fn all() {
        assert_eq!(
            Features::all(&[
                Features(feature::SHA),
                Features(0),
                Features(feature::SSSE3 | feature::SHA)
            ]),
            Features(feature::SSSE3 | feature::SHA)
        );
    }

    #[test]
    fn contains() {
        let f = Features(feature::SHA | feature::SSSE3);
        assert!(f.contains(Features(0)));
        assert!(f.contains(Features(feature::SHA)));
        assert!(f.contains(f));
        assert!(!f.contains(Features(feature::SHA | feature::AVX)));
        assert!(!Features(0).contains(f));
    }

    /// A CPU without leaf 7 (the oldest x86-64 ones; no runner's CPU lacks
    /// it) has none of its features, and leaf 7 is not read: whatever the
    /// runners' CPUs, every architecture tests each branch of `decode`.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn decode_without_leaf_7() {
        // Leaf 1: SSSE3, AES, PCLMULQDQ, OSXSAVE and AVX.
        let leaves = [
            [1, 0, 0, 0],
            [0, 0, 1 << 9 | 1 << 25 | 1 << 1 | 1 << 27 | 1 << 28, 0],
        ];
        let f = decode(|leaf, _| leaves[leaf as usize], || 0b111);
        assert_eq!(
            Features(f),
            Features(feature::SSSE3 | feature::AES | feature::PCLMULQDQ | feature::AVX)
        );
    }

    /// Leaf 7's sub-leaf 1 is read if, and only if, sub-leaf 0 says it
    /// exists.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn decode_sub_leaf_1() {
        for subs in [0, 1] {
            let mut leaves = [[[0; 4]; 2]; 8];
            leaves[0][0][0] = 7;
            leaves[1][0][2] = 1 << 27 | 1 << 28;
            // Sub-leaf 0: the last sub-leaf, SHA and AVX2; sub-leaf 1: SHA512.
            leaves[7] = [[subs, 1 << 29 | 1 << 5, 0, 0], [1, 0, 0, 0]];
            let f = decode(
                |leaf, sub| {
                    assert!(sub <= subs);
                    leaves[leaf as usize][sub as usize]
                },
                || 0b111,
            );
            let want = if subs == 1 {
                Features(feature::SHA | feature::AVX | feature::AVX2 | feature::SHA512)
            } else {
                Features(feature::SHA | feature::AVX | feature::AVX2)
            };
            assert_eq!(Features(f), want);
        }
    }

    /// Detection returns the CPU's features, restricted as
    /// `VG_CPU_FEATURES` says.
    #[test]
    fn detected_is_allowed() {
        assert_eq!(detected(), Features(runtime() & allowed(runtime())));
    }

    #[cfg(feature = "cpu-features-env")]
    #[test]
    fn allowed_by_names() {
        assert_eq!(allowed_by("", 0), u32::MAX);
        assert_eq!(allowed_by("none", 0), 0);
        assert_eq!(allowed_by("aes,ssse3", 0b111), 0b101);
    }

    /// Naming a feature the CPU does not have fails, rather than testing or
    /// benchmarking another configuration.
    #[cfg(feature = "cpu-features-env")]
    #[test]
    #[should_panic(expected = "VG_CPU_FEATURES names sha,avx, which this CPU does not have")]
    fn allowed_by_names_the_cpu_lacks() {
        allowed_by("aes,sha,avx", 0b101);
    }

    #[cfg(feature = "cpu-features-env")]
    #[test]
    fn parse_names() {
        assert_eq!(parse(""), Some(u32::MAX));
        assert_eq!(parse("none"), Some(0));
        assert_eq!(parse("sha"), Some(0b10));
        assert_eq!(parse("aes,pclmulqdq,ssse3"), Some(0b1101));
        assert_eq!(parse("avx,avx2"), Some(0b11_0000));
        assert_eq!(parse("bmi1,bmi2"), Some(0b1100_0000));
        assert_eq!(parse("avx512f"), Some(0b1_0000_0000));
        assert_eq!(parse("sha512"), Some(0b10_0000_0000));
        assert_eq!(parse("sha2"), Some(1 << 10));
        assert_eq!(parse("sha3"), Some(1 << 11));
        assert_eq!(parse("neon,sve2"), Some((1 << 15) | (1 << 16)));
        assert_eq!(parse("sha2,sha3"), Some((1 << 10) | (1 << 11)));
        assert_eq!(parse("adx"), Some(1 << 12));
        assert_eq!(parse("avx512bw"), Some(1 << 19));
        assert_eq!(parse("umaal"), Some(1 << 20));
        for bad in ["avx512vbmi", "aes,", "aes,none", " aes", "AES"] {
            assert_eq!(parse(bad), None, "{bad}");
        }
    }
}
