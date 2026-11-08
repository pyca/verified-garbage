//! CPU features, for choosing among implementations of a primitive: their
//! detection is the crate `verified_garbage_cpu`'s
//! (`crates/verified-garbage-cpu/src/detect.rs`), which the generated
//! dispatchers ask, and its tests are here, which CI runs with the
//! library's.

#[cfg(test)]
mod tests {
    #[cfg(all(
        feature = "cpu-features-env",
        any(target_arch = "x86", target_arch = "x86_64")
    ))]
    use verified_garbage_cpu::detect::REPORTED_WITH;
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    use verified_garbage_cpu::detect::decode;
    use verified_garbage_cpu::detect::{NAMES, allowed, runtime};
    #[cfg(feature = "cpu-features-env")]
    use verified_garbage_cpu::detect::{allowed_by, named_by, parse};
    use verified_garbage_cpu::{COMPILED, Features, detected, feature, requested, target_contains};

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

    /// BMI2 and ADX are reported only with AVX2: without it (leaf 7's bit 5
    /// clear, or the `ymm` state not enabled), not at all.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn decode_bmi2_adx_need_avx2() {
        let mut leaves = [[0; 4]; 8];
        leaves[0][0] = 7;
        leaves[1][2] = 1 << 27 | 1 << 28;
        // BMI2 and ADX, and AVX2 or not.
        for (avx2, xcr0, want) in [
            (
                1 << 5,
                0b111,
                feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX,
            ),
            (0, 0b111, feature::AVX),
            (1 << 5, 0b001, 0),
        ] {
            leaves[7][1] = 1 << 8 | 1 << 19 | avx2;
            let f = decode(|leaf, _| leaves[leaf as usize], || xcr0);
            assert_eq!(Features(f), Features(want));
        }
    }

    /// AES-NI is reported only with SSSE3, VAES only with AES-NI, and
    /// AVX-512F only with AVX2 (`REPORTED_WITH`).
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[test]
    fn decode_aes_vaes_avx512f_need_their_others() {
        let mut leaves = [[0; 4]; 8];
        leaves[0][0] = 7;
        // OSXSAVE and AVX; SSSE3 and AES-NI, or AES-NI alone.
        for (ecx, ebx, want) in [
            // VAES and AVX-512F, with AES-NI, SSSE3 and AVX2.
            (
                1 << 9 | 1 << 25,
                1 << 5 | 1 << 16,
                feature::SSSE3
                    | feature::AES
                    | feature::AVX
                    | feature::AVX2
                    | feature::VAES
                    | feature::AVX512F,
            ),
            // Without SSSE3, no AES-NI, so no VAES; without AVX2, no AVX-512F.
            (1 << 25, 1 << 16, feature::AVX),
        ] {
            leaves[1][2] = ecx | 1 << 27 | 1 << 28;
            leaves[7][1] = ebx;
            leaves[7][2] = 1 << 9;
            let f = decode(|leaf, _| leaves[leaf as usize], || 0b1110_0111);
            assert_eq!(Features(f), Features(want));
        }
    }

    /// Detection returns the CPU's features, restricted as
    /// `VG_CPU_FEATURES` says.
    #[test]
    fn detected_is_allowed() {
        assert_eq!(detected(), Features(runtime() & allowed(runtime())));
    }

    /// The CPU has every feature the compilation target enables, and
    /// detection reports each; with `cpu-features-env`, which lets
    /// `VG_CPU_FEATURES` remove any, it enables none.
    #[test]
    fn compiled_is_detected() {
        assert!(Features(runtime()).contains(COMPILED));
        #[cfg(not(feature = "cpu-features-env"))]
        assert!(detected().contains(COMPILED));
        #[cfg(feature = "cpu-features-env")]
        assert_eq!(COMPILED, Features(0));
    }

    /// The features of `aarch64-apple-darwin`'s baseline (Apple's M1),
    /// which `target_contains` answers for without detecting.
    #[cfg(all(
        not(feature = "cpu-features-env"),
        target_arch = "aarch64",
        target_vendor = "apple"
    ))]
    #[test]
    fn compiled_apple() {
        let m1 = feature::NEON | feature::AES | feature::SHA2 | feature::SHA3 | feature::DIT;
        assert!(COMPILED.contains(Features(m1)));
    }

    /// `target_contains` holds only where detection reports the same
    /// features, and with `cpu-features-env` never but for the empty set.
    #[test]
    fn target_contains_is_detected() {
        assert!(target_contains(Features(0)));
        for (name, bit) in NAMES {
            let f = Features(bit);
            assert_eq!(target_contains(f), COMPILED.contains(f), "{name}");
            assert!(!target_contains(f) || detected().contains(f), "{name}");
            #[cfg(feature = "cpu-features-env")]
            assert!(!target_contains(f), "{name}");
        }
        assert!(target_contains(COMPILED));
    }

    /// `requested` says whether `VG_CPU_FEATURES` names every feature of a
    /// set that is not empty.
    #[test]
    fn requested_is_named() {
        #[cfg(feature = "cpu-features-env")]
        let named = named_by(&std::env::var("VG_CPU_FEATURES").unwrap_or_default());
        #[cfg(not(feature = "cpu-features-env"))]
        let named = 0;
        assert!(!requested(Features(0)));
        for (name, bit) in NAMES {
            assert_eq!(requested(Features(bit)), named & bit != 0, "{name}");
        }
        assert_eq!(requested(Features(named)), named != 0);
    }

    /// What a value of `VG_CPU_FEATURES` names: nothing if it is empty or
    /// `none`.
    #[cfg(feature = "cpu-features-env")]
    #[test]
    fn named_by_names() {
        assert_eq!(named_by(""), 0);
        assert_eq!(named_by("none"), 0);
        assert_eq!(named_by("aes,ssse3"), 0b101);
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

    /// BMI2 without AVX2 is a configuration no CPU has.
    #[cfg(all(
        feature = "cpu-features-env",
        any(target_arch = "x86", target_arch = "x86_64")
    ))]
    #[test]
    #[should_panic(expected = "VG_CPU_FEATURES names bmi2 without avx2, which no CPU has")]
    fn allowed_by_bmi2_without_avx2() {
        allowed_by("bmi2,adx", u32::MAX);
    }

    /// Naming a feature that is reported only with another
    /// (`REPORTED_WITH`) fails without that one, whatever else it names, and
    /// not with it.
    #[cfg(all(
        feature = "cpu-features-env",
        any(target_arch = "x86", target_arch = "x86_64")
    ))]
    #[test]
    fn allowed_by_reported_with() {
        // `VG_CPU_FEATURES` naming the features `bits`.
        let names = |bits: u32| {
            let named: std::vec::Vec<&str> = (NAMES.iter())
                .filter(|(_, b)| bits & b != 0)
                .map(|(n, _)| *n)
                .collect();
            named.join(",")
        };
        // Every feature another is reported only with.
        let others = feature::SSSE3 | feature::AES | feature::AVX | feature::AVX2;
        for (f, with) in REPORTED_WITH {
            let without = names(f | (others & !with));
            assert!(std::panic::catch_unwind(|| allowed_by(&without, u32::MAX)).is_err());
            assert_eq!(allowed_by(&names(f | others), u32::MAX), f | others);
        }
    }

    /// With AVX2, BMI2 and ADX are allowed.
    #[cfg(feature = "cpu-features-env")]
    #[test]
    fn allowed_by_bmi2_adx_with_avx2() {
        let f = feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX;
        assert_eq!(allowed_by("avx,avx2,bmi2,adx", u32::MAX), f);
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
