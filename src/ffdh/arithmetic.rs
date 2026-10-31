//! Public arithmetic for FFDH, and the selection of its implementations.
#[cfg(target_arch = "x86_64")]
use crate::arch::ffdh::{
    VG_FFDH_CHECK_DOMAIN_ADX_FEATURES, VG_FFDH_CHECK_PRIVATE_ADX_FEATURES,
    VG_FFDH_CHECK_PUBLIC_ADX_FEATURES, VG_FFDH_EXCHANGE_ADX_FEATURES,
    VG_FFDH_GENERATE_KEY_ADX_FEATURES, VG_FFDH_GENERATE_KEY_SEARCH_ADX_FEATURES,
    VG_FFDH_GENERATE_PARAMETERS_ADX_FEATURES,
};
#[cfg(target_arch = "arm")]
use crate::arch::ffdh::{
    VG_FFDH_CHECK_DOMAIN_UMAAL_FEATURES, VG_FFDH_CHECK_PRIVATE_UMAAL_FEATURES,
    VG_FFDH_CHECK_PUBLIC_UMAAL_FEATURES, VG_FFDH_DERIVE_PUBLIC_UMAAL_FEATURES,
    VG_FFDH_EXCHANGE_UMAAL_FEATURES, VG_FFDH_GENERATE_KEY_CACHED_UMAAL_FEATURES,
    VG_FFDH_GENERATE_KEY_PRECOMPUTE_UMAAL_FEATURES,
    VG_FFDH_GENERATE_KEY_SEARCH_CACHED_UMAAL_FEATURES,
    VG_FFDH_GENERATE_PARAMETERS_SIEVED_UMAAL_FEATURES,
};
use alloc::{vec, vec::Vec};
use verified_garbage_cpu::Features;

pub(super) fn canonical(a: &[u8]) -> &[u8] {
    &a[a.iter().position(|&b| b != 0).unwrap_or(a.len())..]
}
pub(super) fn bits(a: &[u8]) -> usize {
    let a = canonical(a);
    a.first()
        .map_or(0, |b| 8 * a.len() - b.leading_zeros() as usize)
}
pub(super) fn scalar(a: &[u8], len: usize) -> Vec<u8> {
    let a = canonical(a);
    let mut out = vec![0; len];
    out[len - a.len()..].copy_from_slice(a);
    out
}
/// The implementations of the verified functions FFDH calls: the baseline
/// ISA's, x86-64 ADX variants, or ARMv7 UMAAL variants. Each use selects it from the
/// features of the functions it calls; RSA's private-key routines have
/// additional feature requirements that do not apply to these functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Backend {
    Baseline,
    #[cfg(target_arch = "x86_64")]
    Adx,
    #[cfg(target_arch = "arm")]
    Umaal,
}
impl Backend {
    /// The implementation of the FFDH operations (`vg_ffdh_*`, in
    /// `Domain`, key generation and parameter generation) a CPU with the features `_f`
    /// can run.
    pub(super) fn ffdh(_f: Features) -> Self {
        #[cfg(target_arch = "x86_64")]
        if _f.contains(
            const {
                Features::all(&[
                    VG_FFDH_CHECK_DOMAIN_ADX_FEATURES,
                    VG_FFDH_CHECK_PUBLIC_ADX_FEATURES,
                    VG_FFDH_CHECK_PRIVATE_ADX_FEATURES,
                    VG_FFDH_GENERATE_KEY_ADX_FEATURES,
                    VG_FFDH_EXCHANGE_ADX_FEATURES,
                    VG_FFDH_GENERATE_PARAMETERS_ADX_FEATURES,
                    VG_FFDH_GENERATE_KEY_SEARCH_ADX_FEATURES,
                ])
            },
        ) {
            return Self::Adx;
        }
        #[cfg(target_arch = "arm")]
        if _f.contains(
            const {
                Features::all(&[
                    VG_FFDH_CHECK_DOMAIN_UMAAL_FEATURES,
                    VG_FFDH_CHECK_PUBLIC_UMAAL_FEATURES,
                    VG_FFDH_CHECK_PRIVATE_UMAAL_FEATURES,
                    VG_FFDH_EXCHANGE_UMAAL_FEATURES,
                    VG_FFDH_DERIVE_PUBLIC_UMAAL_FEATURES,
                    VG_FFDH_GENERATE_KEY_PRECOMPUTE_UMAAL_FEATURES,
                    VG_FFDH_GENERATE_KEY_CACHED_UMAAL_FEATURES,
                    VG_FFDH_GENERATE_KEY_SEARCH_CACHED_UMAAL_FEATURES,
                    VG_FFDH_GENERATE_PARAMETERS_SIEVED_UMAAL_FEATURES,
                ])
            },
        ) {
            return Self::Umaal;
        }
        Self::Baseline
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
mod tests {
    use super::*;
    use verified_garbage_cpu::feature;

    #[test]
    fn backend_feature_requirements() {
        // The selection needs exactly BMI2 and ADX, the generated feature
        // sets of the functions it calls. AVX, AVX2 and IFMA belong to
        // other RSA routines: they neither enable ADX nor gate it when BMI2
        // and ADX are present.
        let cases: &[(u32, Backend)] = &[
            (0, Backend::Baseline),
            (feature::BMI2, Backend::Baseline),
            (feature::ADX, Backend::Baseline),
            (feature::AVX | feature::AVX2, Backend::Baseline),
            (
                feature::AVX | feature::AVX2 | feature::BMI2,
                Backend::Baseline,
            ),
            (
                feature::AVX | feature::AVX2 | feature::ADX,
                Backend::Baseline,
            ),
            (
                feature::AVX
                    | feature::AVX2
                    | feature::AVX512F
                    | feature::AVX512IFMA
                    | feature::AVX512VL,
                Backend::Baseline,
            ),
            (feature::BMI2 | feature::ADX, Backend::Adx),
            (
                feature::AVX | feature::AVX2 | feature::BMI2 | feature::ADX,
                Backend::Adx,
            ),
            (
                feature::AVX
                    | feature::AVX2
                    | feature::AVX512F
                    | feature::BMI2
                    | feature::ADX
                    | feature::AVX512IFMA
                    | feature::AVX512VL,
                Backend::Adx,
            ),
        ];
        for &(features, expected) in cases {
            let selected = Backend::ffdh(Features(features));
            assert_eq!(selected, expected, "{features:?}");
        }
    }
}

#[cfg(all(test, target_arch = "arm"))]
mod arm_tests {
    use super::*;
    use verified_garbage_cpu::feature;
    #[test]
    fn backend_feature_requirements() {
        for (names, expected) in [
            (0, Backend::Baseline),
            (feature::NEON, Backend::Baseline),
            (feature::UMAAL, Backend::Umaal),
            (feature::NEON | feature::UMAAL, Backend::Umaal),
        ] {
            assert_eq!(Backend::ffdh(Features(names)), expected);
        }
    }
}
