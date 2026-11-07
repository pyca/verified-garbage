#[cfg(target_arch = "x86_64")]
use super::Round;
use super::{Search, Searcher};
use crate::arch::dsa::vg_dsa_parameter_search_init;
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES, VG_DSA_PARAMETER_SEARCH_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_IFMA_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_IFMA_FEATURES, vg_dsa_parameter_search,
    vg_dsa_parameter_search_mr_adx, vg_dsa_parameter_search_mr_ifma,
    vg_dsa_parameter_search_sha1_avx_bmi, vg_dsa_parameter_search_sha1_avx_bmi_mr_adx,
    vg_dsa_parameter_search_sha1_avx_bmi_mr_ifma, vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2,
    vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_adx,
    vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_ifma,
    vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani,
    vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani_mr_adx,
    vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani_mr_ifma, vg_dsa_parameter_search_sha1_shani,
    vg_dsa_parameter_search_sha1_shani_mr_adx, vg_dsa_parameter_search_sha1_shani_mr_ifma,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_ifma,
    vg_dsa_parameter_search_sha1_shani_sha256_shani,
    vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_ifma, vg_dsa_parameter_search_sha256_avx2,
    vg_dsa_parameter_search_sha256_avx2_mr_adx, vg_dsa_parameter_search_sha256_avx2_mr_ifma,
    vg_dsa_parameter_search_sha256_shani, vg_dsa_parameter_search_sha256_shani_mr_adx,
    vg_dsa_parameter_search_sha256_shani_mr_ifma,
};
use crate::cpu::detected;
#[cfg(target_arch = "x86_64")]
use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
use alloc::vec;
#[cfg(target_arch = "x86_64")]
use verified_garbage_cpu::Features;

const WIDTHS: [(usize, usize); 3] = [(128, 20), (256, 32), (384, 32)];

#[test]
fn init_words() {
    for (p_len, _) in WIDTHS {
        let mut state = [7u64; 4];
        // SAFETY: four writable words.
        assert_eq!(
            unsafe { vg_dsa_parameter_search_init(&mut state, p_len) },
            1
        );
        let p = p_len as u64;
        assert_eq!(state, [4096, p, 32769 * p, 512 * p]);
    }
    for p_len in [0, 20, 127, 192, 512] {
        let mut state = [7u64; 4];
        // SAFETY: four writable words.
        assert_eq!(
            unsafe { vg_dsa_parameter_search_init(&mut state, p_len) },
            0
        );
        assert_eq!(state, [0; 4]);
    }
}

/// `search` on an empty tape asks for the first tape, and (at 1024 bits) on
/// a tape of 0x02 octets, whose seeds' q are divisible by 3, rejects every
/// seed: with one seed allowed it is exhausted after consuming one seed.
fn check(search: Search) {
    for (p_len, q_len) in WIDTHS {
        let mut s = Searcher::new(p_len, q_len);
        s.search = search;
        s.packed.fill(0xa5);
        assert_eq!(s.run(&[]), (0, 0));
        assert_eq!(s.state[3], 512 * p_len as u64);
        assert!(s.packed.iter().all(|&b| b == 0));
        if p_len != 128 {
            continue;
        }
        s.state[0] = 1;
        let tape = vec![2u8; 2 * q_len];
        assert_eq!(s.run(&tape), (3, q_len));
        assert_eq!(s.state, [0, p_len as u64, 32769 * p_len as u64, 0]);
    }
}

#[test]
#[cfg(target_arch = "x86_64")]
fn backend_combinations() {
    use super::select_backends;
    // Some of these combinations cannot be selected by a real CPU, since the
    // hash instructions share feature requirements. Check the complete
    // dispatch table against the emitted feature sets, at every width.
    let cases: &[(H1, H256, Round, Search, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            Round::Baseline,
            vg_dsa_parameter_search,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::Scalar,
            Round::Adx,
            vg_dsa_parameter_search_mr_adx,
            VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Scalar,
            Round::Ifma,
            vg_dsa_parameter_search_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_MR_IFMA_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Avx2,
            Round::Baseline,
            vg_dsa_parameter_search_sha256_avx2,
            VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Avx2,
            Round::Adx,
            vg_dsa_parameter_search_sha256_avx2_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Avx2,
            Round::Ifma,
            vg_dsa_parameter_search_sha256_avx2_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_IFMA_FEATURES,
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            Round::Baseline,
            vg_dsa_parameter_search_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES,
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            Round::Adx,
            vg_dsa_parameter_search_sha256_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            Round::Ifma,
            vg_dsa_parameter_search_sha256_shani_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_IFMA_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            Round::Adx,
            vg_dsa_parameter_search_sha1_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_shani_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_IFMA_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Avx2,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_shani_sha256_avx2,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Avx2,
            Round::Adx,
            vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Avx2,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_IFMA_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_shani_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            Round::Adx,
            vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_IFMA_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Scalar,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_avx_bmi,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Scalar,
            Round::Adx,
            vg_dsa_parameter_search_sha1_avx_bmi_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_MR_ADX_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Scalar,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_avx_bmi_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_MR_IFMA_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Avx2,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Avx2,
            Round::Adx,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::Avx2,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_avx2_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_AVX2_MR_IFMA_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::ShaNi,
            Round::Baseline,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::ShaNi,
            Round::Adx,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::AvxBmi,
            H256::ShaNi,
            Round::Ifma,
            vg_dsa_parameter_search_sha1_avx_bmi_sha256_shani_mr_ifma,
            VG_DSA_PARAMETER_SEARCH_SHA1_AVX_BMI_SHA256_SHANI_MR_IFMA_FEATURES,
        ),
    ];
    for &(h1, h256, round, expected, required) in cases {
        let selected = select_backends(h1, h256, round);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        if detected().contains(required) {
            check(selected);
        }
    }
}

/// The round's implementation is chosen by its generated feature sets: IFMA's
/// needs AVX, AVX512F, AVX512_IFMA and AVX512VL with ADX's BMI2 and ADX.
#[test]
#[cfg(target_arch = "x86_64")]
fn round_feature_requirements() {
    use verified_garbage_cpu::feature;
    let adx = feature::BMI2 | feature::ADX;
    let ifma = adx | feature::AVX | feature::AVX512F | feature::AVX512IFMA | feature::AVX512VL;
    let cases: &[(u32, Round)] = &[
        (0, Round::Baseline),
        (feature::BMI2, Round::Baseline),
        (feature::ADX, Round::Baseline),
        (ifma & !feature::BMI2, Round::Baseline),
        (ifma & !feature::ADX, Round::Baseline),
        (adx, Round::Adx),
        (adx | feature::AVX | feature::AVX2, Round::Adx),
        (ifma & !feature::AVX, Round::Adx),
        (ifma & !feature::AVX512F, Round::Adx),
        (ifma & !feature::AVX512IFMA, Round::Adx),
        (ifma & !feature::AVX512VL, Round::Adx),
        (ifma, Round::Ifma),
        (
            ifma | feature::AVX2 | feature::SHA | feature::SSSE3,
            Round::Ifma,
        ),
    ];
    for &(features, expected) in cases {
        assert_eq!(Round::select(Features(features)), expected, "{features:?}");
    }
}

#[test]
#[cfg(target_arch = "powerpc64")]
fn baseline() {
    check(super::select(detected()));
}

#[test]
#[cfg(target_arch = "x86")]
fn backend_combinations() {
    use super::select_backends;
    use crate::arch::dsa::{
        VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
        VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
        VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES, vg_dsa_parameter_search,
        vg_dsa_parameter_search_sha1_shani, vg_dsa_parameter_search_sha1_shani_sha256_shani,
        vg_dsa_parameter_search_sha256_shani,
    };
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    use verified_garbage_cpu::Features;
    // The mixed SHA pairs cannot be selected by a real CPU, since both hashes
    // need the same feature. Check the complete dispatch table against the
    // emitted feature sets, at every width.
    let cases: &[(H1, H256, Search, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            vg_dsa_parameter_search,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            vg_dsa_parameter_search_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            vg_dsa_parameter_search_sha1_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            vg_dsa_parameter_search_sha1_shani_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
        ),
    ];
    for &(h1, h256, expected, required) in cases {
        let selected = select_backends(h1, h256);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        if detected().contains(required) {
            check(selected);
        }
    }
}

#[test]
#[cfg(target_arch = "aarch64")]
fn backend_combinations() {
    use super::select_backends;
    use crate::arch::dsa::{
        VG_DSA_PARAMETER_SEARCH_SHA1_SHA2_FEATURES,
        VG_DSA_PARAMETER_SEARCH_SHA1_SHA2_SHA256_SHA2_FEATURES,
        VG_DSA_PARAMETER_SEARCH_SHA256_SHA2_FEATURES, vg_dsa_parameter_search,
        vg_dsa_parameter_search_sha1_sha2, vg_dsa_parameter_search_sha1_sha2_sha256_sha2,
        vg_dsa_parameter_search_sha256_sha2,
    };
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    use verified_garbage_cpu::Features;
    // The mixed SHA pairs cannot be selected by a real CPU, since both hashes
    // need the same feature. Check the complete dispatch table against the
    // emitted feature sets, at every width.
    let cases: &[(H1, H256, Search, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            vg_dsa_parameter_search,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::Sha2,
            vg_dsa_parameter_search_sha256_sha2,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHA2_FEATURES,
        ),
        (
            H1::Sha2,
            H256::Scalar,
            vg_dsa_parameter_search_sha1_sha2,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHA2_FEATURES,
        ),
        (
            H1::Sha2,
            H256::Sha2,
            vg_dsa_parameter_search_sha1_sha2_sha256_sha2,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHA2_SHA256_SHA2_FEATURES,
        ),
    ];
    for &(h1, h256, expected, required) in cases {
        let selected = select_backends(h1, h256);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        if detected().contains(required) {
            check(selected);
        }
    }
}

#[test]
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
fn backend_combinations() {
    use super::{select, select_backends};
    use crate::arch::dsa::{
        VG_DSA_PARAMETER_SEARCH_UMAAL_FEATURES, vg_dsa_parameter_search,
        vg_dsa_parameter_search_umaal,
    };
    use verified_garbage_cpu::Features;
    let cases: &[(bool, Search, Features)] = &[
        (false, vg_dsa_parameter_search, Features(0)),
        (
            true,
            vg_dsa_parameter_search_umaal,
            VG_DSA_PARAMETER_SEARCH_UMAAL_FEATURES,
        ),
    ];
    for &(umaal, expected, required) in cases {
        let selected = select_backends(umaal);
        assert!(core::ptr::fn_addr_eq(selected, expected));
        assert!(core::ptr::fn_addr_eq(select(required), expected));
        if detected().contains(required) {
            check(selected);
        }
    }
}
