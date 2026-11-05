#[cfg(target_arch = "x86_64")]
use super::select_backends;
use super::{Search, Searcher};
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES, VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_ADX_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES,
    VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_ADX_FEATURES, vg_dsa_parameter_search_mr_adx,
    vg_dsa_parameter_search_sha1_shani, vg_dsa_parameter_search_sha1_shani_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_shani,
    vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx, vg_dsa_parameter_search_sha256_avx2,
    vg_dsa_parameter_search_sha256_avx2_mr_adx, vg_dsa_parameter_search_sha256_shani,
    vg_dsa_parameter_search_sha256_shani_mr_adx,
};
use crate::arch::dsa::{vg_dsa_parameter_search, vg_dsa_parameter_search_init};
use crate::cpu::detected;
#[cfg(target_arch = "x86_64")]
use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
use alloc::vec;
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
    // Some of these pairs cannot be selected by a real CPU, since the hash
    // instructions share feature requirements. Check the complete dispatch
    // table against the emitted feature sets, at every width.
    let cases: &[(H1, H256, bool, Search, Features)] = &[
        (
            H1::Scalar,
            H256::Scalar,
            false,
            vg_dsa_parameter_search,
            Features(0),
        ),
        (
            H1::Scalar,
            H256::Scalar,
            true,
            vg_dsa_parameter_search_mr_adx,
            VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Avx2,
            false,
            vg_dsa_parameter_search_sha256_avx2,
            VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_FEATURES,
        ),
        (
            H1::Scalar,
            H256::Avx2,
            true,
            vg_dsa_parameter_search_sha256_avx2_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            false,
            vg_dsa_parameter_search_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_FEATURES,
        ),
        (
            H1::Scalar,
            H256::ShaNi,
            true,
            vg_dsa_parameter_search_sha256_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA256_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            false,
            vg_dsa_parameter_search_sha1_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Scalar,
            true,
            vg_dsa_parameter_search_sha1_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Avx2,
            false,
            vg_dsa_parameter_search_sha1_shani_sha256_avx2,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::Avx2,
            true,
            vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_AVX2_MR_ADX_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            false,
            vg_dsa_parameter_search_sha1_shani_sha256_shani,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_FEATURES,
        ),
        (
            H1::ShaNi,
            H256::ShaNi,
            true,
            vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx,
            VG_DSA_PARAMETER_SEARCH_SHA1_SHANI_SHA256_SHANI_MR_ADX_FEATURES,
        ),
    ];
    for &(h1, h256, adx, expected, required) in cases {
        let selected = select_backends(h1, h256, adx);
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
    use crate::arch::dsa::{VG_DSA_PARAMETER_SEARCH_UMAAL_FEATURES, vg_dsa_parameter_search_umaal};
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
