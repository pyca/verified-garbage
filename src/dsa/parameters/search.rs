//! Parameter generation over refillable random tapes
//! (`VG.Spec.Dsa.parameterSearch`): `vg_dsa_parameter_search_init` makes the
//! search's four public words, and `vg_dsa_parameter_search` runs seeds over
//! one tape until it finds parameters, gives up, or asks for a longer tape,
//! which [`entropy::serve`] supplies.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use alloc::{vec, vec::Vec};

use super::{Error, Secret};
#[cfg(target_arch = "x86_64")]
use crate::arch::dsa::{
    VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES, vg_dsa_parameter_search_mr_adx,
    vg_dsa_parameter_search_sha1_shani, vg_dsa_parameter_search_sha1_shani_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2,
    vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx,
    vg_dsa_parameter_search_sha1_shani_sha256_shani,
    vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx, vg_dsa_parameter_search_sha256_avx2,
    vg_dsa_parameter_search_sha256_avx2_mr_adx, vg_dsa_parameter_search_sha256_shani,
    vg_dsa_parameter_search_sha256_shani_mr_adx,
};
use crate::arch::dsa::{vg_dsa_parameter_search, vg_dsa_parameter_search_init};
#[cfg(target_arch = "aarch64")]
use crate::arch::dsa::{
    vg_dsa_parameter_search_sha1_sha2, vg_dsa_parameter_search_sha1_sha2_sha256_sha2,
    vg_dsa_parameter_search_sha256_sha2,
};
#[cfg(target_arch = "x86")]
use crate::arch::dsa::{
    vg_dsa_parameter_search_sha1_shani, vg_dsa_parameter_search_sha1_shani_sha256_shani,
    vg_dsa_parameter_search_sha256_shani,
};
use crate::cpu::detected;
use crate::entropy::{self, Step, Stop};
use verified_garbage_cpu::Features;

/// An implementation and its name, which the tests compare: the address of
/// a generated function is not unique, as its public function is inlined
/// into each caller (`core::ptr::fn_addr_eq`).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
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
))]
pub(super) type Named = (Search, &'static str);

/// The implementation `$f`, with its name (`Named`).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
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
))]
macro_rules! named {
    ($f:ident) => {
        ($f as Search, stringify!($f))
    };
}

#[cfg(target_arch = "x86_64")]
pub(super) type Search = unsafe fn(
    crate::dit::Dit<'_>,
    *mut u8,
    usize,
    *mut [u64; 1],
    *const u8,
    usize,
    *mut u64,
    usize,
    *mut [u64; 4],
) -> u32;

#[cfg(target_arch = "x86_64")]
pub(super) fn select(features: Features) -> Search {
    use crate::hashes::{sha1::Sha1Backend, sha256::Sha256Backend};
    select_backends(
        Sha1Backend::select(features),
        Sha256Backend::select(features),
        features.contains(VG_DSA_PARAMETER_SEARCH_MR_ADX_FEATURES),
    )
    .0
}

#[cfg(target_arch = "x86_64")]
pub(super) fn select_backends(
    sha1: crate::hashes::sha1::Sha1Backend,
    sha256: crate::hashes::sha256::Sha256Backend,
    adx: bool,
) -> Named {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    // Match the hashes' enums exhaustively so a new hash backend reaches
    // parameter generation.
    match (sha1, sha256, adx) {
        (H1::Scalar, H256::Scalar, false) => named!(vg_dsa_parameter_search),
        (H1::Scalar, H256::Scalar, true) => named!(vg_dsa_parameter_search_mr_adx),
        (H1::Scalar, H256::Avx2, false) => named!(vg_dsa_parameter_search_sha256_avx2),
        (H1::Scalar, H256::Avx2, true) => named!(vg_dsa_parameter_search_sha256_avx2_mr_adx),
        (H1::Scalar, H256::ShaNi, false) => named!(vg_dsa_parameter_search_sha256_shani),
        (H1::Scalar, H256::ShaNi, true) => named!(vg_dsa_parameter_search_sha256_shani_mr_adx),
        (H1::ShaNi, H256::Scalar, false) => named!(vg_dsa_parameter_search_sha1_shani),
        (H1::ShaNi, H256::Scalar, true) => named!(vg_dsa_parameter_search_sha1_shani_mr_adx),
        (H1::ShaNi, H256::Avx2, false) => named!(vg_dsa_parameter_search_sha1_shani_sha256_avx2),
        (H1::ShaNi, H256::Avx2, true) => {
            named!(vg_dsa_parameter_search_sha1_shani_sha256_avx2_mr_adx)
        }
        (H1::ShaNi, H256::ShaNi, false) => named!(vg_dsa_parameter_search_sha1_shani_sha256_shani),
        (H1::ShaNi, H256::ShaNi, true) => {
            named!(vg_dsa_parameter_search_sha1_shani_sha256_shani_mr_adx)
        }
    }
}

#[cfg(target_arch = "powerpc64")]
pub(super) type Search = unsafe fn(
    crate::dit::Dit<'_>,
    *mut u8,
    usize,
    *mut [u64; 1],
    *const u8,
    usize,
    *mut u64,
    usize,
    *mut [u64; 4],
) -> u32;

/// The PPC64LE implementation: neither hash has a variant there, so the
/// match names only their baselines, and a new hash backend does not compile
/// until the search handles it.
#[cfg(target_arch = "powerpc64")]
pub(super) fn select(features: Features) -> Search {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    match (H1::select(features), H256::select(features)) {
        (H1::Scalar, H256::Scalar) => vg_dsa_parameter_search,
    }
}

#[cfg(target_arch = "x86")]
pub(super) type Search = unsafe fn(
    crate::dit::Dit<'_>,
    *mut u8,
    usize,
    *mut [u64; 1],
    *const u8,
    usize,
    *mut u64,
    usize,
    *mut [u64; 4],
) -> u32;

#[cfg(target_arch = "x86")]
pub(super) fn select(features: Features) -> Search {
    use crate::hashes::{sha1::Sha1Backend, sha256::Sha256Backend};
    select_backends(
        Sha1Backend::select(features),
        Sha256Backend::select(features),
    )
    .0
}

#[cfg(target_arch = "x86")]
pub(super) fn select_backends(
    sha1: crate::hashes::sha1::Sha1Backend,
    sha256: crate::hashes::sha256::Sha256Backend,
) -> Named {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    // Match the hashes' enums exhaustively so a new hash backend reaches
    // parameter generation.
    match (sha1, sha256) {
        (H1::Scalar, H256::Scalar) => named!(vg_dsa_parameter_search),
        (H1::Scalar, H256::ShaNi) => named!(vg_dsa_parameter_search_sha256_shani),
        (H1::ShaNi, H256::Scalar) => named!(vg_dsa_parameter_search_sha1_shani),
        (H1::ShaNi, H256::ShaNi) => named!(vg_dsa_parameter_search_sha1_shani_sha256_shani),
    }
}

#[cfg(target_arch = "aarch64")]
pub(super) type Search = unsafe fn(
    crate::dit::Dit<'_>,
    *mut u8,
    usize,
    *mut [u64; 1],
    *const u8,
    usize,
    *mut u64,
    usize,
    *mut [u64; 4],
) -> u32;

#[cfg(target_arch = "aarch64")]
pub(super) fn select(features: Features) -> Search {
    use crate::hashes::{sha1::Sha1Backend, sha256::Sha256Backend};
    select_backends(
        Sha1Backend::select(features),
        Sha256Backend::select(features),
    )
    .0
}

#[cfg(target_arch = "aarch64")]
pub(super) fn select_backends(
    sha1: crate::hashes::sha1::Sha1Backend,
    sha256: crate::hashes::sha256::Sha256Backend,
) -> Named {
    use crate::hashes::{sha1::Sha1Backend as H1, sha256::Sha256Backend as H256};
    // Match the hashes' enums exhaustively so a new hash backend reaches
    // parameter generation.
    match (sha1, sha256) {
        (H1::Scalar, H256::Scalar) => named!(vg_dsa_parameter_search),
        (H1::Scalar, H256::Sha2) => named!(vg_dsa_parameter_search_sha256_sha2),
        (H1::Sha2, H256::Scalar) => named!(vg_dsa_parameter_search_sha1_sha2),
        (H1::Sha2, H256::Sha2) => named!(vg_dsa_parameter_search_sha1_sha2_sha256_sha2),
    }
}

#[cfg(target_arch = "arm")]
pub(super) type Search = unsafe fn(
    crate::dit::Dit<'_>,
    *mut u8,
    usize,
    *mut [u64; 1],
    *const u8,
    usize,
    *mut u64,
    usize,
    *mut [u64; 4],
) -> u32;

/// ARMv7: `vg_dsa_parameter_search_umaal` where the operating system runs on
/// A-profile cores alone, on CPUs with the features its `_FEATURES` constant
/// names, else the baseline.
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
pub(super) fn select(features: Features) -> Search {
    select_named(features).0
}

/// [`select`], with the implementation's name (`Named`).
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
pub(super) fn select_named(features: Features) -> Named {
    use crate::arch::dsa::VG_DSA_PARAMETER_SEARCH_UMAAL_FEATURES;
    select_backends(features.contains(VG_DSA_PARAMETER_SEARCH_UMAAL_FEATURES))
}

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
pub(super) fn select_backends(umaal: bool) -> Named {
    use crate::arch::dsa::vg_dsa_parameter_search_umaal;
    match umaal {
        false => named!(vg_dsa_parameter_search),
        true => named!(vg_dsa_parameter_search_umaal),
    }
}

#[cfg(all(
    target_arch = "arm",
    not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd"
    ))
))]
pub(super) fn select(_features: Features) -> Search {
    vg_dsa_parameter_search
}

/// The search's buffers and state, for one modulus width.
struct Searcher {
    state: [u64; 4],
    packed: Vec<u8>,
    scratch: Secret<u64>,
    search: Search,
}

impl Searcher {
    fn new(dit: crate::dit::Dit<'_>, p_len: usize, q_len: usize) -> Self {
        let mut state = [0u64; 4];
        // SAFETY: `state` is four writable words of its own.
        let ok = unsafe { vg_dsa_parameter_search_init(dit, &mut state, p_len) };
        // The caller chose one of the three supported widths.
        assert_eq!(ok, 1);
        Self {
            state,
            packed: vec![0; 2 * p_len + q_len],
            scratch: Secret(vec![0u64; 64 * p_len + 1024]),
            search: select(detected()),
        }
    }

    /// One call on `tape`: the status and the octets consumed.
    fn run(&mut self, dit: crate::dit::Dit<'_>, tape: &[u8]) -> (u32, usize) {
        assert!(tape.len() <= self.state[2] as usize);
        let mut used = [0u64; 1];
        // SAFETY: `state` came from `vg_dsa_parameter_search_init` or the
        // last call, which returned 0; `packed` has `2 * p_len + q_len`
        // bytes, `scratch` `64 * p_len + 1024` words, the tape is at most the
        // budget, and every buffer is a distinct owned allocation. Selection
        // checked the CPU features.
        let status = unsafe {
            (self.search)(
                dit,
                self.packed.as_mut_ptr(),
                self.packed.len(),
                &mut used,
                tape.as_ptr(),
                tape.len(),
                self.scratch.0.as_mut_ptr(),
                self.scratch.0.len(),
                &mut self.state,
            )
        };
        (status, used[0] as usize)
    }
}

/// `p || q || g` for the widths `p_len` and `q_len`, from the random octets
/// `random` supplies, refilled as the search asks.
pub(super) fn generate(
    dit: crate::dit::Dit<'_>,
    p_len: usize,
    q_len: usize,
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    let mut searcher = Searcher::new(dit, p_len, q_len);
    entropy::serve(searcher.state[3] as usize, random, |tape| {
        match searcher.run(dit, tape) {
            (1, _) => Step::Done,
            (0, used) => Step::More {
                used,
                requested: searcher.state[3] as usize,
            },
            _ => Step::Failed,
        }
    })
    .map_err(|stop| match stop {
        Stop::Failed => Error::InvalidKeyOrNonce,
        Stop::Fill(e) => e,
    })?;
    Ok(core::mem::take(&mut searcher.packed))
}

#[cfg(test)]
mod tests;
