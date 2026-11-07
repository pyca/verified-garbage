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
use crate::arch::dispatch::dsa::{vg_dsa_parameter_search_auto, vg_dsa_parameter_search_init_auto};
use crate::entropy::{self, Step, Stop};

/// The search's buffers and state, for one modulus width.
struct Searcher {
    state: [u64; 4],
    packed: Vec<u8>,
    scratch: Secret<u64>,
}

impl Searcher {
    fn new(p_len: usize, q_len: usize) -> Self {
        let mut state = [0u64; 4];
        // SAFETY: `state` is four writable words of its own.
        let ok = unsafe { vg_dsa_parameter_search_init_auto(&mut state, p_len) };
        // The caller chose one of the three supported widths.
        assert_eq!(ok, 1);
        Self {
            state,
            packed: vec![0; 2 * p_len + q_len],
            scratch: Secret(vec![0u64; 64 * p_len + 1024]),
        }
    }

    /// One call on `tape`: the status and the octets consumed.
    fn run(&mut self, tape: &[u8]) -> (u32, usize) {
        assert!(tape.len() <= self.state[2] as usize);
        let mut used = [0u64; 1];
        // SAFETY: `state` came from `vg_dsa_parameter_search_init` or the
        // last call, which returned 0; `packed` has `2 * p_len + q_len`
        // bytes, `scratch` `64 * p_len + 1024` words, the tape is at most the
        // budget, and every buffer is a distinct owned allocation. The
        // dispatcher calls only an implementation the CPU has the features of.
        let status = unsafe {
            vg_dsa_parameter_search_auto(
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
    p_len: usize,
    q_len: usize,
    random: impl FnMut(&mut [u8]) -> Result<(), Error>,
) -> Result<Vec<u8>, Error> {
    let mut searcher = Searcher::new(p_len, q_len);
    entropy::serve(searcher.state[3] as usize, random, |tape| {
        match searcher.run(tape) {
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
