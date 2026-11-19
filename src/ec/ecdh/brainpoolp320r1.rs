//! ECDH over brainpoolP320r1.

#![cfg(target_arch = "x86_64")]

use crate::align::CacheAligned;
use crate::arch::dispatch::ecdh_brainpoolp320r1::vg_ecdh_brainpoolp320r1_auto;
use crate::ec::BrainpoolP320r1;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for BrainpoolP320r1 {
    fn exchange(dit: crate::dit::Dit<'_>, d: &[u8; 40], peer: &[u8; 81]) -> Option<[u8; 40]> {
        let mut out = [0; 40];
        let mut scratch = CacheAligned([0u64; 1024]);
        // SAFETY: `out` is valid for reads and writes of 40 bytes, `d` for
        // reads of 40, `peer` for reads of 81 and `scratch` for reads and
        // writes of 8192; `out` and `scratch` are distinct objects from each
        // other and the others, so none overlaps another or the call's stack
        // frame, and, as Rust objects, none wraps around the address space. The
        // dispatcher calls only an implementation the CPU has the features of.
        let ok = unsafe { vg_ecdh_brainpoolp320r1_auto(dit, &mut out, d, peer, &mut scratch.0) };
        zeroize(&mut scratch.0);
        (ok == 1).then_some(out)
    }
}
