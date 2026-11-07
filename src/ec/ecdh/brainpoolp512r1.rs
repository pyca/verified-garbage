//! ECDH over brainpoolP512r1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::ecdh_brainpoolp512r1::vg_ecdh_brainpoolp512r1_auto;
use crate::ec::BrainpoolP512r1;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for BrainpoolP512r1 {
    fn exchange(d: &[u8; 64], peer: &[u8; 129]) -> Option<[u8; 64]> {
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 64 bytes, `d` for
        // reads of 64, `peer` for reads of 129 and `scratch` for reads and
        // writes of 8192; `out` and `scratch` are distinct objects from each
        // other and the others, so none overlaps another or the call's stack
        // frame, and, as Rust objects, none wraps around the address space. The
        // dispatcher calls only an implementation the CPU has the features of.
        let ok = unsafe { vg_ecdh_brainpoolp512r1_auto(&mut out, d, peer, &mut scratch) };
        zeroize(&mut scratch);
        (ok == 1).then_some(out)
    }
}
