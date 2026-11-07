//! ECDH over P-521.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "arm",
    target_arch = "aarch64",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::ecdh_p521::vg_ecdh_p521_auto;
use crate::ec::P521;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for P521 {
    fn exchange(dit: crate::dit::Dit<'_>, d: &[u8; 66], peer: &[u8; 133]) -> Option<[u8; 66]> {
        let mut out = [0; 66];
        let mut scratch = [0u64; 1024];
        // SAFETY: `out` is valid for reads and writes of 66 bytes, `d` for
        // reads of 66, `peer` for reads of 133 and `scratch` for reads and
        // writes of 8192; `out` and `scratch` are distinct objects from each
        // other and the others, so none overlaps another or the call's stack
        // frame, and, as Rust objects, none wraps around the address space. The
        // dispatcher calls only an implementation the CPU has the features of.
        let ok = unsafe { vg_ecdh_p521_auto(dit, &mut out, d, peer, &mut scratch) };
        zeroize(&mut scratch);
        (ok == 1).then_some(out)
    }
}
