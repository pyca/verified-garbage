//! ECDH over P-192.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::align::CacheAligned;
use crate::arch::dispatch::ecdh_p192::vg_ecdh_p192_auto;
use crate::ec::P192;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for P192 {
    fn exchange(dit: crate::dit::Dit<'_>, d: &[u8; 24], peer: &[u8; 49]) -> Option<[u8; 24]> {
        let mut out = [0; 24];
        let mut scratch = CacheAligned([0u64; 1024]);
        // SAFETY: `out` is valid for reads and writes of 24 bytes, `d`
        // for reads of 24, `peer` for reads of 49 and `scratch` for reads
        // and writes of 8192; `out` and `scratch` are distinct objects from
        // each other and the others, so none overlaps another or the call's
        // stack frame, and, as Rust objects, none wraps around the address
        // space.
        let ok = unsafe { vg_ecdh_p192_auto(dit, &mut out, d, peer, &mut scratch.0) };
        zeroize(&mut scratch.0);
        (ok == 1).then_some(out)
    }
}
