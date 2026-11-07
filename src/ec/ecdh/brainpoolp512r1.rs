//! ECDH over brainpoolP512r1.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::ecdh_brainpoolp512r1::vg_ecdh_brainpoolp512r1;
#[cfg(target_arch = "arm")]
use crate::arch::ecdh_brainpoolp512r1::vg_ecdh_brainpoolp512r1_umaal;
use crate::cpu::detected;
use crate::ec::BrainpoolP512r1;
use crate::ec::brainpoolp512r1::Mul;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for BrainpoolP512r1 {
    fn exchange(dit: crate::dit::Dit<'_>, d: &[u8; 64], peer: &[u8; 129]) -> Option<[u8; 64]> {
        let mut out = [0; 64];
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `out` is valid for reads and writes of 64 bytes,
            // `d` for reads of 64, `peer` for reads of 129 and
            // `scratch` for reads and writes of 8192; `out` and `scratch`
            // are distinct objects from each other and the others, so none
            // overlaps another or the call's stack frame, and, as Rust
            // objects, none wraps around the address space.
            Mul::Baseline => unsafe {
                vg_ecdh_brainpoolp512r1(dit, &mut out, d, peer, &mut scratch)
            },
            // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
            // (`Mul::select`).
            #[cfg(target_arch = "arm")]
            Mul::Umaal => unsafe {
                vg_ecdh_brainpoolp512r1_umaal(dit, &mut out, d, peer, &mut scratch)
            },
        };
        zeroize(&mut scratch);
        (ok == 1).then_some(out)
    }
}
