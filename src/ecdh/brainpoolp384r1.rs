//! ECDH over brainpoolP384r1 (`vg_ecdh_brainpoolp384r1`), and its `_umaal`
//! variant on ARMv7 CPUs with the features its `_FEATURES` constant names.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::ecdh_brainpoolp384r1::vg_ecdh_brainpoolp384r1;
#[cfg(target_arch = "arm")]
use crate::arch::ecdh_brainpoolp384r1::vg_ecdh_brainpoolp384r1_umaal;
use crate::cpu::detected;
use crate::ec::BrainpoolP384r1;
use crate::ec::brainpoolp384r1::Mul;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for BrainpoolP384r1 {
    fn exchange(d: &[u8; 48], peer: &[u8; 97]) -> Option<[u8; 48]> {
        let mut out = [0; 48];
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `out` is valid for reads and writes of 48 bytes,
            // `d` for reads of 48, `peer` for reads of 97 and
            // `scratch` for reads and writes of 8192; `out` and `scratch`
            // are distinct objects from each other and the others, so none
            // overlaps another or the call's stack frame, and, as Rust
            // objects, none wraps around the address space.
            Mul::Baseline => unsafe { vg_ecdh_brainpoolp384r1(&mut out, d, peer, &mut scratch) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
            // (`Mul::select`).
            #[cfg(target_arch = "arm")]
            Mul::Umaal => unsafe { vg_ecdh_brainpoolp384r1_umaal(&mut out, d, peer, &mut scratch) },
        };
        zeroize(&mut scratch);
        (ok == 1).then_some(out)
    }
}
