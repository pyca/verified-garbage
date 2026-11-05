//! ECDH over P-256 (`vg_ecdh_p256`), and its variants on CPUs with the features
//! their `_FEATURES` constants name: `_adx` on x86-64, `_umaal` on ARMv7.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::ecdh_p256::vg_ecdh_p256;
#[cfg(target_arch = "x86_64")]
use crate::arch::ecdh_p256::vg_ecdh_p256_adx;
#[cfg(target_arch = "arm")]
use crate::arch::ecdh_p256::vg_ecdh_p256_umaal;
use crate::cpu::detected;
use crate::ec::P256;
use crate::ec::p256::Mul;
use crate::ec::sealed::Exchange;
use crate::zeroize::zeroize;

impl Exchange for P256 {
    fn exchange(d: &[u8; 32], peer: &[u8; 65]) -> Option<[u8; 32]> {
        let mut out = [0; 32];
        let mut scratch = [0u64; 1024];
        let ok = match Mul::select(detected()) {
            // SAFETY: `out` is valid for reads and writes of 32 bytes,
            // `d` for reads of 32, `peer` for reads of 65 and `scratch`
            // for reads and writes of 8192; `out` and `scratch` are distinct
            // objects from each other and the others, so none overlaps
            // another or the call's stack frame, and, as Rust objects, none
            // wraps around the address space.
            Mul::Baseline => unsafe { vg_ecdh_p256(&mut out, d, peer, &mut scratch) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has BMI2 and ADX
            // (`Mul::select`).
            #[cfg(target_arch = "x86_64")]
            Mul::Adx => unsafe { vg_ecdh_p256_adx(&mut out, d, peer, &mut scratch) },
            // SAFETY: as for `Mul::Baseline`, and the CPU has `umaal`
            // (`Mul::select`).
            #[cfg(target_arch = "arm")]
            Mul::Umaal => unsafe { vg_ecdh_p256_umaal(&mut out, d, peer, &mut scratch) },
        };
        zeroize(&mut scratch);
        (ok == 1).then_some(out)
    }
}
