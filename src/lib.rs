//! An experimental, formally verified cryptography library, implemented
//! entirely by LLMs.
//!
//! Each primitive is assembly proven in Lean to be correct, memory safe and
//! constant time, and the public APIs are Rust that composes them. The README
//! says what the constant-time guarantee assumes, and a module's or item's
//! documentation says when an operation's timing may depend on more than its
//! public inputs; `lean/README.md` says what is proven and what has to be
//! trusted.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

mod cpu;

// The verified assembly of the architecture being compiled for:
// `crate::arch::<module>` is the module of the target's crate of generated
// code (`verified_garbage_asm_<target>::<module>`), so a module
// that runs the same functions on every architecture it supports imports
// them once (and supporting another architecture changes only its
// `#![cfg(...)]`).
#[cfg(target_arch = "aarch64")]
use verified_garbage_asm_aarch64 as arch;
#[cfg(target_arch = "arm")]
use verified_garbage_asm_arm as arch;
#[cfg(all(target_arch = "powerpc64", target_endian = "little"))]
use verified_garbage_asm_powerpc64le as arch;
#[cfg(all(target_arch = "riscv64", target_endian = "little"))]
use verified_garbage_asm_riscv64 as arch;
#[cfg(target_arch = "x86")]
use verified_garbage_asm_x86 as arch;
#[cfg(target_arch = "x86_64")]
use verified_garbage_asm_x86_64 as arch;

// The ISA models are little-endian, and the contracts assume the pointer
// width of each architecture's calling convention: the verified assembly is
// compiled only where both hold (each target's `rustCfg`, in
// `lean/VerifiedGarbage/TCB/<Target>/Target.lean`), not on aarch64_be, armeb,
// big-endian powerpc64 or riscv64, or x32. This `compile_error!` and those below each mirror a condition of a
// `rustCfg`.
#[cfg(any(
    all(
        any(
            target_arch = "aarch64",
            target_arch = "arm",
            target_arch = "powerpc64",
            target_arch = "riscv64"
        ),
        target_endian = "big"
    ),
    all(
        any(target_arch = "aarch64", target_arch = "x86_64"),
        target_pointer_width = "32"
    ),
))]
compile_error!(
    "the verified assembly needs a little-endian target with its architecture's usual pointer width (not, e.g., aarch64_be, powerpc64 or x32)"
);

// The RISC-V model's multiplies are the M extension's (see
// `lean/VerifiedGarbage/TCB/RISCV64/Isa.lean`), which every RV64 target Rust
// has enables.
#[cfg(all(target_arch = "riscv64", not(target_feature = "m")))]
compile_error!("64-bit RISC-V needs the M extension (e.g. riscv64gc-unknown-linux-gnu)");

// The RISC-V code uses the C extension's compressed encodings (see
// `lean/VerifiedGarbage/TCB/RISCV64/Encode.lean`), which every `riscv64gc`
// target has.
#[cfg(all(target_arch = "riscv64", not(target_feature = "c")))]
compile_error!("64-bit RISC-V needs the C extension (e.g. riscv64gc-unknown-linux-gnu)");

// The 32-bit x86 model's baseline is i686 with SSE2 (see
// `lean/VerifiedGarbage/TCB/X86/Isa.lean`): older CPUs' `mul` is not constant
// time.
#[cfg(all(target_arch = "x86", not(target_feature = "sse2")))]
compile_error!("32-bit x86 needs an i686 target with SSE2 (e.g. i686-unknown-linux-gnu)");

// The x86-64 model's baseline includes SSE2, as the System V psABI's does,
// but `x86_64-unknown-none` and `x86_64-unknown-uefi` turn it off (and the
// Rust code there would not save the SSE registers the functions use, some of
// which UEFI's calling convention makes callee-saved).
#[cfg(all(target_arch = "x86_64", not(target_feature = "sse2")))]
compile_error!(
    "x86-64 needs a target with SSE2 (not, e.g., x86_64-unknown-none or x86_64-unknown-uefi)"
);

// The AArch64 model's baseline includes AdvSIMD (NEON), which
// `aarch64-unknown-none-softfloat` turns off.
#[cfg(all(target_arch = "aarch64", not(target_feature = "neon")))]
compile_error!("AArch64 needs a target with NEON (not, e.g., aarch64-unknown-none-softfloat)");

// The ARM model's calling convention is AAPCS; Apple's 32-bit ARM targets use
// APCS (armv7s-apple-ios) or AAPCS16 (armv7k-apple-watchos), which pass some
// arguments elsewhere.
#[cfg(all(target_arch = "arm", target_vendor = "apple"))]
compile_error!("32-bit ARM needs an AAPCS target (not Apple's armv7s or armv7k)");

pub mod aead;
pub mod cipher;
pub mod cmac;
mod ct;
mod dit;
pub mod dsa;
pub mod ec;
pub mod ed25519;
pub mod ed448;
mod entropy;
pub mod error;
pub mod ffdh;
pub mod hashes;
pub mod hmac;
pub mod kdf;
pub mod mldsa44;
pub mod mldsa65;
pub mod mldsa87;
mod mldsa_common;
pub mod mlkem1024;
pub mod mlkem768;
mod mlkem_common;
pub mod poly1305;
pub mod rsa;
pub mod x25519;
pub mod x448;
mod zeroize;

#[cfg(test)]
mod tests {
    /// The pipeline self-test artifact (`VG.Spec.Selftest.addContract`).
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn selftest_add_x86_64() {
        let dit = crate::dit::public(crate::dit::Why::Test);
        let cases = [
            (0, 0),
            (1, 2),
            (u64::MAX, 1),
            (u64::MAX, u64::MAX),
            (0x8000_0000_0000_0000, 0x8000_0000_0000_0000),
            (0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210),
        ];
        for (a, b) in cases {
            // SAFETY: the contract has no preconditions.
            let r = unsafe { crate::arch::selftest::vg_selftest_add(dit, a, b) };
            assert_eq!(r, a.wrapping_add(b));
        }
    }
}
