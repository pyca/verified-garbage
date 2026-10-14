//! An experimental, formally verified cryptography library, implemented
//! entirely by LLMs.
//!
//! The cryptographic primitives are assembly that has been formally verified
//! in Lean (see `lean/README.md` for what is proven and what has to be
//! trusted). They live in naked functions in the generated `asm` module, and
//! the public APIs compose them.

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "cpu-features-env")]
extern crate std;

mod asm;
mod cpu;

// The verified assembly of the architecture being compiled for:
// `crate::arch::<module>` is `crate::asm::<target>::<module>`, so a module
// that runs the same functions on every architecture it supports imports
// them once (and supporting another architecture changes only its
// `#![cfg(...)]`).
#[cfg(target_arch = "aarch64")]
use asm::aarch64 as arch;
#[cfg(target_arch = "arm")]
use asm::arm as arch;
#[cfg(target_arch = "x86")]
use asm::x86 as arch;
#[cfg(target_arch = "x86_64")]
use asm::x86_64 as arch;

// The ISA models are little-endian, and the contracts assume the pointer
// width of each architecture's calling convention: the verified assembly is
// compiled only where both hold (each target's `rustCfg`, in
// `lean/VerifiedGarbage/TCB/<Target>/Target.lean`), not on aarch64_be, armeb
// or x32. This `compile_error!` and those below each mirror a condition of a
// `rustCfg`.
#[cfg(any(
    all(
        any(target_arch = "aarch64", target_arch = "arm"),
        target_endian = "big"
    ),
    all(
        any(target_arch = "aarch64", target_arch = "x86_64"),
        target_pointer_width = "32"
    ),
))]
compile_error!(
    "the verified assembly needs a little-endian target with its architecture's usual pointer width (not, e.g., aarch64_be or x32)"
);

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

mod aes;
pub mod aes_cbc;
pub mod aes_ccm;
pub mod aes_cfb;
pub mod aes_cfb8;
pub mod aes_ctr;
pub mod aes_ecb;
pub mod aes_gcm;
pub mod aes_gcm_siv;
pub mod aes_ocb;
pub mod aes_ofb;
pub mod aes_siv;
pub mod aes_xts;
pub mod argon2;
pub mod blowfish_cbc;
pub mod blowfish_cfb;
pub mod blowfish_ecb;
pub mod blowfish_ofb;
pub mod camellia_cbc;
pub mod camellia_cfb;
pub mod camellia_ctr;
pub mod camellia_ecb;
pub mod camellia_ofb;
pub mod cast5_cbc;
pub mod cast5_cfb;
pub mod cast5_ecb;
pub mod cast5_ofb;
pub mod chacha20;
pub mod chacha20poly1305;
pub mod cmac;
mod ct;
pub mod dsa;
mod ec;
pub mod ecdh;
pub mod ecdsa;
pub mod ed25519;
pub mod ed448;
pub mod ffdh;
pub mod hashes;
pub mod hmac;
pub mod idea_cbc;
pub mod idea_cfb;
pub mod idea_ecb;
pub mod idea_ofb;
pub mod mldsa44;
pub mod mldsa65;
pub mod mldsa87;
mod mldsa_common;
pub mod mlkem1024;
pub mod mlkem768;
mod mlkem_common;
pub mod pbkdf2;
pub mod poly1305;
pub mod rc2_cbc;
pub mod rc4;
pub mod rsa;
pub mod rsa_keygen;
pub mod rsa_oaep;
pub mod rsa_pkcs1_enc;
pub mod rsa_pkcs1_sig;
pub mod rsa_pss;
pub mod scrypt;
pub mod seed_cbc;
pub mod seed_cfb;
pub mod seed_ecb;
pub mod seed_ofb;
pub mod sm4_cbc;
pub mod sm4_cfb;
pub mod sm4_ctr;
pub mod sm4_ecb;
pub mod sm4_ofb;
pub mod triple_des_cbc;
pub mod triple_des_cfb;
pub mod triple_des_cfb8;
pub mod triple_des_ecb;
pub mod triple_des_ofb;
pub mod x25519;
pub mod x448;
mod zeroize;

#[cfg(test)]
mod aes_blocks_tests;

#[cfg(test)]
mod argon2_compress_tests;

#[cfg(test)]
mod argon2_hprime_tests;

#[cfg(test)]
mod tests {
    /// The pipeline self-test artifact (`VG.Spec.Selftest.addContract`).
    #[cfg(target_arch = "x86_64")]
    #[test]
    fn selftest_add_x86_64() {
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
            let r = unsafe { crate::asm::x86_64::selftest::vg_selftest_add(a, b) };
            assert_eq!(r, a.wrapping_add(b));
        }
    }
}

/// Measurement only: code that shifts the addresses of the functions after it.
#[doc(hidden)]
#[inline(never)]
pub fn __placement_pad(mut x: u64) -> u64 {
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 19088744);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 38177487);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 57266230);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 76354973);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 95443716);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 114532459);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 133621202);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 152709945);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 171798688);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 190887431);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 209976174);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 229064917);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 248153660);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 267242403);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 286331146);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 305419889);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 324508632);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 343597375);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 362686118);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 381774861);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 400863604);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 419952347);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 439041090);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 458129833);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 477218576);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 496307319);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 515396062);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 534484805);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 553573548);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 572662291);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 591751034);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 610839777);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 629928520);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 649017263);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 668106006);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 687194749);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 706283492);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 725372235);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 744460978);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 763549721);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 782638464);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 801727207);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 820815950);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 839904693);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 858993436);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 878082179);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 897170922);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 916259665);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 935348408);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 954437151);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 973525894);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 992614637);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1011703380);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1030792123);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1049880866);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1068969609);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1088058352);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1107147095);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1126235838);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 1145324581);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 1164413324);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1183502067);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1202590810);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1221679553);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1240768296);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1259857039);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1278945782);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1298034525);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 1317123268);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 1336212011);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1355300754);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1374389497);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1393478240);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1412566983);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1431655726);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1450744469);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1469833212);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 1488921955);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 1508010698);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1527099441);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1546188184);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1565276927);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1584365670);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1603454413);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1622543156);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1641631899);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 1660720642);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 1679809385);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1698898128);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1717986871);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1737075614);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1756164357);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1775253100);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1794341843);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1813430586);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 1832519329);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 1851608072);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 1870696815);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 1889785558);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 1908874301);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 1927963044);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 1947051787);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 1966140530);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 1985229273);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2004318016);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2023406759);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2042495502);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2061584245);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2080672988);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2099761731);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2118850474);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2137939217);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 2157027960);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2176116703);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2195205446);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2214294189);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2233382932);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2252471675);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2271560418);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2290649161);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2309737904);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 2328826647);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2347915390);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2367004133);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2386092876);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2405181619);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2424270362);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2443359105);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2462447848);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2481536591);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 2500625334);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2519714077);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2538802820);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2557891563);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2576980306);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2596069049);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2615157792);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2634246535);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2653335278);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 2672424021);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2691512764);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2710601507);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2729690250);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2748778993);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2767867736);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2786956479);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2806045222);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2825133965);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 2844222708);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 2863311451);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 2882400194);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 2901488937);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 2920577680);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 2939666423);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 2958755166);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 2977843909);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 2996932652);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3016021395);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3035110138);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3054198881);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3073287624);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3092376367);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3111465110);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3130553853);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 3149642596);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 3168731339);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3187820082);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3206908825);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3225997568);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3245086311);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3264175054);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3283263797);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3302352540);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 3321441283);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 3340530026);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3359618769);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3378707512);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3397796255);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3416884998);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3435973741);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3455062484);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3474151227);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 3493239970);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 3512328713);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3531417456);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3550506199);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3569594942);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3588683685);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3607772428);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3626861171);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3645949914);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 3665038657);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 3684127400);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3703216143);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3722304886);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3741393629);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3760482372);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3779571115);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3798659858);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3817748601);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 3836837344);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 3855926087);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 3875014830);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 3894103573);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 3913192316);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 3932281059);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 3951369802);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 3970458545);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 3989547288);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4008636031);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4027724774);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4046813517);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4065902260);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4084991003);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4104079746);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4123168489);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 4142257232);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 4161345975);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4180434718);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4199523461);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4218612204);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4237700947);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4256789690);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4275878433);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4294967176);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 4314055919);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 4333144662);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4352233405);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4371322148);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4390410891);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4409499634);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4428588377);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4447677120);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4466765863);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 4485854606);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 4504943349);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4524032092);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4543120835);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4562209578);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4581298321);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4600387064);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4619475807);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4638564550);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 4657653293);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 4676742036);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4695830779);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4714919522);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4734008265);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4753097008);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4772185751);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4791274494);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4810363237);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 4829451980);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 4848540723);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 4867629466);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 4886718209);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 4905806952);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 4924895695);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 4943984438);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 4963073181);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 4982161924);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5001250667);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5020339410);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5039428153);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5058516896);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5077605639);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5096694382);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5115783125);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5134871868);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 5153960611);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5173049354);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5192138097);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5211226840);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5230315583);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5249404326);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5268493069);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5287581812);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5306670555);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 5325759298);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5344848041);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5363936784);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5383025527);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5402114270);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5421203013);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5440291756);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5459380499);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5478469242);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 5497557985);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5516646728);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5535735471);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5554824214);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5573912957);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5593001700);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5612090443);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5631179186);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5650267929);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 5669356672);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5688445415);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5707534158);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5726622901);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5745711644);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5764800387);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5783889130);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5802977873);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5822066616);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 5841155359);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 5860244102);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 5879332845);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 5898421588);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 5917510331);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 5936599074);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 5955687817);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 5974776560);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 5993865303);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6012954046);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6032042789);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6051131532);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6070220275);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6089309018);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6108397761);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6127486504);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 6146575247);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 6165663990);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6184752733);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6203841476);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6222930219);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6242018962);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6261107705);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6280196448);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6299285191);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 6318373934);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 6337462677);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6356551420);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6375640163);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6394728906);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6413817649);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6432906392);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6451995135);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6471083878);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 6490172621);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 6509261364);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6528350107);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6547438850);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6566527593);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6585616336);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6604705079);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6623793822);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6642882565);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 6661971308);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 6681060051);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6700148794);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6719237537);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6738326280);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6757415023);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6776503766);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6795592509);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6814681252);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 6833769995);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 6852858738);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 6871947481);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 6891036224);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 6910124967);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 6929213710);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 6948302453);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 6967391196);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 6986479939);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 7005568682);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 7024657425);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 7043746168);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 7062834911);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 7081923654);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 7101012397);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 7120101140);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 7139189883);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 7158278626);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 7177367369);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 7196456112);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 7215544855);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 7234633598);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 7253722341);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 7272811084);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 7291899827);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 7310988570);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 7330077313);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 7349166056);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 7368254799);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 7387343542);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 7406432285);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 7425521028);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 7444609771);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(29) ^ 7463698514);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(36) ^ 7482787257);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(43) ^ 7501876000);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(50) ^ 7520964743);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(57) ^ 7540053486);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(1) ^ 7559142229);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(8) ^ 7578230972);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(15) ^ 7597319715);
    x = core::hint::black_box(x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(22) ^ 7616408458);
    x
}
