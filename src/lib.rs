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
    x
}
