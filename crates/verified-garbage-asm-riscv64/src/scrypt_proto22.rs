//! Unproven prototype, for timing only.
#![allow(clippy::missing_safety_doc)]
#[unsafe(naked)]
pub unsafe extern "C" fn vg_p22_romix_base(b: *mut u8, r: usize, v: *mut u8, vlen: usize, t: *mut u8, save: *mut u64) {
    core::arch::naked_asm!(
        r".option push
.option arch, +m, +c
.insn 4, 0x0017b023
.insn 4, 0x0147b423
.insn 4, 0x0157b823
.insn 4, 0x0167bc23
.insn 4, 0x0377b023
.insn 4, 0x0387b423
.insn 4, 0x0397b823
.insn 4, 0x03a7bc23
.insn 2, 0x8a2a
.insn 2, 0x8ab2
.insn 2, 0x8cba
.insn 2, 0x8d3e
.insn 4, 0x00759b13
.insn 2, 0x82ae
.insn 2, 0x4305
.insn 4, 0x00d683b3
20:
.insn 2, 0x9296
.insn 2, 0x931a
.insn 4, 0x40728e33
bnez t3, 20b
.insn 4, 0x00135313
.insn 4, 0x046d3023
.insn 2, 0x8b9a
.insn 2, 0x8c56
21:
.insn 2, 0x82d2
.insn 2, 0x8362
.insn 4, 0x003b5393
22:
.insn 4, 0x0002be03
.insn 4, 0x01c33023
.insn 2, 0x02a1
.insn 2, 0x0321
.insn 2, 0x13fd
bnez t2, 22b
.insn 2, 0x8562
.insn 4, 0x007b5593
.insn 2, 0x8652
.insn 4, 0x048d0693
call {vg_scrypt_blockmix}
.insn 2, 0x9c5a
.insn 2, 0x1bfd
bnez s7, 21b
.insn 4, 0x040d3b83
.insn 4, 0xfffb8c13
23:
.insn 4, 0x016a0333
.insn 4, 0xfc030313
.insn 4, 0x00033283
.insn 4, 0x0182f2b3
.insn 4, 0x03628333
.insn 2, 0x9356
.insn 2, 0x82d2
.insn 2, 0x83e6
.insn 4, 0x003b5e13
24:
.insn 4, 0x0002be83
.insn 4, 0x00033f03
.insn 4, 0x01eeceb3
.insn 4, 0x01d3b023
.insn 2, 0x02a1
.insn 2, 0x0321
.insn 2, 0x03a1
.insn 2, 0x1e7d
bnez t3, 24b
.insn 2, 0x8566
.insn 4, 0x007b5593
.insn 2, 0x8652
.insn 4, 0x048d0693
call {vg_scrypt_blockmix}
.insn 2, 0x1bfd
bnez s7, 23b
.insn 4, 0x000d3083
.insn 4, 0x008d3a03
.insn 4, 0x010d3a83
.insn 4, 0x018d3b03
.insn 4, 0x020d3b83
.insn 4, 0x028d3c03
.insn 4, 0x030d3c83
.insn 4, 0x038d3d03
.insn 2, 0x8082
.option pop",
        vg_scrypt_blockmix = sym crate::scrypt::vg_scrypt_blockmix::vg_scrypt_blockmix,
    )
}
#[unsafe(naked)]
pub unsafe extern "C" fn vg_p22_romix_u4(b: *mut u8, r: usize, v: *mut u8, vlen: usize, t: *mut u8, save: *mut u64) {
    core::arch::naked_asm!(
        r".option push
.option arch, +m, +c
.insn 4, 0x0017b023
.insn 4, 0x0147b423
.insn 4, 0x0157b823
.insn 4, 0x0167bc23
.insn 4, 0x0377b023
.insn 4, 0x0387b423
.insn 4, 0x0397b823
.insn 4, 0x03a7bc23
.insn 2, 0x8a2a
.insn 2, 0x8ab2
.insn 2, 0x8cba
.insn 2, 0x8d3e
.insn 4, 0x00759b13
.insn 2, 0x82ae
.insn 2, 0x4305
.insn 4, 0x00d683b3
20:
.insn 2, 0x9296
.insn 2, 0x931a
.insn 4, 0x40728e33
bnez t3, 20b
.insn 4, 0x00135313
.insn 4, 0x046d3023
.insn 2, 0x8b9a
.insn 2, 0x8c56
21:
.insn 2, 0x82d2
.insn 2, 0x8362
.insn 4, 0x005b5393
22:
.insn 4, 0x0002be03
.insn 4, 0x0082be83
.insn 4, 0x0102bf03
.insn 4, 0x0182bf83
.insn 4, 0x01c33023
.insn 4, 0x01d33423
.insn 4, 0x01e33823
.insn 4, 0x01f33c23
.insn 4, 0x02028293
.insn 4, 0x02030313
.insn 2, 0x13fd
bnez t2, 22b
.insn 2, 0x8562
.insn 4, 0x007b5593
.insn 2, 0x8652
.insn 4, 0x048d0693
call {vg_scrypt_blockmix}
.insn 2, 0x9c5a
.insn 2, 0x1bfd
bnez s7, 21b
.insn 4, 0x040d3b83
.insn 4, 0xfffb8c13
23:
.insn 4, 0x016a0333
.insn 4, 0xfc030313
.insn 4, 0x00033283
.insn 4, 0x0182f2b3
.insn 4, 0x03628333
.insn 2, 0x9356
.insn 2, 0x82d2
.insn 2, 0x83e6
.insn 4, 0x005b5e13
24:
.insn 4, 0x0002be83
.insn 4, 0x00033f03
.insn 4, 0x0082bf83
.insn 4, 0x00833803
.insn 4, 0x0102b883
.insn 4, 0x01033503
.insn 4, 0x0182b583
.insn 4, 0x01833603
.insn 4, 0x01eeceb3
.insn 4, 0x010fcfb3
.insn 4, 0x00a8c8b3
.insn 2, 0x8db1
.insn 4, 0x01d3b023
.insn 4, 0x01f3b423
.insn 4, 0x0113b823
.insn 4, 0x00b3bc23
.insn 4, 0x02028293
.insn 4, 0x02030313
.insn 4, 0x02038393
.insn 2, 0x1e7d
bnez t3, 24b
.insn 2, 0x8566
.insn 4, 0x007b5593
.insn 2, 0x8652
.insn 4, 0x048d0693
call {vg_scrypt_blockmix}
.insn 2, 0x1bfd
bnez s7, 23b
.insn 4, 0x000d3083
.insn 4, 0x008d3a03
.insn 4, 0x010d3a83
.insn 4, 0x018d3b03
.insn 4, 0x020d3b83
.insn 4, 0x028d3c03
.insn 4, 0x030d3c83
.insn 4, 0x038d3d03
.insn 2, 0x8082
.option pop",
        vg_scrypt_blockmix = sym crate::scrypt::vg_scrypt_blockmix::vg_scrypt_blockmix,
    )
}
