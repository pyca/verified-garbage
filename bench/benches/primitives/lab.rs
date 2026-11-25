//! Lab.
use criterion::{BenchmarkId, Criterion};
use crate::{BenchDyn, VG};
pub const USES: &[&str] = &["x25519"];
core::arch::global_asm!(r".p2align 6
.globl lab_clk_add100
lab_clk_add100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
add x2, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_mul50_adds50
lab_mix_mul50_adds50:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
mul x6, x2, x3
adds x14, x2, x3
mul x7, x2, x3
adds x15, x2, x3
mul x4, x2, x3
adds x12, x2, x3
mul x5, x2, x3
adds x13, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_mul50_add50
lab_mix_mul50_add50:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_mul50_add100
lab_mix_mul50_add100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
mul x6, x2, x3
add x14, x2, x3
add x14, x2, x3
mul x7, x2, x3
add x15, x2, x3
add x15, x2, x3
mul x4, x2, x3
add x12, x2, x3
add x12, x2, x3
mul x5, x2, x3
add x13, x2, x3
add x13, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_mul100_chain4x25
lab_mix_mul100_chain4x25:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_mul50_chain4x25
lab_mix_mul50_chain4x25:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
mul x4, x2, x3
mul x5, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mix_add100_chain4x25
lab_mix_add100_chain4x25:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x14, x2, x3
adcs x15, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_chain8x12
lab_chain8x12:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adds x12, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
adcs x13, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_chain4x25_dst
lab_chain4x25_dst:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
adds x12, x12, x3
adcs x13, x13, x3
adcs x14, x14, x3
adcs x15, x15, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_adc_nochain100
lab_adc_nochain100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
adc x8, x2, x3
adc x9, x2, x3
adc x10, x2, x3
adc x11, x2, x3
adc x4, x2, x3
adc x5, x2, x3
adc x6, x2, x3
adc x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_adcs_nochain_src100
lab_adcs_nochain_src100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
cmp x2, x3
adcs x4, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_adds_dep_mul
lab_adds_dep_mul:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
mul x6, x2, x3
adds x14, x6, x3
mul x7, x2, x3
adds x15, x7, x3
mul x4, x2, x3
adds x12, x4, x3
mul x5, x2, x3
adds x13, x5, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_nop100
lab_nop100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
nop
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mov100
lab_mov100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
mov w8, #38
mov w9, #38
mov w10, #38
mov w11, #38
mov w4, #38
mov w5, #38
mov w6, #38
mov w7, #38
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_ldr_thr100
lab_ldr_thr100:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
ldr x8, [x0, #64]
ldr x9, [x0, #64]
ldr x10, [x0, #64]
ldr x11, [x0, #64]
ldr x4, [x0, #64]
ldr x5, [x0, #64]
ldr x6, [x0, #64]
ldr x7, [x0, #64]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_mix_mul50_adds50(p: *mut u64, n: u64);fn lab_mix_mul50_add50(p: *mut u64, n: u64);fn lab_mix_mul50_add100(p: *mut u64, n: u64);fn lab_mix_mul100_chain4x25(p: *mut u64, n: u64);fn lab_mix_mul50_chain4x25(p: *mut u64, n: u64);fn lab_mix_add100_chain4x25(p: *mut u64, n: u64);fn lab_chain8x12(p: *mut u64, n: u64);fn lab_chain4x25_dst(p: *mut u64, n: u64);fn lab_adc_nochain100(p: *mut u64, n: u64);fn lab_adcs_nochain_src100(p: *mut u64, n: u64);fn lab_adds_dep_mul(p: *mut u64, n: u64);fn lab_nop100(p: *mut u64, n: u64);fn lab_mov100(p: *mut u64, n: u64);fn lab_ldr_thr100(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_mul50_adds50"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_mul50_adds50(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_mul50_add50"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_mul50_add50(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_mul50_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_mul50_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_mul100_chain4x25"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_mul100_chain4x25(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_mul50_chain4x25"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_mul50_chain4x25(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mix_add100_chain4x25"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mix_add100_chain4x25(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_chain8x12"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_chain8x12(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_chain4x25_dst"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_chain4x25_dst(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adc_nochain100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adc_nochain100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adcs_nochain_src100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adcs_nochain_src100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adds_dep_mul"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adds_dep_mul(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_nop100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_nop100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mov100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mov100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ldr_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ldr_thr100(p, 100) })); g.finish();
}