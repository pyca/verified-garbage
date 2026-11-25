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
.globl lab_mul_thr100
lab_mul_thr100:
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
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
mul x8, x2, x3
mul x9, x2, x3
mul x10, x2, x3
mul x11, x2, x3
mul x4, x2, x3
mul x5, x2, x3
mul x6, x2, x3
mul x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_umulh_thr100
lab_umulh_thr100:
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
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
umulh x8, x2, x3
umulh x9, x2, x3
umulh x10, x2, x3
umulh x11, x2, x3
umulh x4, x2, x3
umulh x5, x2, x3
umulh x6, x2, x3
umulh x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mulpair_thr50
lab_mulpair_thr50:
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
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
mul x6, x2, x3
umulh x14, x2, x3
mul x7, x2, x3
umulh x15, x2, x3
mul x8, x2, x3
umulh x12, x2, x3
mul x9, x2, x3
umulh x13, x2, x3
mul x10, x2, x3
umulh x14, x2, x3
mul x11, x2, x3
umulh x15, x2, x3
mul x4, x2, x3
umulh x12, x2, x3
mul x5, x2, x3
umulh x13, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mul_lat100
lab_mul_lat100:
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
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
mul x2, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_umulh_lat100
lab_umulh_lat100:
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
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
umulh x2, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_umull_thr100
lab_umull_thr100:
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
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
umull x8, w2, w3
umull x9, w2, w3
umull x10, w2, w3
umull x11, w2, w3
umull x4, w2, w3
umull x5, w2, w3
umull x6, w2, w3
umull x7, w2, w3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_madd_thr100
lab_madd_thr100:
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
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
madd x8, x2, x3, x8
madd x9, x2, x3, x9
madd x10, x2, x3, x10
madd x11, x2, x3, x11
madd x4, x2, x3, x4
madd x5, x2, x3, x5
madd x6, x2, x3, x6
madd x7, x2, x3, x7
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_umaddl_thr100
lab_umaddl_thr100:
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
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
umaddl x8, w2, w3, x8
umaddl x9, w2, w3, x9
umaddl x10, w2, w3, x10
umaddl x11, w2, w3, x11
umaddl x4, w2, w3, x4
umaddl x5, w2, w3, x5
umaddl x6, w2, w3, x6
umaddl x7, w2, w3, x7
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_adcs_chain100
lab_adcs_chain100:
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
adds x4, x4, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
adcs x7, x7, x2
adcs x8, x8, x2
adcs x9, x9, x2
adcs x10, x10, x2
adcs x11, x11, x2
adcs x4, x4, x2
adcs x5, x5, x2
adcs x6, x6, x2
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_adcs_indep25x4
lab_adcs_indep25x4:
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
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
adc x7, x2, x3
adds x4, x2, x3
adcs x5, x2, x3
adcs x6, x2, x3
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
.globl lab_adds_indep100
lab_adds_indep100:
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
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
adds x8, x2, x3
adds x9, x2, x3
adds x10, x2, x3
adds x11, x2, x3
adds x4, x2, x3
adds x5, x2, x3
adds x6, x2, x3
adds x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_add_thr100
lab_add_thr100:
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
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
add x8, x2, x3
add x9, x2, x3
add x10, x2, x3
add x11, x2, x3
add x4, x2, x3
add x5, x2, x3
add x6, x2, x3
add x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_addlsl_thr100
lab_addlsl_thr100:
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
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
add x8, x2, x3, lsl #13
add x9, x2, x3, lsl #13
add x10, x2, x3, lsl #13
add x11, x2, x3, lsl #13
add x4, x2, x3, lsl #13
add x5, x2, x3, lsl #13
add x6, x2, x3, lsl #13
add x7, x2, x3, lsl #13
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_csel_thr100
lab_csel_thr100:
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
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
csel x8, x2, x3, ne
csel x9, x2, x3, ne
csel x10, x2, x3, ne
csel x11, x2, x3, ne
csel x4, x2, x3, ne
csel x5, x2, x3, ne
csel x6, x2, x3, ne
csel x7, x2, x3, ne
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_extr_thr100
lab_extr_thr100:
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
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
extr x8, x2, x3, #7
extr x9, x2, x3, #7
extr x10, x2, x3, #7
extr x11, x2, x3, #7
extr x4, x2, x3, #7
extr x5, x2, x3, #7
extr x6, x2, x3, #7
extr x7, x2, x3, #7
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_lsr_thr100
lab_lsr_thr100:
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
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
lsr x8, x2, #7
lsr x9, x2, #7
lsr x10, x2, #7
lsr x11, x2, #7
lsr x4, x2, #7
lsr x5, x2, #7
lsr x6, x2, #7
lsr x7, x2, #7
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_ldp_thr100
lab_ldp_thr100:
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
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
ldp x4, x5, [x0, #64]
ldp x6, x7, [x0, #64]
ldp x8, x9, [x0, #64]
ldp x10, x11, [x0, #64]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_stp_thr100
lab_stp_thr100:
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
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
stp x2, x3, [x0, #64]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_vumull_thr100
lab_vumull_thr100:
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
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
umull v4.2d, v16.2s, v17.2s
umull v5.2d, v16.2s, v17.2s
umull v6.2d, v16.2s, v17.2s
umull v7.2d, v16.2s, v17.2s
umull v0.2d, v16.2s, v17.2s
umull v1.2d, v16.2s, v17.2s
umull v2.2d, v16.2s, v17.2s
umull v3.2d, v16.2s, v17.2s
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_vumlal_thr100
lab_vumlal_thr100:
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
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
umlal v4.2d, v16.2s, v17.2s
umlal v5.2d, v16.2s, v17.2s
umlal v6.2d, v16.2s, v17.2s
umlal v7.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v1.2d, v16.2s, v17.2s
umlal v2.2d, v16.2s, v17.2s
umlal v3.2d, v16.2s, v17.2s
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_vumlal_lat100
lab_vumlal_lat100:
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
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
umlal v0.2d, v16.2s, v17.2s
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_vmix100
lab_vmix100:
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
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
umlal v4.2d, v16.2s, v17.2s
mul x8, x2, x3
umlal v5.2d, v16.2s, v17.2s
mul x9, x2, x3
umlal v6.2d, v16.2s, v17.2s
mul x10, x2, x3
umlal v7.2d, v16.2s, v17.2s
mul x11, x2, x3
umlal v0.2d, v16.2s, v17.2s
mul x4, x2, x3
umlal v1.2d, v16.2s, v17.2s
mul x5, x2, x3
umlal v2.2d, v16.2s, v17.2s
mul x6, x2, x3
umlal v3.2d, v16.2s, v17.2s
mul x7, x2, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_vadd_thr100
lab_vadd_thr100:
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
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
add v4.2d, v16.2d, v17.2d
add v5.2d, v16.2d, v17.2d
add v6.2d, v16.2d, v17.2d
add v7.2d, v16.2d, v17.2d
add v0.2d, v16.2d, v17.2d
add v1.2d, v16.2d, v17.2d
add v2.2d, v16.2d, v17.2d
add v3.2d, v16.2d, v17.2d
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_step
lab_step:
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
mov w10, #0
mov x19, #100
ldp x4, x5, [x0, #96]
ldp x6, x7, [x0, #112]
ldp x12, x13, [x0, #160]
ldp x14, x15, [x0, #176]
ldp x21, x22, [x0, #128]
ldp x23, x24, [x0, #144]
ldp x2, x3, [x0, #192]
ldp x8, x9, [x0, #208]
sub x19, x19, #1
add x17, x0, x19
ldrb w16, [x17, #1984]
ldrb w17, [x17, #1985]
eor x16, x16, x17
tst x16, x16
csel x11, x12, x4, ne
csel x12, x4, x12, ne
csel x4, x13, x5, ne
csel x13, x5, x13, ne
csel x5, x14, x6, ne
csel x14, x6, x14, ne
csel x6, x15, x7, ne
csel x15, x7, x15, ne
csel x7, x2, x21, ne
csel x2, x21, x2, ne
csel x21, x3, x22, ne
csel x3, x22, x3, ne
csel x22, x8, x23, ne
csel x8, x23, x8, ne
csel x23, x9, x24, ne
csel x9, x24, x9, ne
stp x2, x3, [x0, #192]
stp x8, x9, [x0, #208]
adds x16, x11, x7
adcs x17, x4, x21
movz w2, #38, lsl #0
adcs x20, x5, x22
adcs x24, x6, x23
csel x3, x2, x10, hs
adds x16, x16, x3
adcs x17, x17, x10
adc x20, x20, x10
stp x16, x17, [x0, #224]
stp x20, x24, [x0, #240]
subs x11, x11, x7
sbcs x4, x4, x21
movz w2, #38, lsl #0
sbcs x5, x5, x22
sbcs x6, x6, x23
csel x3, x10, x2, hs
subs x11, x11, x3
sbcs x4, x4, x10
sbcs x5, x5, x10
sbc x6, x6, x10
stp x11, x4, [x0, #256]
stp x5, x6, [x0, #272]
ldp x21, x22, [x0, #192]
ldp x23, x24, [x0, #208]
adds x4, x12, x21
adcs x5, x13, x22
movz w2, #38, lsl #0
adcs x6, x14, x23
adcs x7, x15, x24
csel x3, x2, x10, hs
adds x4, x4, x3
adcs x5, x5, x10
adc x6, x6, x10
stp x4, x5, [x0, #288]
stp x6, x7, [x0, #304]
subs x12, x12, x21
sbcs x13, x13, x22
movz w2, #38, lsl #0
sbcs x14, x14, x23
sbcs x15, x15, x24
csel x3, x10, x2, hs
subs x12, x12, x3
sbcs x13, x13, x10
sbcs x14, x14, x10
sbc x15, x15, x10
stp x12, x13, [x0, #320]
stp x14, x15, [x0, #336]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
ldp x4, x5, [x0, #352]
ldp x6, x7, [x0, #368]
ldp x21, x22, [x0, #384]
ldp x23, x24, [x0, #400]
subs x12, x4, x21
sbcs x13, x5, x22
movz w2, #38, lsl #0
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x2, hs
subs x12, x12, x3
sbcs x13, x13, x10
sbcs x14, x14, x10
sbc x15, x15, x10
stp x12, x13, [x0, #416]
stp x14, x15, [x0, #432]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
ldr x3, [x0, #320]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #328]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #336]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #344]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #296]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #312]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
adds x12, x4, x21
adcs x13, x5, x22
movz w2, #38, lsl #0
adcs x14, x6, x23
adcs x15, x7, x24
csel x3, x2, x10, hs
adds x12, x12, x3
adcs x13, x13, x10
adc x14, x14, x10
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
subs x12, x4, x21
sbcs x13, x5, x22
movz w2, #38, lsl #0
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x2, hs
subs x12, x12, x3
sbcs x13, x13, x10
sbcs x14, x14, x10
sbc x15, x15, x10
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
add x12, x4, #0
add x13, x5, #0
add x14, x6, #0
add x15, x7, #0
ldr x3, [x0, #64]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #72]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #80]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #88]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #384]
ldp x14, x15, [x0, #400]
ldr x3, [x0, #352]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #360]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #368]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #376]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldp x4, x5, [x0, #352]
ldp x6, x7, [x0, #368]
ldp x12, x13, [x0, #416]
ldp x14, x15, [x0, #432]
movz x11, #56129, lsl #0
movk x11, #1, lsl #16
mul x2, x12, x11
mul x3, x13, x11
mul x8, x14, x11
mul x9, x15, x11
umulh x20, x15, x11
adds x4, x4, x2
adcs x5, x5, x3
adcs x6, x6, x8
adcs x7, x7, x9
adc x20, x20, x10
umulh x2, x12, x11
umulh x3, x13, x11
umulh x8, x14, x11
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x12, x4, x9
adcs x13, x5, x2
adcs x14, x6, x3
adc x15, x7, x8
ldr x3, [x0, #416]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #424]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #432]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #440]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_sqr
lab_sqr:
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
mov w10, #0
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mul
lab_mul:
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
mov w10, #0
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
ldr x3, [x0, #320]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x16, x10
ldr x3, [x0, #328]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
ldr x3, [x0, #336]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
ldr x3, [x0, #344]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adcs x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_sqr_dep
lab_sqr_dep:
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
mov w10, #0
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x16, x10
adds x21, x21, x9
adcs x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adcs x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adcs x24, x10, x10
mul x4, x12, x12
umulh x2, x12, x12
mul x8, x13, x13
umulh x9, x13, x13
mul x16, x14, x14
umulh x17, x14, x14
mul x3, x15, x15
umulh x11, x15, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adcs x22, x22, x17
adcs x23, x23, x3
adcs x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adcs x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adcs x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x10
stp x4, x5, [x0, #224]
stp x6, x7, [x0, #240]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_front
lab_front:
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
mov w10, #0
mov x19, #100
ldp x4, x5, [x0, #96]
ldp x6, x7, [x0, #112]
ldp x12, x13, [x0, #160]
ldp x14, x15, [x0, #176]
ldp x21, x22, [x0, #128]
ldp x23, x24, [x0, #144]
ldp x2, x3, [x0, #192]
ldp x8, x9, [x0, #208]
sub x19, x19, #1
add x17, x0, x19
ldrb w16, [x17, #1984]
ldrb w17, [x17, #1985]
eor x16, x16, x17
tst x16, x16
csel x11, x12, x4, ne
csel x12, x4, x12, ne
csel x4, x13, x5, ne
csel x13, x5, x13, ne
csel x5, x14, x6, ne
csel x14, x6, x14, ne
csel x6, x15, x7, ne
csel x15, x7, x15, ne
csel x7, x2, x21, ne
csel x2, x21, x2, ne
csel x21, x3, x22, ne
csel x3, x22, x3, ne
csel x22, x8, x23, ne
csel x8, x23, x8, ne
csel x23, x9, x24, ne
csel x9, x24, x9, ne
stp x2, x3, [x0, #192]
stp x8, x9, [x0, #208]
adds x16, x11, x7
adcs x17, x4, x21
movz w2, #38, lsl #0
adcs x20, x5, x22
adcs x24, x6, x23
csel x3, x2, x10, hs
adds x16, x16, x3
adcs x17, x17, x10
adc x20, x20, x10
stp x16, x17, [x0, #224]
stp x20, x24, [x0, #240]
subs x11, x11, x7
sbcs x4, x4, x21
movz w2, #38, lsl #0
sbcs x5, x5, x22
sbcs x6, x6, x23
csel x3, x10, x2, hs
subs x11, x11, x3
sbcs x4, x4, x10
sbcs x5, x5, x10
sbc x6, x6, x10
stp x11, x4, [x0, #256]
stp x5, x6, [x0, #272]
ldp x21, x22, [x0, #192]
ldp x23, x24, [x0, #208]
adds x4, x12, x21
adcs x5, x13, x22
movz w2, #38, lsl #0
adcs x6, x14, x23
adcs x7, x15, x24
csel x3, x2, x10, hs
adds x4, x4, x3
adcs x5, x5, x10
adc x6, x6, x10
stp x4, x5, [x0, #288]
stp x6, x7, [x0, #304]
subs x12, x12, x21
sbcs x13, x13, x22
movz w2, #38, lsl #0
sbcs x14, x14, x23
sbcs x15, x15, x24
csel x3, x10, x2, hs
subs x12, x12, x3
sbcs x13, x13, x10
sbcs x14, x14, x10
sbc x15, x15, x10
stp x12, x13, [x0, #320]
stp x14, x15, [x0, #336]
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
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_mul_thr100(p: *mut u64, n: u64);fn lab_umulh_thr100(p: *mut u64, n: u64);fn lab_mulpair_thr50(p: *mut u64, n: u64);fn lab_mul_lat100(p: *mut u64, n: u64);fn lab_umulh_lat100(p: *mut u64, n: u64);fn lab_umull_thr100(p: *mut u64, n: u64);fn lab_madd_thr100(p: *mut u64, n: u64);fn lab_umaddl_thr100(p: *mut u64, n: u64);fn lab_adcs_chain100(p: *mut u64, n: u64);fn lab_adcs_indep25x4(p: *mut u64, n: u64);fn lab_adds_indep100(p: *mut u64, n: u64);fn lab_add_thr100(p: *mut u64, n: u64);fn lab_addlsl_thr100(p: *mut u64, n: u64);fn lab_csel_thr100(p: *mut u64, n: u64);fn lab_extr_thr100(p: *mut u64, n: u64);fn lab_lsr_thr100(p: *mut u64, n: u64);fn lab_ldp_thr100(p: *mut u64, n: u64);fn lab_stp_thr100(p: *mut u64, n: u64);fn lab_vumull_thr100(p: *mut u64, n: u64);fn lab_vumlal_thr100(p: *mut u64, n: u64);fn lab_vumlal_lat100(p: *mut u64, n: u64);fn lab_vmix100(p: *mut u64, n: u64);fn lab_vadd_thr100(p: *mut u64, n: u64);fn lab_step(p: *mut u64, n: u64);fn lab_sqr(p: *mut u64, n: u64);fn lab_mul(p: *mut u64, n: u64);fn lab_sqr_dep(p: *mut u64, n: u64);fn lab_front(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mul_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mul_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_umulh_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_umulh_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mulpair_thr50"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mulpair_thr50(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mul_lat100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mul_lat100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_umulh_lat100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_umulh_lat100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_umull_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_umull_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_madd_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_madd_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_umaddl_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_umaddl_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adcs_chain100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adcs_chain100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adcs_indep25x4"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adcs_indep25x4(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_adds_indep100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_adds_indep100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_add_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_add_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_addlsl_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_addlsl_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_csel_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_csel_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_extr_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_extr_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_lsr_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_lsr_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ldp_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ldp_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_stp_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_stp_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_vumull_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_vumull_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_vumlal_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_vumlal_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_vumlal_lat100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_vumlal_lat100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_vmix100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_vmix100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_vadd_thr100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_vadd_thr100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_step"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_step(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sqr"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sqr(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mul"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mul(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sqr_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sqr_dep(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_front"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_front(p, 100) })); g.finish();
}