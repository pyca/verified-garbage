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
mov x26, x1
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
.globl lab_win_adds10
lab_win_adds10:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add10
lab_win_add10:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_adds20
lab_win_adds20:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add20
lab_win_add20:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_adds30
lab_win_adds30:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add30
lab_win_add30:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_adds40
lab_win_adds40:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add40
lab_win_add40:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_adds50
lab_win_adds50:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add50
lab_win_add50:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_adds60
lab_win_adds60:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
adds x12, x3, x3
adds x13, x3, x3
adds x14, x3, x3
adds x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_win_add60
lab_win_add60:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
umulh x4, x4, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
add x12, x3, x3
add x13, x3, x3
add x14, x3, x3
add x15, x3, x3
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_mulA
lab_mulA:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
adc x21, x16, x10
ldr x3, [x0, #328]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adc x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adc x22, x22, x16
ldr x3, [x0, #336]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adc x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adc x23, x23, x16
ldr x3, [x0, #344]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adc x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adc x24, x24, x16
mov w11, #38
mul x2, x11, x21
mul x8, x11, x22
mul x9, x11, x23
mul x16, x11, x24
umulh x21, x11, x21
umulh x22, x11, x22
umulh x23, x11, x23
umulh x24, x11, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
mov w11, #19
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
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
.globl lab_mulA_dep
lab_mulA_dep:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mov w10, #0
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
ldr x3, [x0, #224]
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
adc x21, x16, x10
ldr x3, [x0, #232]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x21, x21, x16
adc x22, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adc x22, x22, x16
ldr x3, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x21, x21, x9
adcs x22, x22, x16
adc x23, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adc x23, x23, x16
ldr x3, [x0, #248]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x7, x7, x2
adcs x21, x21, x8
adcs x22, x22, x9
adcs x23, x23, x16
adc x24, x10, x10
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adc x24, x24, x16
mov w11, #38
mul x2, x11, x21
mul x8, x11, x22
mul x9, x11, x23
mul x16, x11, x24
umulh x21, x11, x21
umulh x22, x11, x22
umulh x23, x11, x23
umulh x24, x11, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
mov w11, #19
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
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
.globl lab_mulT
lab_mulT:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
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
umulh x21, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adc x21, x21, x10
ldr x3, [x0, #328]
mul x16, x3, x12
mul x17, x3, x13
mul x20, x3, x14
mul x22, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x23, x3, x15
adds x17, x17, x2
adcs x20, x20, x8
adcs x22, x22, x9
adc x23, x23, x10
adds x5, x5, x16
adcs x6, x6, x17
adcs x7, x7, x20
adcs x21, x21, x22
adc x23, x23, x10
ldr x3, [x0, #336]
mul x1, x3, x12
mul x11, x3, x13
mul x16, x3, x14
mul x17, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x20, x3, x15
adds x11, x11, x2
adcs x16, x16, x8
adcs x17, x17, x9
adc x20, x20, x10
adds x6, x6, x1
adcs x7, x7, x11
adcs x21, x21, x16
adcs x23, x23, x17
adc x20, x20, x10
ldr x3, [x0, #344]
mul x1, x3, x12
mul x11, x3, x13
mul x16, x3, x14
mul x17, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x24, x3, x15
adds x11, x11, x2
adcs x16, x16, x8
adcs x17, x17, x9
adc x24, x24, x10
adds x7, x7, x1
adcs x21, x21, x11
adcs x23, x23, x16
adcs x20, x20, x17
adc x24, x24, x10
mov w11, #38
mul x2, x11, x21
mul x8, x11, x23
mul x9, x11, x20
mul x16, x11, x24
umulh x21, x11, x21
umulh x23, x11, x23
umulh x20, x11, x20
umulh x24, x11, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x20
adc x24, x24, x10
mov w11, #19
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x23
adc x7, x7, x10
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
.globl lab_mulT_dep
lab_mulT_dep:
stp x19, x20, [sp, #-96]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
mov x25, x1
mov x26, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
mov w10, #0
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
ldr x3, [x0, #224]
mul x4, x3, x12
mul x5, x3, x13
mul x6, x3, x14
mul x7, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x21, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adc x21, x21, x10
ldr x3, [x0, #232]
mul x16, x3, x12
mul x17, x3, x13
mul x20, x3, x14
mul x22, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x23, x3, x15
adds x17, x17, x2
adcs x20, x20, x8
adcs x22, x22, x9
adc x23, x23, x10
adds x5, x5, x16
adcs x6, x6, x17
adcs x7, x7, x20
adcs x21, x21, x22
adc x23, x23, x10
ldr x3, [x0, #240]
mul x1, x3, x12
mul x11, x3, x13
mul x16, x3, x14
mul x17, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x20, x3, x15
adds x11, x11, x2
adcs x16, x16, x8
adcs x17, x17, x9
adc x20, x20, x10
adds x6, x6, x1
adcs x7, x7, x11
adcs x21, x21, x16
adcs x23, x23, x17
adc x20, x20, x10
ldr x3, [x0, #248]
mul x1, x3, x12
mul x11, x3, x13
mul x16, x3, x14
mul x17, x3, x15
umulh x2, x3, x12
umulh x8, x3, x13
umulh x9, x3, x14
umulh x24, x3, x15
adds x11, x11, x2
adcs x16, x16, x8
adcs x17, x17, x9
adc x24, x24, x10
adds x7, x7, x1
adcs x21, x21, x11
adcs x23, x23, x16
adcs x20, x20, x17
adc x24, x24, x10
mov w11, #38
mul x2, x11, x21
mul x8, x11, x23
mul x9, x11, x20
mul x16, x11, x24
umulh x21, x11, x21
umulh x23, x11, x23
umulh x20, x11, x20
umulh x24, x11, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x20
adc x24, x24, x10
mov w11, #19
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x23
adc x7, x7, x10
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
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_win_adds10(p: *mut u64, n: u64);fn lab_win_add10(p: *mut u64, n: u64);fn lab_win_adds20(p: *mut u64, n: u64);fn lab_win_add20(p: *mut u64, n: u64);fn lab_win_adds30(p: *mut u64, n: u64);fn lab_win_add30(p: *mut u64, n: u64);fn lab_win_adds40(p: *mut u64, n: u64);fn lab_win_add40(p: *mut u64, n: u64);fn lab_win_adds50(p: *mut u64, n: u64);fn lab_win_add50(p: *mut u64, n: u64);fn lab_win_adds60(p: *mut u64, n: u64);fn lab_win_add60(p: *mut u64, n: u64);fn lab_mulA(p: *mut u64, n: u64);fn lab_mulA_dep(p: *mut u64, n: u64);fn lab_mulT(p: *mut u64, n: u64);fn lab_mulT_dep(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds10"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds10(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add10"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add10(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds20"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds20(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add20"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add20(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds30"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds30(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add30"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add30(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds40"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds40(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add40"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add40(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds50"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds50(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add50"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add50(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_adds60"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_adds60(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_win_add60"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_win_add60(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mulA"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mulA(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mulA_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mulA_dep(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mulT"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mulT(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mulT_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mulT_dep(p, 100) })); g.finish();
}