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
.globl lab_m51
lab_m51:
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
ldp x1, x2, [x0, #224]
ldp x3, x4, [x0, #240]
ldr x5, [x0, #256]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #320]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #328]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #336]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #344]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #352]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #448]
stp x14, x16, [x0, #464]
str x20, [x0, #480]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_m51_dep
lab_m51_dep:
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
ldp x1, x2, [x0, #224]
ldp x3, x4, [x0, #240]
ldr x5, [x0, #256]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #224]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #232]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #240]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #248]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #256]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #224]
stp x14, x16, [x0, #240]
str x20, [x0, #256]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_s51
lab_s51:
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
ldp x1, x2, [x0, #224]
ldp x3, x4, [x0, #240]
ldr x5, [x0, #256]
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #448]
stp x14, x16, [x0, #464]
str x20, [x0, #480]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_s51_dep
lab_s51_dep:
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
ldp x1, x2, [x0, #224]
ldp x3, x4, [x0, #240]
ldr x5, [x0, #256]
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #224]
stp x14, x16, [x0, #240]
str x20, [x0, #256]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_st51
lab_st51:
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
mov x19, #100
sub x19, x19, #1
add x17, x0, x19
ldrb w16, [x17, #1984]
ldrb w17, [x17, #1985]
eor x16, x16, x17
tst x16, x16
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
movk x24, #0xf, lsl #48
sub x23, x24, #36
ldr x1, [x0, #104]
ldr x2, [x0, #144]
ldr x3, [x0, #184]
ldr x4, [x0, #224]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x9, x5, x6
add x5, x5, x23
sub x5, x5, x6
add x10, x7, x8
add x7, x7, x23
sub x7, x7, x8
str x9, [x0, #264]
str x5, [x0, #304]
str x10, [x0, #344]
str x7, [x0, #384]
ldr x1, [x0, #112]
ldr x2, [x0, #152]
ldr x3, [x0, #192]
ldr x4, [x0, #232]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x9, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x10, x7, x8
add x7, x7, x24
sub x7, x7, x8
str x9, [x0, #272]
str x5, [x0, #312]
str x10, [x0, #352]
str x7, [x0, #392]
ldr x1, [x0, #120]
ldr x2, [x0, #160]
ldr x3, [x0, #200]
ldr x4, [x0, #240]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x9, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x10, x7, x8
add x7, x7, x24
sub x7, x7, x8
str x9, [x0, #280]
str x5, [x0, #320]
str x10, [x0, #360]
str x7, [x0, #400]
ldr x1, [x0, #128]
ldr x2, [x0, #168]
ldr x3, [x0, #208]
ldr x4, [x0, #248]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x9, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x10, x7, x8
add x7, x7, x24
sub x7, x7, x8
str x9, [x0, #288]
str x5, [x0, #328]
str x10, [x0, #368]
str x7, [x0, #408]
ldr x1, [x0, #136]
ldr x2, [x0, #176]
ldr x3, [x0, #216]
ldr x4, [x0, #256]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x9, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x10, x7, x8
add x7, x7, x24
sub x7, x7, x8
str x9, [x0, #296]
str x5, [x0, #336]
str x10, [x0, #376]
str x7, [x0, #416]
ldp x1, x2, [x0, #264]
ldp x3, x4, [x0, #280]
ldr x5, [x0, #296]
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #424]
stp x14, x16, [x0, #440]
str x20, [x0, #456]
ldp x1, x2, [x0, #304]
ldp x3, x4, [x0, #320]
ldr x5, [x0, #336]
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #464]
stp x14, x16, [x0, #480]
str x20, [x0, #496]
ldp x1, x2, [x0, #264]
ldp x3, x4, [x0, #280]
ldr x5, [x0, #296]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #384]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #392]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #400]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #408]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #416]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #384]
stp x14, x16, [x0, #400]
str x20, [x0, #416]
ldp x1, x2, [x0, #304]
ldp x3, x4, [x0, #320]
ldr x5, [x0, #336]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #344]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #352]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #360]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #368]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #376]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #344]
stp x14, x16, [x0, #360]
str x20, [x0, #376]
ldp x1, x2, [x0, #424]
ldp x3, x4, [x0, #440]
ldr x5, [x0, #456]
ldp x6, x7, [x0, #464]
ldp x8, x9, [x0, #480]
ldr x10, [x0, #496]
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
movk x24, #0xf, lsl #48
sub x23, x24, #36
add x1, x1, x23
sub x1, x1, x6
add x2, x2, x24
sub x2, x2, x7
add x3, x3, x24
sub x3, x3, x8
add x4, x4, x24
sub x4, x4, x9
add x5, x5, x24
sub x5, x5, x10
stp x1, x2, [x0, #304]
stp x3, x4, [x0, #320]
str x5, [x0, #336]
ldp x1, x2, [x0, #464]
ldp x3, x4, [x0, #480]
ldr x5, [x0, #496]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #424]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #432]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #440]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #448]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #456]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #104]
stp x14, x16, [x0, #120]
str x20, [x0, #136]
ldp x1, x2, [x0, #384]
ldp x3, x4, [x0, #400]
ldr x5, [x0, #416]
ldp x6, x7, [x0, #344]
ldp x8, x9, [x0, #360]
ldr x10, [x0, #376]
add x1, x1, x6
add x2, x2, x7
add x3, x3, x8
add x4, x4, x9
add x5, x5, x10
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #184]
stp x14, x16, [x0, #200]
str x20, [x0, #216]
ldp x1, x2, [x0, #384]
ldp x3, x4, [x0, #400]
ldr x5, [x0, #416]
ldp x6, x7, [x0, #344]
ldp x8, x9, [x0, #360]
ldr x10, [x0, #376]
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
movk x24, #0xf, lsl #48
sub x23, x24, #36
add x1, x1, x23
sub x1, x1, x6
add x2, x2, x24
sub x2, x2, x7
add x3, x3, x24
sub x3, x3, x8
add x4, x4, x24
sub x4, x4, x9
add x5, x5, x24
sub x5, x5, x10
mov w22, #19
add x6, x1, x1
add x7, x2, x2
mul x8, x4, x22
mul x9, x5, x22
add x24, x9, x9
mul x10, x1, x1
umulh x11, x1, x1
mul x12, x6, x2
umulh x13, x6, x2
mul x14, x6, x3
umulh x15, x6, x3
mul x16, x6, x4
umulh x17, x6, x4
mul x20, x6, x5
umulh x21, x6, x5
mul x22, x2, x24
umulh x23, x2, x24
adds x10, x10, x22
adc x11, x11, x23
mul x22, x2, x2
umulh x23, x2, x2
adds x14, x14, x22
adc x15, x15, x23
mul x22, x7, x3
umulh x23, x7, x3
adds x16, x16, x22
adc x17, x17, x23
mul x22, x7, x4
umulh x23, x7, x4
adds x20, x20, x22
adc x21, x21, x23
mul x22, x3, x24
umulh x23, x3, x24
adds x12, x12, x22
adc x13, x13, x23
mul x22, x3, x3
umulh x23, x3, x3
adds x20, x20, x22
adc x21, x21, x23
mul x22, x4, x24
umulh x23, x4, x24
adds x14, x14, x22
adc x15, x15, x23
mul x22, x5, x9
umulh x23, x5, x9
adds x16, x16, x22
adc x17, x17, x23
mul x22, x4, x8
umulh x23, x4, x8
adds x12, x12, x22
adc x13, x13, x23
add x8, x8, x8
mul x22, x8, x3
umulh x23, x8, x3
adds x10, x10, x22
adc x11, x11, x23
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #224]
stp x14, x16, [x0, #240]
str x20, [x0, #256]
ldp x20, x21, [x0, #304]
ldp x22, x23, [x0, #320]
ldr x24, [x0, #336]
ldp x1, x2, [x0, #424]
ldp x3, x4, [x0, #440]
ldr x5, [x0, #456]
mov w16, #0xdb41
movk w16, #1, lsl #16
mov x17, #0xffff
movk x17, #0xffff, lsl #16
movk x17, #0xffff, lsl #32
movk x17, #7, lsl #48
mul x6, x20, x16
mul x7, x21, x16
mul x8, x22, x16
mul x9, x23, x16
mul x10, x24, x16
umulh x11, x20, x16
umulh x12, x21, x16
umulh x13, x22, x16
umulh x14, x23, x16
umulh x15, x24, x16
extr x11, x11, x6, #51
extr x12, x12, x7, #51
extr x13, x13, x8, #51
extr x14, x14, x9, #51
extr x15, x15, x10, #51
and x6, x6, x17
and x7, x7, x17
and x8, x8, x17
and x9, x9, x17
and x10, x10, x17
mov w16, #19
mul x15, x15, x16
add x1, x1, x6
add x2, x2, x7
add x3, x3, x8
add x4, x4, x9
add x5, x5, x10
add x1, x1, x15
add x2, x2, x11
add x3, x3, x12
add x4, x4, x13
add x5, x5, x14
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #304]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #312]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #320]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #328]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #336]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #144]
stp x14, x16, [x0, #160]
str x20, [x0, #176]
ldp x1, x2, [x0, #224]
ldp x3, x4, [x0, #240]
ldr x5, [x0, #256]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #64]
mul x10, x22, x1
umulh x11, x22, x1
mul x12, x22, x2
umulh x13, x22, x2
mul x14, x22, x3
umulh x15, x22, x3
mul x16, x22, x4
umulh x17, x22, x4
mul x20, x22, x5
umulh x21, x22, x5
ldr x22, [x0, #72]
mul x23, x22, x1
umulh x24, x22, x1
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x4
umulh x24, x22, x4
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x10, x10, x23
adc x11, x11, x24
ldr x22, [x0, #80]
mul x23, x22, x1
umulh x24, x22, x1
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x3
umulh x24, x22, x3
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x12, x12, x23
adc x13, x13, x24
ldr x22, [x0, #88]
mul x23, x22, x1
umulh x24, x22, x1
adds x16, x16, x23
adc x17, x17, x24
mul x23, x22, x2
umulh x24, x22, x2
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x14, x14, x23
adc x15, x15, x24
ldr x22, [x0, #96]
mul x23, x22, x1
umulh x24, x22, x1
adds x20, x20, x23
adc x21, x21, x24
mul x23, x22, x6
umulh x24, x22, x6
adds x10, x10, x23
adc x11, x11, x24
mul x23, x22, x7
umulh x24, x22, x7
adds x12, x12, x23
adc x13, x13, x24
mul x23, x22, x8
umulh x24, x22, x8
adds x14, x14, x23
adc x15, x15, x24
mul x23, x22, x9
umulh x24, x22, x9
adds x16, x16, x23
adc x17, x17, x24
mov x1, #0xffff
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
mov w7, #19
extr x2, x11, x10, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
lsr x2, x10, #51
lsr x3, x12, #51
lsr x4, x14, #51
lsr x5, x16, #51
lsr x6, x20, #51
and x10, x10, x1
and x12, x12, x1
and x14, x14, x1
and x16, x16, x1
and x20, x20, x1
mul x6, x6, x7
add x10, x10, x6
add x12, x12, x2
add x14, x14, x3
add x16, x16, x4
add x20, x20, x5
stp x10, x12, [x0, #224]
stp x14, x16, [x0, #240]
str x20, [x0, #256]
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
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_m51(p: *mut u64, n: u64);fn lab_m51_dep(p: *mut u64, n: u64);fn lab_s51(p: *mut u64, n: u64);fn lab_s51_dep(p: *mut u64, n: u64);fn lab_st51(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_m51"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_m51(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_m51_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_m51_dep(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_s51"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_s51(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_s51_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_s51_dep(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_st51"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_st51(p, 100) })); g.finish();
}