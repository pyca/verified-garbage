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
.globl lab_pair
lab_pair:
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
ldr x3, [x0, #320]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #256]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2080]
adds x21, x8, x12
adcs x22, x9, x13
adcs x23, x16, x14
adc x24, x15, x10
ldr x3, [x0, #328]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #264]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x21, [x0, #2088]
adds x22, x22, x12
adcs x23, x23, x13
adcs x24, x24, x14
adc x21, x17, x15
ldr x3, [x0, #336]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #272]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x22, x22, x2
adcs x23, x23, x8
adcs x24, x24, x9
adcs x21, x21, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x22, [x0, #2096]
adds x23, x23, x12
adcs x24, x24, x13
adcs x21, x21, x14
adc x22, x17, x15
ldr x3, [x0, #344]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
ldr x3, [x0, #280]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x23, x23, x2
adcs x24, x24, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x23, [x0, #2104]
adds x24, x24, x12
adcs x21, x21, x13
adcs x22, x22, x14
adc x23, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #448]
stp x8, x9, [x0, #464]
mov w11, #38
ldp x2, x3, [x0, #2080]
ldp x8, x9, [x0, #2096]
mul x12, x11, x24
mul x13, x11, x21
mul x14, x11, x22
mul x15, x11, x23
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x24, x11, x24
umulh x21, x11, x21
umulh x22, x11, x22
umulh x23, x11, x23
adds x9, x9, x22
adc x17, x17, x23
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x24
adcs x8, x8, x21
adc x9, x9, x10
stp x2, x3, [x0, #480]
stp x8, x9, [x0, #496]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_pair_dep
lab_pair_dep:
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
ldr x3, [x0, #224]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #256]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2080]
adds x21, x8, x12
adcs x22, x9, x13
adcs x23, x16, x14
adc x24, x15, x10
ldr x3, [x0, #232]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #264]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x21, x21, x2
adcs x22, x22, x8
adcs x23, x23, x9
adcs x24, x24, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x21, [x0, #2088]
adds x22, x22, x12
adcs x23, x23, x13
adcs x24, x24, x14
adc x21, x17, x15
ldr x3, [x0, #240]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #272]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x22, x22, x2
adcs x23, x23, x8
adcs x24, x24, x9
adcs x21, x21, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x22, [x0, #2096]
adds x23, x23, x12
adcs x24, x24, x13
adcs x21, x21, x14
adc x22, x17, x15
ldr x3, [x0, #248]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
ldr x3, [x0, #280]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x23, x23, x2
adcs x24, x24, x8
adcs x21, x21, x9
adcs x22, x22, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x23, [x0, #2104]
adds x24, x24, x12
adcs x21, x21, x13
adcs x22, x22, x14
adc x23, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #224]
stp x8, x9, [x0, #240]
mov w11, #38
ldp x2, x3, [x0, #2080]
ldp x8, x9, [x0, #2096]
mul x12, x11, x24
mul x13, x11, x21
mul x14, x11, x22
mul x15, x11, x23
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x24, x11, x24
umulh x21, x11, x21
umulh x22, x11, x22
umulh x23, x11, x23
adds x9, x9, x22
adc x17, x17, x23
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x24
adcs x8, x8, x21
adc x9, x9, x10
stp x2, x3, [x0, #256]
stp x8, x9, [x0, #272]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_seqpair
lab_seqpair:
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
ldr x3, [x0, #320]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #328]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #336]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #344]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #448]
stp x8, x9, [x0, #464]
ldr x3, [x0, #256]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #264]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #272]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #280]
ldp x12, x13, [x0, #288]
ldp x14, x15, [x0, #304]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #480]
stp x8, x9, [x0, #496]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #96
ret

.p2align 6
.globl lab_seqpair_dep
lab_seqpair_dep:
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
ldr x3, [x0, #224]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #232]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #240]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #248]
ldp x12, x13, [x0, #224]
ldp x14, x15, [x0, #240]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #224]
stp x8, x9, [x0, #240]
ldr x3, [x0, #256]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x2, [x0, #2048]
adds x4, x8, x12
adcs x5, x9, x13
adcs x6, x16, x14
adc x7, x15, x10
ldr x3, [x0, #264]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x4, [x0, #2056]
adds x5, x5, x12
adcs x6, x6, x13
adcs x7, x7, x14
adc x4, x17, x15
ldr x3, [x0, #272]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x5, x5, x2
adcs x6, x6, x8
adcs x7, x7, x9
adcs x4, x4, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x5, [x0, #2064]
adds x6, x6, x12
adcs x7, x7, x13
adcs x4, x4, x14
adc x5, x17, x15
ldr x3, [x0, #280]
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
mul x2, x3, x12
mul x8, x3, x13
mul x9, x3, x14
mul x16, x3, x15
adds x6, x6, x2
adcs x7, x7, x8
adcs x4, x4, x9
adcs x5, x5, x16
adcs x17, x10, x10
umulh x12, x3, x12
umulh x13, x3, x13
umulh x14, x3, x14
umulh x15, x3, x15
str x6, [x0, #2072]
adds x7, x7, x12
adcs x4, x4, x13
adcs x5, x5, x14
adc x6, x17, x15
mov w11, #38
ldp x2, x3, [x0, #2048]
ldp x8, x9, [x0, #2064]
mul x12, x11, x7
mul x13, x11, x4
mul x14, x11, x5
mul x15, x11, x6
adds x2, x2, x12
adcs x3, x3, x13
adcs x8, x8, x14
adcs x9, x9, x15
adcs x17, x10, x10
umulh x7, x11, x7
umulh x4, x11, x4
umulh x5, x11, x5
umulh x6, x11, x6
adds x9, x9, x5
adc x17, x17, x6
adds x16, x9, x9
adc x17, x17, x17
mov w11, #19
lsr x9, x16, #1
mul x17, x17, x11
adds x2, x2, x17
adcs x3, x3, x7
adcs x8, x8, x4
adc x9, x9, x10
stp x2, x3, [x0, #256]
stp x8, x9, [x0, #272]
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
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_step(p: *mut u64, n: u64);fn lab_mul(p: *mut u64, n: u64);fn lab_pair(p: *mut u64, n: u64);fn lab_pair_dep(p: *mut u64, n: u64);fn lab_seqpair(p: *mut u64, n: u64);fn lab_seqpair_dep(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_step"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_step(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mul"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mul(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_pair"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_pair(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_pair_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_pair_dep(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_seqpair"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_seqpair(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_seqpair_dep"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_seqpair_dep(p, 100) })); g.finish();
}