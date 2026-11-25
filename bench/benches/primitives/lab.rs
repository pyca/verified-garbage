//! Lab.
use criterion::{BenchmarkId, Criterion};
use crate::{BenchDyn, VG};
pub const USES: &[&str] = &["x25519"];
core::arch::global_asm!(r".p2align 6
.globl lab_clk_add100
lab_clk_add100:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r_now
lab_r_now:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r0
lab_r0:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r1
lab_r1:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r2
lab_r2:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r3
lab_r3:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r4
lab_r4:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r5
lab_r5:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r6
lab_r6:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r7
lab_r7:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r8
lab_r8:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r9
lab_r9:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r10
lab_r10:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r11
lab_r11:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r12
lab_r12:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r13
lab_r13:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r14
lab_r14:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r15
lab_r15:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r16
lab_r16:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r17
lab_r17:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r18
lab_r18:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r19
lab_r19:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r20
lab_r20:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r21
lab_r21:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r22
lab_r22:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret

.p2align 6
.globl lab_r23
lab_r23:
stp x19, x20, [sp, #-160]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp x27, x28, [sp, #136]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
str x1, [sp, #128]
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
adc x21, x16, x10
ldr x3, [x0, #296]
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
ldr x3, [x0, #304]
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
ldr x3, [x0, #312]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #384]
stp x6, x7, [x0, #400]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
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
adc x21, x16, x10
ldr x3, [x0, #360]
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
ldr x3, [x0, #368]
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
ldr x3, [x0, #376]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #96]
stp x6, x7, [x0, #112]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
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
adc x21, x16, x10
ldr x3, [x0, #424]
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
ldr x3, [x0, #432]
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
ldr x3, [x0, #440]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
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
adc x21, x9, x10
mul x2, x13, x14
mul x8, x13, x15
umulh x9, x13, x14
umulh x16, x13, x15
adds x7, x7, x2
adcs x21, x21, x8
adc x22, x16, x10
adds x21, x21, x9
adc x22, x22, x10
mul x2, x14, x15
umulh x8, x14, x15
adds x22, x22, x2
adc x23, x8, x10
adds x5, x5, x5
adcs x6, x6, x6
adcs x7, x7, x7
adcs x21, x21, x21
adcs x22, x22, x22
adcs x23, x23, x23
adc x24, x10, x10
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
adc x24, x24, x11
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x12, x13, [x0, #192]
ldp x14, x15, [x0, #208]
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
adc x21, x16, x10
ldr x3, [x0, #72]
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
ldr x3, [x0, #80]
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
ldr x3, [x0, #88]
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
movz w11, #38, lsl #0
mul x2, x11, x21
adds x4, x4, x2
mul x8, x11, x22
adcs x5, x5, x8
mul x9, x11, x23
adcs x6, x6, x9
mul x16, x11, x24
adcs x7, x7, x16
adc x20, x10, x10
umulh x2, x11, x21
umulh x8, x11, x22
umulh x9, x11, x23
umulh x16, x11, x24
adds x7, x7, x9
adc x20, x20, x16
adds x16, x7, x7
adc x9, x20, x20
lsr x7, x16, #1
movz w11, #19, lsl #0
mul x9, x9, x11
adds x4, x4, x9
adcs x5, x5, x2
adcs x6, x6, x8
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldr x25, [sp, #128]
sub x25, x25, #1
str x25, [sp, #128]
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x27, x28, [sp, #136]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #160
ret
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_r_now(p: *mut u64, n: u64);fn lab_r0(p: *mut u64, n: u64);fn lab_r1(p: *mut u64, n: u64);fn lab_r2(p: *mut u64, n: u64);fn lab_r3(p: *mut u64, n: u64);fn lab_r4(p: *mut u64, n: u64);fn lab_r5(p: *mut u64, n: u64);fn lab_r6(p: *mut u64, n: u64);fn lab_r7(p: *mut u64, n: u64);fn lab_r8(p: *mut u64, n: u64);fn lab_r9(p: *mut u64, n: u64);fn lab_r10(p: *mut u64, n: u64);fn lab_r11(p: *mut u64, n: u64);fn lab_r12(p: *mut u64, n: u64);fn lab_r13(p: *mut u64, n: u64);fn lab_r14(p: *mut u64, n: u64);fn lab_r15(p: *mut u64, n: u64);fn lab_r16(p: *mut u64, n: u64);fn lab_r17(p: *mut u64, n: u64);fn lab_r18(p: *mut u64, n: u64);fn lab_r19(p: *mut u64, n: u64);fn lab_r20(p: *mut u64, n: u64);fn lab_r21(p: *mut u64, n: u64);fn lab_r22(p: *mut u64, n: u64);fn lab_r23(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r_now"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r_now(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r3"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r3(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r4"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r4(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r5"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r5(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r6"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r6(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r7"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r7(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r8"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r8(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r9"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r9(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r10"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r10(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r11"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r11(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r12"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r12(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r13"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r13(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r14"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r14(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r15"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r15(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r16"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r16(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r17"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r17(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r18"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r18(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r19"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r19(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r20"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r20(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r21"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r21(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r22"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r22(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_r23"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_r23(p, 100) })); g.finish();
}