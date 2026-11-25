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
.globl lab_st_o3
lab_st_o3:
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
ldp x4, x5, [x0, #352]
ldp x6, x7, [x0, #368]
ldp x21, x22, [x0, #384]
ldp x23, x24, [x0, #400]
subs x12, x4, x21
sbcs x13, x5, x22
mov w2, #38
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
stp x12, x13, [x0, #128]
stp x14, x15, [x0, #144]
ldp x12, x13, [x0, #128]
ldp x14, x15, [x0, #144]
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
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
subs x12, x4, x21
sbcs x13, x5, x22
mov w2, #38
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
adds x12, x4, x21
adcs x13, x5, x22
mov w2, #38
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
.globl lab_src
lab_src:
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
mov w26, #19
mov w27, #38
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
adcs x20, x5, x22
adcs x24, x6, x23
csel x3, x27, x10, hs
adds x16, x16, x3
adcs x17, x17, x10
adc x20, x20, x10
stp x16, x17, [x0, #224]
stp x20, x24, [x0, #240]
subs x11, x11, x7
sbcs x4, x4, x21
sbcs x5, x5, x22
sbcs x6, x6, x23
csel x3, x10, x27, hs
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
adcs x6, x14, x23
adcs x7, x15, x24
csel x3, x27, x10, hs
adds x4, x4, x3
adcs x5, x5, x10
adc x6, x6, x10
stp x4, x5, [x0, #288]
stp x6, x7, [x0, #304]
subs x12, x12, x21
sbcs x13, x13, x22
sbcs x14, x14, x23
sbcs x15, x15, x24
csel x3, x10, x27, hs
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
ldp x4, x5, [x0, #352]
ldp x6, x7, [x0, #368]
ldp x21, x22, [x0, #384]
ldp x23, x24, [x0, #400]
subs x12, x4, x21
sbcs x13, x5, x22
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
mul x9, x9, x26
adds x12, x4, x9
adcs x13, x5, x2
adcs x14, x6, x3
adc x15, x7, x8
stp x12, x13, [x0, #128]
stp x14, x15, [x0, #144]
ldp x12, x13, [x0, #128]
ldp x14, x15, [x0, #144]
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
stp x4, x5, [x0, #128]
stp x6, x7, [x0, #144]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
subs x12, x4, x21
sbcs x13, x5, x22
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
adds x12, x4, x21
adcs x13, x5, x22
adcs x14, x6, x23
adcs x15, x7, x24
csel x3, x27, x10, hs
adds x12, x12, x3
adcs x13, x13, x10
adc x14, x14, x10
mul x5, x12, x13
mul x6, x12, x14
mul x7, x12, x15
umulh x2, x12, x13
umulh x8, x12, x14
umulh x9, x12, x15
mul x16, x13, x14
mul x17, x13, x15
umulh x3, x13, x14
umulh x11, x13, x15
mul x20, x14, x15
umulh x23, x14, x15
adds x6, x6, x2
adcs x7, x7, x8
adc x21, x9, x10
adds x7, x7, x16
adcs x21, x21, x17
adc x22, x11, x10
adds x21, x21, x3
adcs x22, x22, x20
adc x23, x23, x10
lsr x24, x23, #63
extr x23, x23, x22, #63
extr x22, x22, x21, #63
extr x21, x21, x7, #63
extr x7, x7, x6, #63
extr x6, x6, x5, #63
lsl x5, x5, #1
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
mul x2, x27, x21
mul x8, x27, x22
mul x9, x27, x23
mul x16, x27, x24
umulh x21, x27, x21
umulh x22, x27, x22
umulh x23, x27, x23
umulh x24, x27, x24
adds x4, x4, x2
adcs x5, x5, x8
adcs x6, x6, x9
adcs x7, x7, x16
adc x24, x24, x10
adds x7, x7, x23
adc x24, x24, x10
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
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
.globl lab_sc_o1_19_50_0
lab_sc_o1_19_50_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
stp x6, x15, [x0, #256]
stp x9, x21, [x0, #224]
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x6, x16, x5
adcs x15, x1, x28
csel x9, x27, x10, hs
stp x17, x3, [x0, #240]
stp x8, x23, [x0, #272]
ldp x21, x11, [x0, #224]
subs x25, x12, x14
sbcs x24, x20, x10
sbcs x7, x13, x10
sbc x16, x4, x10
adds x5, x22, x9
adcs x28, x2, x10
adc x1, x6, x10
ldp x17, x3, [x0, #240]
stp x25, x24, [x0, #320]
stp x5, x28, [x0, #288]
stp x1, x15, [x0, #304]
stp x7, x16, [x0, #336]
ldr x8, [x0, #320]
ldr x23, [x0, #328]
ldr x12, [x0, #336]
ldr x14, [x0, #344]
umulh x20, x8, x21
umulh x13, x8, x11
umulh x4, x8, x17
umulh x22, x8, x3
mul x9, x8, x11
mul x2, x8, x17
mul x6, x8, x3
mul x25, x23, x21
mul x24, x23, x11
mul x5, x23, x17
mul x28, x23, x3
mul x1, x8, x21
adds x15, x9, x20
adcs x7, x2, x13
adcs x16, x6, x4
adc x8, x22, x10
umulh x9, x23, x21
umulh x20, x23, x11
umulh x2, x23, x17
umulh x13, x23, x3
adds x6, x15, x25
adcs x4, x7, x24
adcs x22, x16, x5
adcs x23, x8, x28
adc x25, x10, x10
mul x15, x12, x21
mul x7, x12, x11
mul x24, x12, x17
adds x16, x4, x9
adcs x5, x22, x20
adcs x8, x23, x2
adc x28, x25, x13
mul x4, x12, x3
umulh x9, x12, x21
umulh x22, x12, x11
umulh x20, x12, x17
umulh x23, x12, x3
adds x2, x16, x15
adcs x13, x5, x7
adcs x25, x8, x24
adcs x12, x28, x4
adc x16, x10, x10
ldr x15, [x0, #288]
ldp x5, x7, [x0, #256]
adds x24, x13, x9
adcs x8, x25, x22
adcs x4, x12, x20
adc x28, x16, x23
umulh x13, x15, x5
umulh x9, x15, x7
mul x22, x15, x7
mul x25, x14, x21
umulh x20, x14, x21
mul x12, x14, x11
umulh x23, x14, x11
mul x16, x14, x17
umulh x21, x14, x17
mul x11, x14, x3
adds x17, x24, x25
adcs x25, x8, x12
adcs x24, x4, x16
adcs x12, x28, x11
adc x8, x10, x10
umulh x16, x14, x3
ldr x4, [x0, #296]
adds x11, x25, x20
adcs x28, x24, x23
adcs x3, x12, x21
adc x14, x8, x16
mul x20, x4, x5
mul x25, x4, x7
ldp x23, x24, [x0, #272]
mul x21, x27, x11
umulh x12, x27, x11
mul x8, x27, x28
umulh x16, x27, x28
mul x11, x27, x3
umulh x28, x27, x3
mul x3, x27, x14
umulh x14, x27, x14
adds x21, x1, x21
adcs x1, x6, x8
adcs x6, x2, x11
adcs x8, x17, x3
adc x2, x14, x10
adds x11, x8, x28
adc x3, x2, x10
umulh x17, x15, x23
extr x14, x3, x11, #63
and x8, x11, #0x7fffffffffffffff
mul x28, x14, x26
adds x2, x21, x28
adcs x3, x1, x12
adcs x11, x6, x16
adc x14, x8, x10
umulh x21, x15, x24
mul x28, x15, x23
mul x1, x15, x24
mul x12, x15, x5
adds x6, x22, x13
adcs x16, x28, x9
adcs x8, x1, x17
adc x15, x21, x10
mul x13, x4, x23
mul x22, x4, x24
umulh x9, x4, x5
stp x2, x3, [x0, #448]
umulh x28, x4, x7
umulh x17, x4, x23
umulh x1, x4, x24
stp x11, x14, [x0, #464]
ldr x21, [x0, #304]
ldr x2, [x0, #312]
adds x3, x6, x20
adcs x4, x16, x25
adcs x11, x8, x13
adcs x14, x15, x22
adc x20, x10, x10
mul x6, x21, x5
mul x25, x21, x7
mul x16, x21, x23
adds x13, x4, x9
adcs x8, x11, x28
adcs x22, x14, x17
adc x15, x20, x1
mul x9, x21, x24
umulh x4, x21, x5
umulh x28, x21, x7
umulh x11, x21, x23
umulh x14, x21, x24
adds x17, x13, x6
adcs x20, x8, x25
adcs x1, x22, x16
adcs x21, x15, x9
adc x6, x10, x10
mul x13, x2, x5
umulh x25, x2, x5
mul x8, x2, x7
umulh x22, x2, x7
mul x16, x2, x23
umulh x15, x2, x23
adds x9, x20, x4
adcs x5, x1, x28
adcs x7, x21, x11
adc x23, x6, x14
mul x20, x2, x24
umulh x4, x2, x24
ldp x1, x28, [x0, #224]
ldp x21, x11, [x0, #240]
adds x6, x9, x13
adcs x14, x5, x8
adcs x24, x7, x16
adcs x2, x23, x20
adc x9, x10, x10
umulh x13, x1, x28
umulh x5, x1, x21
umulh x8, x1, x11
adds x7, x14, x25
adcs x16, x24, x22
adcs x20, x2, x15
adc x23, x9, x4
mul x14, x1, x21
mul x25, x1, x11
umulh x24, x28, x11
mul x22, x28, x21
adds x15, x14, x13
adcs x2, x25, x5
adc x4, x8, x10
umulh x9, x27, x23
mul x14, x27, x23
mul x13, x28, x11
adds x25, x2, x22
adcs x5, x4, x13
adc x8, x24, x10
mul x23, x27, x7
umulh x2, x27, x7
mul x22, x27, x16
umulh x4, x27, x16
mul x13, x27, x20
umulh x24, x27, x20
adds x7, x12, x23
adcs x16, x3, x22
adcs x20, x17, x13
adcs x12, x6, x14
adc x23, x9, x10
umulh x3, x28, x21
umulh x22, x21, x11
mul x13, x21, x11
adds x17, x5, x3
adcs x6, x8, x13
adc x14, x22, x10
adds x9, x12, x24
adc x5, x23, x10
mul x3, x1, x28
umulh x8, x1, x1
umulh x13, x28, x28
mul x22, x28, x28
mul x12, x1, x1
extr x24, x5, x9, #63
and x23, x9, #0x7fffffffffffffff
mul x28, x24, x26
adds x1, x7, x28
adcs x5, x16, x2
adcs x9, x20, x4
adc x24, x23, x10
umulh x7, x21, x21
mul x28, x21, x21
umulh x2, x11, x11
mul x16, x11, x11
lsr x20, x14, #63
extr x4, x14, x6, #63
extr x23, x6, x17, #63
extr x21, x17, x25, #63
extr x11, x25, x15, #63
extr x14, x15, x3, #63
lsl x6, x3, #1
stp x1, x5, [x0, #480]
stp x9, x24, [x0, #496]
adds x17, x6, x8
adcs x25, x14, x22
adcs x15, x11, x13
adcs x3, x21, x28
adcs x1, x23, x7
adcs x5, x4, x16
adc x9, x20, x2
ldp x24, x6, [x0, #256]
ldp x8, x14, [x0, #272]
umulh x22, x24, x6
umulh x11, x24, x8
umulh x13, x24, x14
mul x21, x24, x8
mul x28, x24, x14
umulh x7, x6, x14
mul x23, x6, x8
adds x16, x21, x22
adcs x4, x28, x11
adc x2, x13, x10
mul x20, x6, x14
umulh x22, x6, x8
adds x21, x4, x23
adcs x11, x2, x20
adc x28, x7, x10
umulh x13, x8, x14
mul x4, x8, x14
adds x23, x11, x22
adcs x2, x28, x4
adc x20, x13, x10
mul x7, x24, x6
umulh x22, x27, x9
mul x11, x27, x9
mul x28, x27, x3
umulh x4, x27, x3
mul x13, x27, x1
umulh x9, x27, x1
mul x3, x27, x5
umulh x1, x27, x5
adds x5, x12, x28
adcs x28, x17, x13
adcs x12, x25, x3
adcs x17, x15, x11
adc x13, x22, x10
umulh x3, x24, x24
mul x25, x24, x24
adds x11, x17, x1
adc x15, x13, x10
umulh x22, x6, x6
mul x24, x6, x6
extr x1, x15, x11, #63
and x17, x11, #0x7fffffffffffffff
mul x13, x1, x26
adds x6, x5, x13
adcs x15, x28, x4
adcs x11, x12, x9
adc x1, x17, x10
umulh x5, x8, x8
mul x13, x8, x8
umulh x28, x14, x14
mul x4, x14, x14
lsr x9, x20, #63
extr x12, x20, x2, #63
extr x17, x2, x23, #63
extr x8, x23, x21, #63
extr x14, x21, x16, #63
extr x20, x16, x7, #63
lsl x2, x7, #1
stp x6, x15, [x0, #352]
stp x11, x1, [x0, #368]
adds x23, x2, x3
adcs x21, x20, x24
adcs x16, x14, x22
adcs x7, x8, x13
adcs x6, x17, x5
adcs x15, x12, x4
adc x1, x9, x28
ldp x11, x2, [x0, #448]
ldp x3, x24, [x0, #464]
ldp x20, x22, [x0, #480]
ldp x14, x13, [x0, #496]
subs x8, x11, x20
sbcs x17, x2, x22
sbcs x5, x3, x14
sbcs x12, x24, x13
csel x4, x10, x27, hs
umulh x28, x27, x1
mul x9, x27, x1
mul x20, x27, x7
umulh x11, x27, x7
mul x22, x27, x6
umulh x2, x27, x6
mul x3, x27, x15
umulh x14, x27, x15
adds x24, x25, x20
adcs x13, x23, x22
adcs x1, x21, x3
adcs x7, x16, x9
adc x6, x28, x10
subs x15, x8, x4
sbcs x20, x17, x10
sbcs x25, x5, x10
sbc x23, x12, x10
adds x22, x7, x14
adc x21, x6, x10
umulh x3, x15, x20
umulh x9, x15, x25
umulh x16, x15, x23
mul x28, x15, x25
mul x4, x15, x23
umulh x8, x20, x23
extr x17, x21, x22, #63
and x5, x22, #0x7fffffffffffffff
mul x12, x20, x25
mul x7, x20, x23
mul x14, x17, x26
adds x6, x28, x3
adcs x21, x4, x9
adc x22, x16, x10
umulh x17, x20, x25
adds x28, x24, x14
adcs x3, x13, x11
adcs x4, x1, x2
adc x9, x5, x10
umulh x16, x25, x23
mul x24, x25, x23
mul x14, x15, x20
umulh x13, x15, x15
adds x11, x21, x12
adcs x1, x22, x7
adc x2, x8, x10
umulh x5, x20, x20
mul x21, x20, x20
umulh x12, x25, x25
mul x22, x25, x25
mul x7, x15, x15
stp x28, x3, [x0, #384]
stp x4, x9, [x0, #400]
umulh x8, x23, x23
mul x20, x23, x23
adds x25, x1, x17
adcs x15, x2, x24
adc x28, x16, x10
extr x3, x11, x6, #63
extr x4, x6, x14, #63
lsl x9, x14, #1
ldp x23, x17, [x0, #448]
ldp x1, x2, [x0, #464]
extr x24, x25, x11, #63
extr x16, x15, x25, #63
extr x6, x28, x15, #63
lsr x14, x28, #63
adds x11, x9, x13
adcs x25, x4, x21
adcs x15, x3, x5
adcs x28, x24, x22
adcs x9, x16, x12
adcs x13, x6, x20
adc x4, x14, x8
ldp x21, x3, [x0, #480]
ldp x5, x22, [x0, #496]
adds x24, x23, x21
adcs x12, x17, x3
adcs x16, x1, x5
adcs x20, x2, x22
csel x6, x27, x10, hs
umulh x8, x27, x4
mul x14, x27, x4
mul x23, x27, x28
umulh x21, x27, x28
mul x17, x27, x9
umulh x3, x27, x9
mul x1, x27, x13
umulh x5, x27, x13
adds x2, x7, x23
adcs x22, x11, x17
adcs x4, x25, x1
adcs x28, x15, x14
adc x9, x8, x10
adds x13, x24, x6
adcs x23, x12, x10
adc x7, x16, x10
umulh x11, x13, x23
umulh x17, x13, x7
umulh x1, x13, x20
adds x25, x28, x5
adc x14, x9, x10
mul x15, x13, x7
mul x8, x13, x20
umulh x24, x23, x20
mul x6, x23, x7
mul x12, x23, x20
extr x16, x14, x25, #63
and x5, x25, #0x7fffffffffffffff
adds x28, x15, x11
adcs x9, x8, x17
adc x14, x1, x10
mul x25, x16, x26
umulh x15, x23, x7
umulh x11, x7, x20
adds x8, x2, x25
adcs x17, x22, x21
adcs x1, x4, x3
adc x16, x5, x10
adds x2, x9, x6
adcs x25, x14, x12
adc x22, x24, x10
mul x21, x7, x20
mul x4, x13, x23
umulh x3, x13, x13
umulh x5, x23, x23
mul x9, x23, x23
umulh x6, x7, x7
mul x14, x7, x7
mul x12, x13, x13
stp x8, x17, [x0, #192]
stp x1, x16, [x0, #208]
adds x24, x25, x15
adcs x23, x22, x21
adc x7, x11, x10
ldr x13, [x0, #64]
umulh x8, x20, x20
mul x17, x20, x20
extr x1, x2, x28, #63
extr x16, x28, x4, #63
lsl x25, x4, #1
lsr x15, x7, #63
extr x22, x7, x23, #63
extr x21, x23, x24, #63
extr x11, x24, x2, #63
ldr x20, [x0, #72]
ldp x28, x4, [x0, #192]
adds x7, x25, x3
adcs x23, x16, x9
adcs x24, x1, x5
adcs x2, x11, x14
adcs x25, x21, x6
adcs x3, x22, x17
adc x16, x15, x8
ldp x9, x1, [x0, #208]
umulh x5, x13, x28
umulh x11, x13, x4
mul x14, x13, x4
mul x6, x20, x28
mul x21, x20, x4
mul x17, x27, x2
umulh x22, x27, x2
mul x8, x27, x25
umulh x15, x27, x25
mul x2, x27, x3
umulh x25, x27, x3
mul x3, x27, x16
umulh x16, x27, x16
adds x17, x12, x17
adcs x12, x7, x8
adcs x7, x23, x2
adcs x8, x24, x3
adc x2, x16, x10
adds x23, x8, x25
adc x24, x2, x10
umulh x3, x13, x9
extr x16, x24, x23, #63
and x25, x23, #0x7fffffffffffffff
mul x8, x16, x26
adds x2, x17, x8
adcs x24, x12, x22
adcs x23, x7, x15
adc x16, x25, x10
umulh x17, x13, x1
mul x8, x13, x9
mul x12, x13, x1
mul x22, x13, x28
adds x15, x14, x5
adcs x7, x8, x11
adcs x25, x12, x3
adc x13, x17, x10
mul x5, x20, x9
mul x14, x20, x1
umulh x8, x20, x28
stp x2, x24, [x0, #160]
umulh x11, x20, x4
umulh x12, x20, x9
umulh x3, x20, x1
stp x23, x16, [x0, #176]
ldr x17, [x0, #80]
ldr x2, [x0, #88]
adds x24, x15, x6
adcs x20, x7, x21
adcs x16, x25, x5
adcs x23, x13, x14
adc x6, x10, x10
mul x15, x17, x28
mul x21, x17, x4
mul x7, x17, x9
adds x25, x20, x8
adcs x5, x16, x11
adcs x13, x23, x12
adc x14, x6, x3
mul x20, x17, x1
umulh x8, x17, x28
umulh x16, x17, x4
umulh x11, x17, x9
umulh x23, x17, x1
adds x12, x25, x15
adcs x6, x5, x21
adcs x3, x13, x7
adcs x17, x14, x20
adc x25, x10, x10
ldp x15, x5, [x0, #352]
mul x21, x2, x28
umulh x13, x2, x28
adds x7, x6, x8
adcs x20, x3, x16
adcs x14, x17, x11
adc x28, x25, x23
ldp x6, x8, [x0, #368]
ldp x3, x16, [x0, #384]
mul x11, x2, x4
umulh x17, x2, x4
mul x23, x2, x9
umulh x25, x2, x9
mul x4, x2, x1
adds x9, x7, x21
adcs x7, x20, x11
adcs x21, x14, x23
adcs x11, x28, x4
adc x20, x10, x10
umulh x23, x2, x1
ldr x14, [x0, #352]
adds x4, x7, x13
adcs x28, x21, x17
adcs x1, x11, x25
adc x2, x20, x23
ldp x13, x7, [x0, #400]
ldp x17, x21, [x0, #384]
subs x25, x15, x3
sbcs x11, x5, x16
sbcs x23, x6, x13
sbcs x20, x8, x7
csel x3, x10, x27, hs
umulh x15, x14, x17
umulh x16, x14, x21
mul x5, x14, x21
subs x6, x25, x3
sbcs x13, x11, x10
sbcs x8, x23, x10
sbc x7, x20, x10
umulh x3, x27, x2
mul x25, x27, x2
stp x8, x7, [x0, #432]
stp x6, x13, [x0, #416]
ldp x11, x23, [x0, #400]
mul x20, x27, x4
umulh x2, x27, x4
mul x8, x27, x28
umulh x7, x27, x28
mul x6, x27, x1
umulh x13, x27, x1
adds x4, x22, x20
adcs x28, x24, x8
adcs x1, x12, x6
adcs x20, x9, x25
adc x22, x3, x10
ldr x8, [x0, #360]
mul x24, x14, x17
umulh x12, x14, x11
adds x6, x20, x13
adc x25, x22, x10
umulh x9, x14, x23
extr x3, x25, x6, #63
and x20, x6, #0x7fffffffffffffff
mul x13, x3, x26
adds x22, x4, x13
adcs x25, x28, x2
adcs x6, x1, x7
adc x3, x20, x10
mul x4, x14, x11
mul x13, x14, x23
mul x28, x8, x17
mul x2, x8, x21
adds x1, x5, x15
adcs x7, x4, x16
adcs x20, x13, x12
adc x14, x9, x10
mul x15, x8, x11
mul x5, x8, x23
umulh x16, x8, x17
stp x22, x25, [x0, #192]
umulh x4, x8, x21
umulh x12, x8, x11
umulh x13, x8, x23
stp x6, x3, [x0, #208]
ldr x9, [x0, #368]
ldr x22, [x0, #376]
adds x25, x1, x28
adcs x8, x7, x2
adcs x6, x20, x15
adcs x3, x14, x5
adc x28, x10, x10
mul x1, x9, x17
mul x2, x9, x21
mul x7, x9, x11
adds x15, x8, x16
adcs x20, x6, x4
adcs x5, x3, x12
adc x14, x28, x13
mul x16, x9, x23
umulh x8, x9, x17
umulh x4, x9, x21
umulh x6, x9, x11
umulh x3, x9, x23
adds x12, x15, x1
adcs x28, x20, x2
adcs x13, x5, x7
adcs x9, x14, x16
adc x1, x10, x10
movz x15, #56129, lsl #0
ldp x2, x20, [x0, #432]
adds x5, x28, x8
adcs x7, x13, x4
adcs x14, x9, x6
adc x16, x1, x3
movk x15, #1, lsl #16
ldp x28, x8, [x0, #416]
ldp x13, x4, [x0, #352]
mul x9, x22, x17
umulh x6, x22, x17
mul x1, x22, x21
umulh x3, x22, x21
mul x17, x22, x11
umulh x21, x22, x11
mul x11, x22, x23
adds x5, x5, x9
adcs x9, x7, x1
adcs x7, x14, x17
adcs x1, x16, x11
adc x14, x10, x10
umulh x17, x22, x23
adds x11, x9, x6
adcs x16, x7, x3
adcs x23, x1, x21
adc x22, x14, x17
umulh x9, x20, x15
mul x6, x20, x15
mul x7, x28, x15
umulh x3, x28, x15
mul x21, x8, x15
umulh x1, x8, x15
mul x17, x2, x15
umulh x14, x2, x15
umulh x20, x27, x22
mul x28, x27, x22
mul x8, x27, x11
umulh x2, x27, x11
mul x15, x27, x16
umulh x22, x27, x16
mul x11, x27, x23
umulh x16, x27, x23
adds x23, x24, x8
adcs x24, x25, x15
adcs x8, x12, x11
adcs x25, x5, x28
adc x15, x20, x10
ldr x11, [x0, #416]
adds x12, x25, x16
adc x5, x15, x10
extr x28, x5, x12, #63
and x20, x12, #0x7fffffffffffffff
mul x25, x28, x26
ldr x16, [x0, #424]
adds x15, x23, x25
adcs x5, x24, x2
adcs x12, x8, x22
adc x28, x20, x10
ldp x23, x25, [x0, #368]
stp x15, x5, [x0, #96]
stp x12, x28, [x0, #112]
adds x2, x13, x7
adcs x24, x4, x21
adcs x8, x23, x17
adcs x22, x25, x6
adc x20, x9, x10
ldr x15, [x0, #432]
adds x5, x22, x22
adc x12, x20, x20
mul x28, x12, x26
lsr x13, x5, #1
adds x7, x2, x28
adcs x4, x24, x3
adcs x21, x8, x1
adc x17, x13, x14
stp x7, x4, [x0, #128]
stp x21, x17, [x0, #144]
ldp x23, x6, [x0, #128]
ldp x25, x9, [x0, #144]
ldr x22, [x0, #440]
umulh x20, x11, x23
umulh x12, x11, x6
umulh x5, x11, x25
umulh x2, x11, x9
mul x28, x11, x6
mul x3, x11, x25
mul x24, x11, x9
mul x1, x16, x23
mul x8, x16, x6
mul x14, x16, x25
mul x13, x16, x9
mul x4, x11, x23
adds x7, x28, x20
adcs x21, x3, x12
adcs x17, x24, x5
adc x11, x2, x10
umulh x28, x16, x23
umulh x20, x16, x6
umulh x3, x16, x25
umulh x12, x16, x9
adds x24, x7, x1
adcs x5, x21, x8
adcs x2, x17, x14
adcs x16, x11, x13
adc x7, x10, x10
mul x1, x15, x23
mul x21, x15, x6
mul x8, x15, x25
adds x17, x5, x28
adcs x14, x2, x20
adcs x13, x16, x3
adc x11, x7, x12
mul x5, x15, x9
umulh x28, x15, x23
umulh x2, x15, x6
umulh x20, x15, x25
umulh x3, x15, x9
adds x16, x17, x1
adcs x12, x14, x21
adcs x7, x13, x8
adcs x15, x11, x5
adc x17, x10, x10
mul x1, x22, x23
umulh x21, x22, x23
mul x14, x22, x6
umulh x8, x22, x6
mul x13, x22, x25
umulh x5, x22, x25
adds x11, x12, x28
adcs x23, x7, x2
adcs x6, x15, x20
adc x25, x17, x3
mul x28, x22, x9
umulh x12, x22, x9
adds x2, x11, x1
adcs x7, x23, x14
adcs x20, x6, x13
adcs x15, x25, x28
adc x3, x10, x10
adds x17, x7, x21
adcs x22, x20, x8
adcs x9, x15, x5
adc x1, x3, x12
umulh x11, x27, x1
mul x14, x27, x17
mul x23, x27, x22
mul x13, x27, x9
mul x6, x27, x1
umulh x28, x27, x9
umulh x25, x27, x17
umulh x21, x27, x22
adds x7, x4, x14
adcs x8, x24, x23
adcs x20, x16, x13
adcs x15, x2, x6
adc x5, x11, x10
adds x3, x15, x28
adc x12, x5, x10
extr x1, x12, x3, #63
and x9, x3, #0x7fffffffffffffff
mul x17, x1, x26
adds x22, x7, x17
adcs x4, x8, x25
adcs x14, x20, x21
adc x24, x9, x10
stp x22, x4, [x0, #128]
stp x14, x24, [x0, #144]
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
.globl lab_sc_o1_19_50_1
lab_sc_o1_19_50_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
ldr x11, [x0, #336]
ldr x4, [x0, #344]
umulh x8, x3, x12
mul x2, x3, x24
umulh x13, x3, x24
mul x17, x3, x9
umulh x14, x3, x25
mul x1, x7, x9
umulh x6, x3, x9
mul x20, x3, x25
mul x22, x7, x25
mul x16, x7, x12
umulh x23, x7, x12
mul x15, x3, x12
adds x21, x17, x8
adcs x5, x20, x6
adcs x28, x2, x14
adc x3, x13, x10
umulh x17, x7, x9
mul x8, x7, x24
umulh x20, x7, x24
umulh x6, x7, x25
adds x2, x21, x16
adcs x14, x5, x1
adcs x13, x28, x22
adcs x7, x3, x8
adc x16, x10, x10
mul x21, x11, x12
mul x5, x11, x24
mul x1, x11, x9
adds x28, x14, x23
adcs x22, x13, x17
adcs x3, x7, x6
adc x8, x16, x20
mul x14, x11, x25
umulh x23, x11, x12
umulh x13, x11, x24
umulh x17, x11, x25
umulh x7, x11, x9
adds x6, x28, x21
adcs x20, x22, x1
adcs x16, x3, x14
adcs x11, x8, x5
adc x28, x10, x10
ldr x21, [x0, #288]
ldp x22, x1, [x0, #272]
adds x14, x20, x23
adcs x3, x16, x7
adcs x5, x11, x17
adc x8, x28, x13
mul x20, x21, x1
umulh x23, x21, x22
ldp x7, x16, [x0, #256]
mul x17, x4, x12
umulh x11, x4, x12
mul x13, x4, x9
umulh x28, x4, x9
mul x12, x4, x25
umulh x9, x4, x25
mul x25, x4, x24
adds x17, x14, x17
adcs x14, x3, x13
adcs x13, x5, x12
adcs x3, x8, x25
adc x12, x10, x10
umulh x5, x4, x24
adds x25, x14, x11
adcs x8, x13, x28
adcs x24, x3, x9
adc x4, x12, x5
umulh x11, x21, x7
umulh x14, x21, x1
mul x28, x21, x16
ldr x13, [x0, #296]
mul x9, x27, x25
umulh x3, x27, x25
mul x12, x27, x8
umulh x5, x27, x8
mul x25, x27, x24
umulh x8, x27, x24
mul x24, x27, x4
umulh x4, x27, x4
adds x9, x15, x9
adcs x15, x2, x12
adcs x2, x6, x25
adcs x12, x17, x24
adc x6, x4, x10
adds x25, x12, x8
adc x24, x6, x10
umulh x17, x21, x16
extr x4, x24, x25, #63
and x12, x25, #0x7fffffffffffffff
mul x8, x4, x26
adds x6, x9, x8
adcs x24, x15, x3
adcs x25, x2, x5
adc x4, x12, x10
mul x9, x13, x16
mul x8, x13, x22
mul x15, x21, x22
mul x3, x21, x7
adds x2, x28, x11
adcs x5, x15, x17
adcs x12, x20, x23
adc x21, x14, x10
mul x11, x13, x7
mul x28, x13, x1
umulh x17, x13, x1
stp x25, x4, [x0, #464]
ldr x15, [x0, #304]
umulh x23, x13, x22
stp x6, x24, [x0, #448]
umulh x20, x13, x7
umulh x14, x13, x16
ldr x25, [x0, #312]
adds x4, x2, x11
adcs x6, x5, x9
adcs x24, x12, x8
adcs x13, x21, x28
adc x11, x10, x10
mul x2, x15, x7
mul x9, x15, x22
mul x5, x15, x1
adds x8, x6, x20
adcs x12, x24, x14
adcs x28, x13, x23
adc x21, x11, x17
mul x20, x15, x16
umulh x6, x15, x22
umulh x14, x15, x1
umulh x24, x15, x7
umulh x13, x15, x16
adds x23, x8, x2
adcs x11, x12, x20
adcs x17, x28, x9
adcs x15, x21, x5
adc x2, x10, x10
mul x8, x25, x1
umulh x20, x25, x1
mul x12, x25, x7
umulh x28, x25, x7
umulh x9, x25, x16
mul x21, x25, x16
adds x5, x11, x24
adcs x1, x17, x13
adcs x7, x15, x6
adc x16, x2, x14
mul x11, x25, x22
umulh x24, x25, x22
ldp x17, x13, [x0, #224]
ldp x15, x6, [x0, #240]
adds x2, x5, x12
adcs x14, x1, x21
adcs x22, x7, x11
adcs x25, x16, x8
adc x5, x10, x10
umulh x12, x17, x13
mul x1, x17, x15
mul x21, x17, x6
adds x7, x14, x28
adcs x11, x22, x9
adcs x8, x25, x24
adc x16, x5, x20
umulh x14, x17, x6
umulh x28, x13, x6
umulh x22, x17, x15
mul x9, x13, x6
adds x24, x1, x12
adcs x25, x21, x22
adc x20, x14, x10
mul x5, x13, x15
mul x1, x27, x8
umulh x12, x27, x8
adds x21, x25, x5
adcs x22, x20, x9
adc x14, x28, x10
mul x8, x27, x11
umulh x25, x27, x11
umulh x5, x27, x16
mul x20, x27, x16
mul x9, x27, x7
umulh x28, x27, x7
adds x11, x3, x9
adcs x16, x4, x8
adcs x7, x23, x1
adcs x3, x2, x20
adc x9, x5, x10
umulh x4, x6, x6
umulh x8, x13, x13
umulh x1, x13, x15
adds x23, x3, x12
adc x2, x9, x10
umulh x20, x15, x6
extr x5, x2, x23, #63
and x3, x23, #0x7fffffffffffffff
mul x12, x5, x26
adds x9, x11, x12
adcs x2, x16, x28
adcs x23, x7, x25
adc x5, x3, x10
mul x11, x6, x6
mul x12, x15, x6
mul x28, x13, x13
mul x16, x17, x13
mul x7, x15, x15
umulh x25, x15, x15
adds x3, x22, x1
adcs x6, x14, x12
adc x13, x20, x10
stp x23, x5, [x0, #496]
extr x15, x21, x24, #63
extr x22, x24, x16, #63
lsl x1, x16, #1
stp x9, x2, [x0, #480]
ldp x14, x12, [x0, #272]
ldp x20, x23, [x0, #256]
umulh x5, x17, x17
mul x24, x17, x17
extr x16, x3, x21, #63
extr x9, x6, x3, #63
extr x2, x13, x6, #63
lsr x17, x13, #63
adds x21, x1, x5
adcs x3, x22, x28
adcs x6, x15, x8
adcs x13, x16, x7
adcs x1, x9, x25
adcs x5, x2, x11
adc x22, x17, x4
umulh x28, x20, x12
umulh x15, x20, x14
umulh x8, x20, x23
mul x16, x23, x12
mul x7, x20, x14
umulh x25, x23, x12
mul x9, x14, x12
mul x11, x27, x13
umulh x2, x27, x13
mul x4, x27, x1
umulh x17, x27, x1
mul x13, x27, x5
umulh x1, x27, x5
mul x5, x27, x22
umulh x22, x27, x22
adds x11, x24, x11
adcs x24, x21, x4
adcs x21, x3, x13
adcs x4, x6, x5
adc x13, x22, x10
adds x3, x4, x1
adc x5, x13, x10
mul x6, x20, x12
extr x22, x5, x3, #63
and x1, x3, #0x7fffffffffffffff
adds x4, x7, x8
adcs x13, x6, x15
adc x5, x28, x10
umulh x3, x23, x14
mul x8, x23, x14
mul x7, x22, x26
adds x15, x13, x8
adcs x6, x5, x16
adc x28, x25, x10
umulh x22, x23, x23
umulh x13, x20, x20
adds x8, x11, x7
adcs x5, x24, x2
adcs x16, x21, x17
adc x25, x1, x10
mul x11, x20, x23
mul x7, x23, x23
umulh x24, x14, x12
mul x2, x14, x14
umulh x17, x14, x14
mul x21, x20, x20
stp x8, x5, [x0, #352]
extr x1, x15, x4, #63
adds x23, x6, x3
adcs x14, x28, x9
adc x20, x24, x10
extr x8, x4, x11, #63
lsl x5, x11, #1
mul x3, x12, x12
umulh x6, x12, x12
stp x16, x25, [x0, #368]
ldp x28, x9, [x0, #480]
ldp x24, x4, [x0, #464]
extr x11, x23, x15, #63
extr x12, x14, x23, #63
extr x25, x20, x14, #63
lsr x16, x20, #63
adds x15, x5, x13
adcs x23, x8, x7
adcs x14, x1, x22
adcs x20, x11, x2
adcs x5, x12, x17
adcs x13, x25, x3
adc x7, x16, x6
ldp x8, x22, [x0, #448]
ldp x1, x2, [x0, #496]
subs x11, x8, x28
sbcs x12, x22, x9
sbcs x17, x24, x1
sbcs x25, x4, x2
csel x3, x10, x27, hs
mul x6, x27, x5
mul x16, x27, x7
umulh x28, x27, x7
mul x8, x27, x13
umulh x9, x27, x13
umulh x22, x27, x5
mul x24, x27, x20
umulh x1, x27, x20
adds x4, x21, x24
adcs x2, x15, x6
adcs x7, x23, x8
adcs x13, x14, x16
adc x5, x28, x10
subs x20, x11, x3
sbcs x24, x12, x10
sbcs x21, x17, x10
sbc x15, x25, x10
adds x6, x13, x9
adc x23, x5, x10
umulh x8, x20, x21
mul x16, x20, x21
umulh x14, x20, x15
umulh x28, x24, x15
umulh x3, x20, x24
umulh x11, x21, x15
extr x12, x23, x6, #63
and x17, x6, #0x7fffffffffffffff
mul x25, x20, x15
mul x13, x24, x15
mul x9, x12, x26
adds x5, x16, x3
adcs x23, x25, x8
adc x6, x14, x10
adds x12, x4, x9
adcs x16, x2, x1
adcs x3, x7, x22
adc x25, x17, x10
umulh x8, x15, x15
mul x14, x24, x21
umulh x4, x24, x21
mul x9, x15, x15
mul x2, x21, x15
mul x1, x24, x24
adds x7, x23, x14
adcs x22, x6, x13
adc x17, x28, x10
stp x12, x16, [x0, #384]
stp x3, x25, [x0, #400]
umulh x15, x24, x24
mul x23, x20, x24
umulh x14, x20, x20
mul x6, x20, x20
mul x13, x21, x21
umulh x28, x21, x21
ldp x12, x16, [x0, #464]
adds x3, x22, x4
adcs x25, x17, x2
adc x24, x11, x10
extr x20, x7, x5, #63
extr x21, x5, x23, #63
lsl x4, x23, #1
ldp x22, x17, [x0, #448]
extr x2, x3, x7, #63
extr x11, x25, x3, #63
extr x5, x24, x25, #63
lsr x23, x24, #63
adds x7, x4, x14
adcs x3, x21, x1
adcs x25, x20, x15
adcs x24, x2, x13
adcs x4, x11, x28
adcs x14, x5, x9
adc x21, x23, x8
ldp x1, x20, [x0, #480]
ldp x15, x13, [x0, #496]
adds x2, x22, x1
adcs x28, x17, x20
adcs x11, x12, x15
adcs x9, x16, x13
csel x5, x27, x10, hs
mul x8, x27, x21
umulh x23, x27, x21
mul x22, x27, x14
umulh x1, x27, x14
mul x17, x27, x4
umulh x20, x27, x4
mul x12, x27, x24
umulh x15, x27, x24
adds x16, x6, x12
adcs x13, x7, x17
adcs x21, x3, x22
adcs x14, x25, x8
adc x4, x23, x10
adds x24, x2, x5
adcs x12, x28, x10
adc x6, x11, x10
umulh x7, x24, x12
mul x17, x24, x6
umulh x22, x24, x9
adds x3, x14, x1
adc x8, x4, x10
umulh x25, x24, x6
mul x23, x24, x9
mul x2, x12, x6
umulh x5, x12, x9
umulh x28, x6, x9
extr x11, x8, x3, #63
and x1, x3, #0x7fffffffffffffff
mul x14, x11, x26
adds x4, x17, x7
adcs x8, x23, x25
adc x3, x22, x10
mul x11, x12, x9
umulh x17, x24, x24
adds x7, x16, x14
adcs x23, x13, x15
adcs x25, x21, x20
adc x22, x1, x10
mul x16, x24, x12
mul x14, x6, x6
adds x13, x8, x2
adcs x15, x3, x11
adc x21, x5, x10
umulh x20, x6, x6
umulh x1, x12, x12
umulh x8, x12, x6
mul x2, x6, x9
mul x3, x12, x12
mul x11, x24, x24
stp x7, x23, [x0, #192]
stp x25, x22, [x0, #208]
lsl x5, x16, #1
extr x6, x4, x16, #63
extr x12, x13, x4, #63
mul x24, x9, x9
umulh x7, x9, x9
adds x23, x15, x8
adcs x25, x21, x2
adc x22, x28, x10
ldr x16, [x0, #64]
lsr x4, x22, #63
ldp x9, x15, [x0, #192]
extr x8, x23, x13, #63
extr x21, x22, x25, #63
extr x2, x25, x23, #63
ldr x28, [x0, #72]
adds x13, x5, x17
adcs x22, x6, x3
adcs x23, x12, x1
adcs x25, x8, x14
adcs x5, x2, x20
adcs x17, x21, x24
adc x6, x4, x7
ldp x3, x12, [x0, #208]
umulh x1, x16, x9
umulh x8, x16, x15
mul x14, x16, x15
mul x20, x16, x9
mul x2, x28, x15
mul x24, x27, x25
umulh x21, x27, x25
mul x7, x27, x5
umulh x4, x27, x5
mul x25, x27, x17
umulh x5, x27, x17
mul x17, x27, x6
umulh x6, x27, x6
adds x24, x11, x24
adcs x11, x13, x7
adcs x13, x22, x25
adcs x7, x23, x17
adc x25, x6, x10
adds x22, x7, x5
adc x23, x25, x10
mul x17, x16, x3
extr x6, x23, x22, #63
and x5, x22, #0x7fffffffffffffff
mul x7, x6, x26
adds x25, x24, x7
adcs x23, x11, x21
adcs x22, x13, x4
adc x6, x5, x10
umulh x24, x16, x3
mul x7, x16, x12
umulh x11, x16, x12
mul x21, x28, x12
stp x25, x23, [x0, #160]
mul x4, x28, x3
adds x13, x14, x1
adcs x5, x17, x8
adcs x16, x7, x24
adc x25, x11, x10
mul x23, x28, x9
umulh x1, x28, x9
ldr x14, [x0, #80]
umulh x17, x28, x12
stp x22, x6, [x0, #176]
umulh x8, x28, x15
umulh x7, x28, x3
ldr x24, [x0, #88]
adds x11, x13, x23
adcs x6, x5, x2
adcs x22, x16, x4
adcs x28, x25, x21
adc x23, x10, x10
mul x13, x14, x9
mul x2, x14, x15
mul x5, x14, x3
adds x16, x6, x1
adcs x4, x22, x8
adcs x25, x28, x7
adc x21, x23, x17
umulh x6, x14, x12
umulh x1, x14, x15
mul x22, x14, x12
umulh x8, x14, x9
umulh x28, x14, x3
adds x7, x16, x13
adcs x23, x4, x2
adcs x17, x25, x5
adcs x14, x21, x22
adc x16, x10, x10
ldp x13, x4, [x0, #352]
mul x2, x24, x9
umulh x25, x24, x9
adds x5, x23, x8
adcs x22, x17, x1
adcs x21, x14, x28
adc x9, x16, x6
ldp x23, x8, [x0, #384]
ldp x17, x1, [x0, #400]
mul x28, x24, x15
umulh x14, x24, x15
mul x6, x24, x3
umulh x16, x24, x3
mul x15, x24, x12
adds x3, x5, x2
adcs x5, x22, x28
adcs x2, x21, x6
adcs x28, x9, x15
adc x22, x10, x10
umulh x6, x24, x12
ldr x21, [x0, #352]
adds x15, x5, x25
adcs x9, x2, x14
adcs x12, x28, x16
adc x24, x22, x6
ldp x25, x5, [x0, #368]
ldp x14, x2, [x0, #384]
subs x16, x13, x23
sbcs x28, x4, x8
sbcs x6, x25, x17
sbcs x22, x5, x1
csel x23, x10, x27, hs
umulh x13, x21, x14
umulh x8, x21, x2
mul x4, x21, x2
subs x25, x16, x23
sbcs x17, x28, x10
sbcs x5, x6, x10
sbc x1, x22, x10
mul x23, x27, x12
umulh x16, x27, x12
stp x5, x1, [x0, #432]
stp x25, x17, [x0, #416]
ldp x28, x6, [x0, #400]
umulh x22, x27, x24
mul x12, x27, x24
mul x5, x27, x9
umulh x1, x27, x9
mul x25, x27, x15
umulh x17, x27, x15
adds x24, x20, x25
adcs x9, x11, x5
adcs x15, x7, x23
adcs x25, x3, x12
adc x20, x22, x10
ldr x5, [x0, #360]
mul x11, x21, x14
umulh x7, x21, x28
adds x23, x25, x16
adc x12, x20, x10
umulh x3, x21, x6
extr x22, x12, x23, #63
and x25, x23, #0x7fffffffffffffff
mul x16, x22, x26
adds x20, x24, x16
adcs x12, x9, x17
adcs x23, x15, x1
adc x22, x25, x10
mul x24, x21, x6
mul x16, x21, x28
mul x9, x5, x2
mul x17, x5, x14
adds x15, x4, x13
adcs x1, x16, x8
adcs x25, x24, x7
adc x21, x3, x10
mul x13, x5, x6
mul x4, x5, x28
umulh x8, x5, x2
stp x23, x22, [x0, #208]
umulh x16, x5, x14
umulh x7, x5, x6
umulh x24, x5, x28
stp x20, x12, [x0, #192]
ldr x3, [x0, #368]
ldr x23, [x0, #376]
adds x22, x15, x17
adcs x5, x1, x9
adcs x20, x25, x4
adcs x12, x21, x13
adc x17, x10, x10
mul x15, x3, x14
mul x9, x3, x6
mul x1, x3, x28
adds x4, x5, x16
adcs x25, x20, x8
adcs x13, x12, x24
adc x21, x17, x7
mul x16, x3, x2
umulh x5, x3, x14
umulh x8, x3, x2
umulh x20, x3, x6
umulh x12, x3, x28
adds x24, x4, x15
adcs x17, x25, x16
adcs x7, x13, x1
adcs x3, x21, x9
adc x15, x10, x10
movz x4, #56129, lsl #0
ldp x16, x25, [x0, #432]
adds x13, x17, x5
adcs x1, x7, x8
adcs x21, x3, x12
adc x9, x15, x20
movk x4, #1, lsl #16
ldp x17, x5, [x0, #416]
ldp x7, x8, [x0, #368]
mul x3, x23, x14
umulh x12, x23, x14
mul x15, x23, x2
umulh x20, x23, x2
mul x14, x23, x28
umulh x2, x23, x28
mul x28, x23, x6
adds x13, x13, x3
adcs x3, x1, x15
adcs x1, x21, x14
adcs x15, x9, x28
adc x21, x10, x10
umulh x14, x23, x6
adds x28, x3, x12
adcs x9, x1, x20
adcs x6, x15, x2
adc x23, x21, x14
umulh x3, x25, x4
mul x12, x25, x4
mul x1, x16, x4
umulh x20, x16, x4
mul x2, x5, x4
umulh x15, x5, x4
mul x14, x17, x4
umulh x21, x17, x4
umulh x25, x27, x23
mul x16, x27, x23
mul x5, x27, x28
umulh x17, x27, x28
mul x4, x27, x9
umulh x23, x27, x9
mul x28, x27, x6
umulh x9, x27, x6
adds x6, x11, x5
adcs x11, x22, x4
adcs x5, x24, x28
adcs x22, x13, x16
adc x4, x25, x10
ldr x28, [x0, #416]
adds x24, x22, x9
adc x13, x4, x10
extr x16, x13, x24, #63
and x25, x24, #0x7fffffffffffffff
mul x22, x16, x26
ldr x9, [x0, #424]
adds x4, x6, x22
adcs x13, x11, x17
adcs x24, x5, x23
adc x16, x25, x10
ldp x6, x22, [x0, #352]
stp x4, x13, [x0, #96]
stp x24, x16, [x0, #112]
adds x17, x6, x14
adcs x11, x22, x2
adcs x5, x7, x1
adcs x23, x8, x12
adc x25, x3, x10
ldr x4, [x0, #432]
adds x13, x23, x23
adc x24, x25, x25
mul x16, x24, x26
lsr x6, x13, #1
adds x14, x17, x16
adcs x22, x11, x21
adcs x2, x5, x15
adc x1, x6, x20
stp x14, x22, [x0, #128]
stp x2, x1, [x0, #144]
ldp x7, x12, [x0, #128]
ldp x8, x3, [x0, #144]
ldr x23, [x0, #440]
umulh x25, x28, x7
umulh x24, x28, x8
mul x13, x28, x3
umulh x17, x28, x12
mul x16, x28, x8
umulh x21, x28, x3
mul x11, x9, x12
mul x15, x28, x12
mul x5, x9, x7
mul x20, x9, x8
mul x6, x9, x3
mul x22, x28, x7
adds x14, x15, x25
adcs x2, x16, x17
adcs x1, x13, x24
adc x28, x21, x10
umulh x15, x9, x7
umulh x25, x9, x3
umulh x16, x9, x12
umulh x17, x9, x8
adds x13, x14, x5
adcs x24, x2, x11
adcs x21, x1, x20
adcs x9, x28, x6
adc x14, x10, x10
mul x5, x4, x3
mul x2, x4, x7
mul x11, x4, x8
adds x1, x24, x15
adcs x20, x21, x16
adcs x6, x9, x17
adc x28, x14, x25
mul x24, x4, x12
umulh x15, x4, x12
umulh x21, x4, x3
umulh x16, x4, x8
umulh x17, x4, x7
adds x9, x1, x2
adcs x25, x20, x24
adcs x14, x6, x11
adcs x4, x28, x5
adc x1, x10, x10
mul x2, x23, x8
umulh x24, x23, x8
mul x20, x23, x3
umulh x11, x23, x3
mul x6, x23, x12
umulh x5, x23, x12
adds x28, x25, x17
adcs x8, x14, x15
adcs x3, x4, x16
adc x12, x1, x21
mul x17, x23, x7
umulh x25, x23, x7
adds x15, x28, x17
adcs x14, x8, x6
adcs x16, x3, x2
adcs x4, x12, x20
adc x21, x10, x10
adds x1, x14, x25
adcs x23, x16, x5
adcs x7, x4, x24
adc x17, x21, x11
umulh x28, x27, x17
mul x6, x27, x23
mul x8, x27, x1
mul x2, x27, x7
mul x3, x27, x17
umulh x20, x27, x7
umulh x12, x27, x1
umulh x25, x27, x23
adds x14, x22, x8
adcs x5, x13, x6
adcs x16, x9, x2
adcs x4, x15, x3
adc x24, x28, x10
adds x21, x4, x20
adc x11, x24, x10
extr x17, x11, x21, #63
and x7, x21, #0x7fffffffffffffff
mul x1, x17, x26
adds x23, x14, x1
adcs x22, x5, x12
adcs x8, x16, x25
adc x13, x7, x10
stp x23, x22, [x0, #128]
stp x8, x13, [x0, #144]
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
.globl lab_sc_o1_19_30_0
lab_sc_o1_19_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
stp x6, x15, [x0, #256]
stp x9, x21, [x0, #224]
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x6, x16, x5
adcs x15, x1, x28
csel x9, x27, x10, hs
stp x17, x3, [x0, #240]
stp x8, x23, [x0, #272]
ldp x21, x11, [x0, #224]
subs x25, x12, x14
sbcs x24, x20, x10
sbcs x7, x13, x10
sbc x16, x4, x10
adds x5, x22, x9
adcs x28, x2, x10
adc x1, x6, x10
ldp x17, x3, [x0, #240]
stp x25, x24, [x0, #320]
stp x5, x28, [x0, #288]
stp x1, x15, [x0, #304]
stp x7, x16, [x0, #336]
ldr x8, [x0, #320]
ldr x23, [x0, #328]
ldr x12, [x0, #336]
umulh x14, x8, x21
umulh x20, x8, x11
umulh x13, x8, x17
umulh x4, x8, x3
mul x22, x8, x11
mul x9, x8, x17
mul x2, x8, x3
mul x6, x23, x21
mul x25, x23, x11
mul x24, x23, x17
mul x5, x23, x3
umulh x28, x23, x21
mul x1, x8, x21
adds x15, x22, x14
adcs x7, x9, x20
adcs x16, x2, x13
adc x8, x4, x10
umulh x22, x23, x11
umulh x14, x23, x17
umulh x9, x23, x3
mul x20, x12, x21
adds x2, x15, x6
adcs x13, x7, x25
adcs x4, x16, x24
adcs x23, x8, x5
adc x6, x10, x10
mul x15, x12, x11
mul x7, x12, x17
mul x25, x12, x3
adds x16, x13, x28
adcs x24, x4, x22
adcs x8, x23, x14
adc x5, x6, x9
umulh x13, x12, x21
umulh x28, x12, x11
umulh x4, x12, x17
umulh x22, x12, x3
ldr x23, [x0, #344]
adds x14, x16, x20
adcs x9, x24, x15
adcs x6, x8, x7
adcs x12, x5, x25
adc x16, x10, x10
mul x20, x23, x21
umulh x24, x23, x21
mul x15, x23, x11
umulh x7, x23, x11
mul x8, x23, x17
umulh x25, x23, x17
adds x5, x9, x13
adcs x21, x6, x28
adcs x11, x12, x4
adc x17, x16, x22
mul x9, x23, x3
umulh x13, x23, x3
adds x28, x5, x20
adcs x6, x21, x15
adcs x4, x11, x8
adcs x12, x17, x9
adc x22, x10, x10
ldp x16, x3, [x0, #256]
ldr x23, [x0, #288]
ldp x20, x5, [x0, #272]
adds x15, x6, x24
adcs x21, x4, x7
adcs x8, x12, x25
adc x11, x22, x13
mul x9, x23, x3
mul x17, x23, x20
mul x24, x23, x5
mul x6, x23, x16
umulh x7, x27, x11
mul x4, x27, x11
mul x25, x27, x15
umulh x12, x27, x15
mul x22, x27, x21
umulh x13, x27, x21
mul x11, x27, x8
umulh x15, x27, x8
adds x21, x1, x25
adcs x8, x2, x22
adcs x25, x14, x11
adcs x1, x28, x4
adc x2, x7, x10
umulh x22, x23, x16
umulh x14, x23, x3
adds x11, x1, x15
adc x4, x2, x10
umulh x28, x23, x20
umulh x7, x23, x5
extr x1, x4, x11, #63
and x15, x11, #0x7fffffffffffffff
mul x2, x1, x26
adds x23, x9, x22
adcs x4, x17, x14
adcs x11, x24, x28
adc x1, x7, x10
ldr x22, [x0, #296]
adds x9, x21, x2
adcs x14, x8, x12
adcs x17, x25, x13
adc x28, x15, x10
mul x24, x22, x16
mul x7, x22, x3
mul x21, x22, x20
mul x2, x22, x5
umulh x8, x22, x16
stp x9, x14, [x0, #448]
umulh x12, x22, x3
umulh x25, x22, x20
umulh x13, x22, x5
stp x17, x28, [x0, #464]
ldr x15, [x0, #304]
adds x9, x23, x24
adcs x14, x4, x7
adcs x22, x11, x21
adcs x17, x1, x2
adc x28, x10, x10
ldr x24, [x0, #312]
mul x23, x15, x16
mul x7, x15, x3
mul x4, x15, x20
adds x21, x14, x8
adcs x11, x22, x12
adcs x2, x17, x25
adc x1, x28, x13
mul x8, x15, x5
umulh x14, x15, x16
umulh x12, x15, x3
umulh x22, x15, x20
umulh x17, x15, x5
adds x25, x21, x23
adcs x28, x11, x7
adcs x13, x2, x4
adcs x15, x1, x8
adc x23, x10, x10
mul x21, x24, x16
umulh x7, x24, x16
mul x11, x24, x3
umulh x2, x24, x3
mul x4, x24, x20
umulh x1, x24, x20
adds x8, x28, x14
adcs x16, x13, x12
adcs x3, x15, x22
adc x20, x23, x17
mul x28, x24, x5
umulh x14, x24, x5
adds x13, x8, x21
adcs x12, x16, x11
adcs x15, x3, x4
adcs x22, x20, x28
adc x23, x10, x10
ldp x17, x5, [x0, #224]
ldp x24, x8, [x0, #240]
adds x21, x12, x7
adcs x16, x15, x2
adcs x11, x22, x1
adc x3, x23, x14
umulh x4, x17, x5
umulh x28, x17, x24
mul x20, x17, x24
mul x12, x17, x8
mul x7, x17, x5
umulh x15, x27, x3
mul x2, x27, x3
mul x1, x27, x21
umulh x22, x27, x21
mul x14, x27, x16
umulh x23, x27, x16
mul x3, x27, x11
umulh x21, x27, x11
adds x16, x6, x1
adcs x11, x9, x14
adcs x6, x25, x3
adcs x1, x13, x2
adc x9, x15, x10
umulh x14, x17, x8
umulh x3, x5, x8
adds x25, x20, x4
adcs x13, x12, x28
adc x2, x14, x10
adds x15, x1, x21
adc x20, x9, x10
mul x4, x5, x24
mul x12, x5, x8
umulh x28, x5, x24
extr x14, x20, x15, #63
and x1, x15, #0x7fffffffffffffff
adds x21, x13, x4
adcs x9, x2, x12
adc x20, x3, x10
mul x15, x14, x26
umulh x13, x24, x8
mul x4, x24, x8
adds x2, x16, x15
adcs x12, x11, x22
adcs x3, x6, x23
adc x14, x1, x10
extr x16, x21, x25, #63
adds x15, x9, x28
adcs x22, x20, x4
adc x11, x13, x10
extr x6, x25, x7, #63
stp x2, x12, [x0, #480]
lsr x23, x11, #63
extr x1, x11, x22, #63
extr x9, x22, x15, #63
extr x28, x15, x21, #63
lsl x20, x7, #1
stp x3, x14, [x0, #496]
umulh x4, x17, x17
umulh x13, x5, x5
umulh x25, x24, x24
mul x2, x5, x5
mul x12, x24, x24
umulh x11, x8, x8
mul x22, x8, x8
mul x15, x17, x17
adds x21, x20, x4
adcs x7, x6, x2
adcs x3, x16, x13
adcs x14, x28, x12
adcs x5, x9, x25
adcs x24, x1, x22
adc x8, x23, x11
ldp x17, x20, [x0, #256]
ldp x4, x6, [x0, #272]
umulh x2, x17, x20
umulh x16, x17, x4
mul x13, x17, x4
mul x28, x17, x6
mul x12, x17, x20
umulh x25, x27, x8
mul x9, x27, x8
mul x22, x27, x14
umulh x1, x27, x14
mul x11, x27, x5
umulh x23, x27, x5
mul x8, x27, x24
umulh x14, x27, x24
adds x5, x15, x22
adcs x24, x21, x11
adcs x22, x7, x8
adcs x15, x3, x9
adc x21, x25, x10
umulh x11, x17, x6
umulh x8, x20, x6
adds x7, x13, x2
adcs x9, x28, x16
adc x3, x11, x10
mul x25, x20, x4
mul x2, x20, x6
adds x13, x15, x14
adc x16, x21, x10
umulh x28, x20, x4
adds x11, x9, x25
adcs x14, x3, x2
adc x15, x8, x10
umulh x21, x4, x6
mul x9, x4, x6
extr x25, x16, x13, #63
and x3, x13, #0x7fffffffffffffff
mul x2, x25, x26
adds x8, x14, x28
adcs x16, x15, x9
adc x13, x21, x10
adds x25, x5, x2
adcs x28, x24, x1
adcs x14, x22, x23
adc x15, x3, x10
extr x9, x11, x7, #63
extr x21, x7, x12, #63
lsr x5, x13, #63
extr x2, x13, x16, #63
extr x24, x16, x8, #63
extr x1, x8, x11, #63
stp x25, x28, [x0, #352]
lsl x23, x12, #1
stp x14, x15, [x0, #368]
umulh x22, x17, x17
umulh x3, x20, x20
umulh x7, x4, x4
mul x13, x20, x20
mul x16, x4, x4
umulh x11, x6, x6
mul x8, x6, x6
mul x25, x17, x17
adds x28, x23, x22
adcs x12, x21, x13
adcs x15, x9, x3
adcs x14, x1, x16
adcs x20, x24, x7
adcs x4, x2, x8
adc x6, x5, x11
ldp x17, x23, [x0, #448]
ldp x22, x13, [x0, #464]
ldp x21, x3, [x0, #480]
ldp x9, x16, [x0, #496]
subs x1, x17, x21
sbcs x24, x23, x3
sbcs x7, x22, x9
sbcs x2, x13, x16
csel x8, x10, x27, hs
umulh x11, x27, x6
mul x5, x27, x6
mul x21, x27, x14
umulh x17, x27, x14
mul x3, x27, x20
umulh x23, x27, x20
mul x22, x27, x4
umulh x9, x27, x4
adds x13, x25, x21
adcs x16, x28, x3
adcs x6, x12, x22
adcs x14, x15, x5
adc x20, x11, x10
subs x4, x1, x8
sbcs x21, x24, x10
sbcs x25, x7, x10
sbc x28, x2, x10
adds x3, x14, x9
adc x12, x20, x10
umulh x22, x4, x21
umulh x5, x4, x25
umulh x15, x4, x28
mul x11, x4, x25
mul x8, x4, x28
mul x1, x21, x25
extr x24, x12, x3, #63
and x7, x3, #0x7fffffffffffffff
umulh x2, x21, x28
mul x14, x21, x28
mul x9, x24, x26
adds x20, x13, x9
adcs x12, x16, x17
adcs x3, x6, x23
adc x24, x7, x10
adds x13, x11, x22
adcs x9, x8, x5
adc x16, x15, x10
umulh x17, x21, x25
umulh x6, x25, x28
mul x23, x25, x28
mul x7, x4, x21
stp x20, x12, [x0, #384]
stp x3, x24, [x0, #400]
adds x11, x9, x1
adcs x22, x16, x14
adc x8, x2, x10
umulh x5, x4, x4
umulh x15, x21, x21
mul x20, x21, x21
umulh x12, x25, x25
mul x3, x25, x25
umulh x24, x28, x28
mul x9, x28, x28
mul x1, x4, x4
extr x16, x13, x7, #63
adds x14, x22, x17
adcs x2, x8, x23
adc x21, x6, x10
extr x25, x11, x13, #63
lsl x28, x7, #1
lsr x4, x21, #63
extr x17, x21, x2, #63
extr x22, x2, x14, #63
extr x8, x14, x11, #63
adds x23, x28, x5
adcs x6, x16, x20
adcs x13, x25, x15
adcs x7, x8, x3
adcs x21, x22, x12
adcs x2, x17, x9
adc x14, x4, x24
ldp x11, x28, [x0, #448]
ldp x5, x16, [x0, #464]
ldp x20, x25, [x0, #480]
ldp x15, x3, [x0, #496]
adds x8, x11, x20
adcs x12, x28, x25
adcs x22, x5, x15
adcs x9, x16, x3
csel x17, x27, x10, hs
umulh x24, x27, x14
mul x4, x27, x14
mul x11, x27, x7
umulh x20, x27, x7
mul x28, x27, x21
umulh x25, x27, x21
mul x5, x27, x2
umulh x15, x27, x2
adds x16, x1, x11
adcs x3, x23, x28
adcs x14, x6, x5
adcs x7, x13, x4
adc x21, x24, x10
adds x2, x8, x17
adcs x11, x12, x10
adc x1, x22, x10
umulh x23, x2, x11
umulh x28, x2, x1
umulh x5, x2, x9
adds x6, x7, x15
adc x4, x21, x10
mul x13, x2, x1
mul x24, x2, x9
umulh x8, x11, x9
mul x17, x11, x1
mul x12, x11, x9
extr x22, x4, x6, #63
and x15, x6, #0x7fffffffffffffff
mul x7, x22, x26
adds x21, x13, x23
adcs x4, x24, x28
adc x6, x5, x10
umulh x22, x11, x1
umulh x13, x1, x9
adds x23, x16, x7
adcs x24, x3, x20
adcs x28, x14, x25
adc x5, x15, x10
mul x16, x1, x9
adds x7, x4, x17
adcs x3, x6, x12
adc x20, x8, x10
mul x14, x2, x11
stp x23, x24, [x0, #192]
stp x28, x5, [x0, #208]
adds x25, x3, x22
adcs x15, x20, x16
adc x4, x13, x10
umulh x17, x2, x2
umulh x6, x11, x11
umulh x12, x1, x1
umulh x8, x9, x9
mul x23, x11, x11
mul x24, x1, x1
mul x28, x9, x9
mul x5, x2, x2
extr x3, x7, x21, #63
extr x22, x25, x7, #63
extr x20, x15, x25, #63
extr x16, x4, x15, #63
lsr x13, x4, #63
extr x11, x21, x14, #63
lsl x1, x14, #1
adds x9, x1, x17
adcs x2, x11, x23
adcs x7, x3, x6
adcs x25, x22, x24
adcs x15, x20, x12
adcs x4, x16, x28
adc x21, x13, x8
ldp x14, x1, [x0, #192]
ldp x17, x11, [x0, #208]
ldr x23, [x0, #64]
mul x3, x23, x1
mul x6, x23, x17
mul x22, x23, x11
umulh x24, x27, x21
mul x12, x27, x21
mul x20, x27, x25
umulh x28, x23, x14
umulh x16, x27, x25
mul x8, x27, x15
umulh x13, x27, x15
mul x21, x27, x4
umulh x25, x27, x4
adds x15, x5, x20
adcs x4, x9, x8
adcs x20, x2, x21
adcs x5, x7, x12
adc x9, x24, x10
umulh x8, x23, x1
umulh x21, x23, x17
adds x2, x5, x25
adc x7, x9, x10
umulh x12, x23, x11
mul x24, x23, x14
extr x25, x7, x2, #63
and x5, x2, #0x7fffffffffffffff
mul x9, x25, x26
adds x23, x3, x28
adcs x7, x6, x8
adcs x2, x22, x21
adc x25, x12, x10
ldr x28, [x0, #72]
adds x3, x15, x9
adcs x6, x4, x16
adcs x8, x20, x13
adc x22, x5, x10
mul x21, x28, x14
mul x12, x28, x1
mul x15, x28, x17
mul x9, x28, x11
umulh x4, x28, x14
stp x3, x6, [x0, #160]
umulh x16, x28, x1
umulh x13, x28, x17
umulh x20, x28, x11
stp x8, x22, [x0, #176]
ldr x5, [x0, #80]
adds x3, x23, x21
adcs x6, x7, x12
adcs x28, x2, x15
adcs x22, x25, x9
adc x8, x10, x10
ldr x21, [x0, #88]
mul x23, x5, x14
mul x12, x5, x1
mul x7, x5, x17
adds x2, x6, x4
adcs x15, x28, x16
adcs x25, x22, x13
adc x9, x8, x20
mul x6, x5, x11
umulh x4, x5, x14
umulh x28, x5, x1
umulh x16, x5, x17
umulh x22, x5, x11
adds x13, x2, x23
adcs x8, x15, x12
adcs x20, x25, x7
adcs x5, x9, x6
adc x2, x10, x10
mul x23, x21, x14
umulh x15, x21, x14
mul x12, x21, x1
umulh x25, x21, x1
mul x7, x21, x17
umulh x6, x21, x17
adds x9, x8, x4
adcs x14, x20, x28
adcs x1, x5, x16
adc x17, x2, x22
mul x8, x21, x11
umulh x4, x21, x11
adds x20, x9, x23
adcs x28, x14, x12
adcs x16, x1, x7
adcs x5, x17, x8
adc x22, x10, x10
ldp x2, x11, [x0, #352]
ldp x21, x9, [x0, #368]
ldp x23, x12, [x0, #384]
adds x14, x28, x15
adcs x7, x16, x25
adcs x1, x5, x6
adc x8, x22, x4
ldp x17, x15, [x0, #400]
umulh x28, x27, x8
mul x25, x27, x8
mul x16, x27, x14
umulh x6, x27, x14
subs x5, x2, x23
sbcs x4, x11, x12
sbcs x22, x21, x17
sbcs x8, x9, x15
csel x14, x10, x27, hs
mul x23, x27, x7
umulh x2, x27, x7
mul x12, x27, x1
umulh x11, x27, x1
adds x21, x24, x16
adcs x17, x3, x23
adcs x9, x13, x12
adcs x15, x20, x25
adc x7, x28, x10
subs x1, x5, x14
sbcs x16, x4, x10
sbcs x24, x22, x10
sbc x23, x8, x10
ldp x3, x13, [x0, #384]
ldr x12, [x0, #352]
ldp x25, x20, [x0, #400]
adds x28, x15, x11
adc x14, x7, x10
stp x24, x23, [x0, #432]
stp x1, x16, [x0, #416]
mul x5, x12, x13
mul x4, x12, x25
mul x22, x12, x20
extr x8, x14, x28, #63
umulh x15, x12, x3
mul x11, x12, x3
and x7, x28, #0x7fffffffffffffff
umulh x24, x12, x13
mul x23, x8, x26
umulh x1, x12, x25
adds x16, x21, x23
adcs x14, x17, x6
adcs x28, x9, x2
adc x8, x7, x10
umulh x21, x12, x20
adds x23, x5, x15
adcs x17, x4, x24
adcs x6, x22, x1
adc x9, x21, x10
stp x16, x14, [x0, #192]
stp x28, x8, [x0, #208]
ldr x2, [x0, #360]
ldr x7, [x0, #368]
mul x12, x2, x3
mul x15, x2, x13
mul x5, x2, x25
mul x24, x2, x20
umulh x4, x2, x3
umulh x1, x2, x13
umulh x22, x2, x25
umulh x21, x2, x20
mul x16, x7, x3
adds x14, x23, x12
adcs x28, x17, x15
adcs x8, x6, x5
adcs x2, x9, x24
adc x12, x10, x10
mul x23, x7, x13
mul x15, x7, x25
mul x17, x7, x20
adds x5, x28, x4
adcs x6, x8, x1
adcs x24, x2, x22
adc x9, x12, x21
umulh x4, x7, x3
umulh x28, x7, x13
umulh x1, x7, x25
umulh x8, x7, x20
ldr x2, [x0, #376]
adds x22, x5, x16
adcs x12, x6, x23
adcs x21, x24, x15
adcs x7, x9, x17
adc x16, x10, x10
mul x5, x2, x3
umulh x23, x2, x3
mul x6, x2, x13
umulh x24, x2, x13
mul x15, x2, x25
umulh x9, x2, x25
adds x17, x12, x4
adcs x3, x21, x28
adcs x13, x7, x1
adc x25, x16, x8
mul x12, x2, x20
umulh x4, x2, x20
adds x21, x17, x5
adcs x28, x3, x6
adcs x7, x13, x15
adcs x1, x25, x12
adc x16, x10, x10
ldp x8, x20, [x0, #416]
ldp x2, x17, [x0, #352]
ldp x5, x3, [x0, #368]
adds x6, x28, x23
adcs x13, x7, x24
adcs x15, x1, x9
adc x12, x16, x4
movz x25, #56129, lsl #0
ldp x28, x23, [x0, #432]
movk x25, #1, lsl #16
mul x7, x8, x25
umulh x24, x27, x12
mul x9, x27, x12
mul x1, x27, x6
umulh x4, x27, x6
mul x16, x27, x13
umulh x12, x27, x13
mul x6, x27, x15
umulh x13, x27, x15
adds x15, x11, x1
adcs x11, x14, x16
adcs x1, x22, x6
adcs x14, x21, x9
adc x16, x24, x10
umulh x6, x8, x25
umulh x22, x23, x25
mul x21, x23, x25
adds x9, x14, x13
adc x24, x16, x10
mul x8, x20, x25
umulh x23, x20, x25
extr x14, x24, x9, #63
and x13, x9, #0x7fffffffffffffff
mul x16, x14, x26
adds x20, x15, x16
adcs x24, x11, x4
adcs x9, x1, x12
adc x14, x13, x10
mul x15, x28, x25
umulh x16, x28, x25
adds x4, x2, x7
adcs x11, x17, x8
adcs x1, x5, x15
adcs x12, x3, x21
adc x13, x22, x10
stp x20, x24, [x0, #96]
stp x9, x14, [x0, #112]
ldr x28, [x0, #416]
ldr x25, [x0, #424]
adds x2, x12, x12
adc x7, x13, x13
mul x17, x7, x26
lsr x8, x2, #1
adds x15, x4, x17
adcs x5, x11, x6
adcs x21, x1, x23
adc x3, x8, x16
stp x15, x5, [x0, #128]
stp x21, x3, [x0, #144]
ldp x22, x20, [x0, #128]
ldp x24, x9, [x0, #144]
ldr x14, [x0, #432]
umulh x12, x28, x22
umulh x13, x28, x20
umulh x7, x28, x24
umulh x2, x28, x9
mul x4, x28, x20
mul x17, x28, x24
mul x6, x28, x9
mul x11, x25, x22
mul x23, x25, x20
mul x1, x25, x24
mul x16, x25, x9
umulh x8, x25, x22
mul x5, x28, x22
adds x15, x4, x12
adcs x21, x17, x13
adcs x3, x6, x7
adc x28, x2, x10
umulh x4, x25, x20
umulh x12, x25, x24
umulh x17, x25, x9
mul x13, x14, x22
adds x6, x15, x11
adcs x7, x21, x23
adcs x2, x3, x1
adcs x25, x28, x16
adc x15, x10, x10
mul x11, x14, x20
mul x21, x14, x24
mul x23, x14, x9
adds x3, x7, x8
adcs x1, x2, x4
adcs x16, x25, x12
adc x28, x15, x17
umulh x7, x14, x22
umulh x8, x14, x20
umulh x2, x14, x24
umulh x4, x14, x9
ldr x12, [x0, #440]
adds x25, x3, x13
adcs x17, x1, x11
adcs x15, x16, x21
adcs x14, x28, x23
adc x3, x10, x10
mul x13, x12, x22
umulh x11, x12, x22
mul x1, x12, x20
umulh x21, x12, x20
mul x16, x12, x24
umulh x23, x12, x24
adds x28, x17, x7
adcs x22, x15, x8
adcs x20, x14, x2
adc x24, x3, x4
mul x7, x12, x9
umulh x17, x12, x9
adds x8, x28, x13
adcs x15, x22, x1
adcs x2, x20, x16
adcs x14, x24, x7
adc x4, x10, x10
adds x3, x15, x11
adcs x12, x2, x21
adcs x9, x14, x23
adc x13, x4, x17
umulh x28, x27, x13
mul x1, x27, x3
mul x22, x27, x12
mul x16, x27, x9
mul x20, x27, x13
umulh x7, x27, x9
umulh x24, x27, x3
umulh x11, x27, x12
adds x15, x5, x1
adcs x21, x6, x22
adcs x2, x25, x16
adcs x14, x8, x20
adc x23, x28, x10
adds x4, x14, x7
adc x17, x23, x10
extr x13, x17, x4, #63
and x9, x4, #0x7fffffffffffffff
mul x3, x13, x26
adds x12, x15, x3
adcs x5, x21, x24
adcs x1, x2, x11
adc x6, x9, x10
stp x12, x5, [x0, #128]
stp x1, x6, [x0, #144]
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
.globl lab_sc_o1_19_30_1
lab_sc_o1_19_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
ldr x11, [x0, #336]
umulh x4, x3, x12
mul x8, x3, x24
umulh x2, x3, x24
mul x13, x3, x9
umulh x17, x3, x25
mul x14, x7, x9
umulh x1, x3, x9
mul x6, x3, x25
mul x20, x7, x25
mul x22, x7, x12
umulh x16, x7, x12
umulh x23, x7, x9
mul x15, x3, x12
adds x21, x13, x4
adcs x5, x6, x1
adcs x28, x8, x17
adc x3, x2, x10
mul x13, x7, x24
umulh x4, x7, x24
umulh x6, x7, x25
mul x1, x11, x12
adds x8, x21, x22
adcs x17, x5, x14
adcs x2, x28, x20
adcs x7, x3, x13
adc x22, x10, x10
mul x21, x11, x24
mul x5, x11, x9
mul x14, x11, x25
adds x28, x17, x16
adcs x20, x2, x23
adcs x3, x7, x6
adc x13, x22, x4
umulh x17, x11, x12
umulh x16, x11, x24
umulh x2, x11, x25
umulh x23, x11, x9
ldr x7, [x0, #344]
adds x6, x28, x1
adcs x4, x20, x5
adcs x22, x3, x14
adcs x11, x13, x21
adc x28, x10, x10
mul x1, x7, x12
umulh x20, x7, x12
mul x5, x7, x9
umulh x14, x7, x9
mul x3, x7, x24
umulh x21, x7, x24
adds x13, x4, x17
adcs x12, x22, x23
adcs x9, x11, x2
adc x24, x28, x16
mul x4, x7, x25
umulh x17, x7, x25
adds x23, x13, x1
adcs x22, x12, x5
adcs x2, x9, x4
adcs x11, x24, x3
adc x16, x10, x10
ldp x28, x25, [x0, #272]
ldr x7, [x0, #288]
ldp x1, x13, [x0, #256]
adds x5, x22, x20
adcs x12, x2, x14
adcs x4, x11, x17
adc x9, x16, x21
mul x3, x7, x25
mul x24, x7, x13
mul x20, x7, x28
mul x22, x7, x1
umulh x14, x27, x9
mul x2, x27, x9
mul x17, x27, x5
umulh x11, x27, x5
mul x16, x27, x12
umulh x21, x27, x12
mul x9, x27, x4
umulh x5, x27, x4
adds x12, x15, x17
adcs x4, x8, x16
adcs x17, x6, x9
adcs x15, x23, x2
adc x8, x14, x10
umulh x16, x7, x1
umulh x6, x7, x28
adds x9, x15, x5
adc x2, x8, x10
umulh x23, x7, x25
umulh x14, x7, x13
extr x15, x2, x9, #63
and x5, x9, #0x7fffffffffffffff
mul x8, x15, x26
adds x7, x24, x16
adcs x2, x20, x14
adcs x9, x3, x6
adc x15, x23, x10
ldr x16, [x0, #296]
adds x24, x12, x8
adcs x14, x4, x11
adcs x20, x17, x21
adc x6, x5, x10
mul x3, x16, x1
mul x23, x16, x13
mul x12, x16, x28
mul x8, x16, x25
umulh x4, x16, x25
stp x20, x6, [x0, #464]
umulh x11, x16, x28
umulh x17, x16, x1
umulh x21, x16, x13
stp x24, x14, [x0, #448]
ldr x5, [x0, #304]
adds x20, x7, x3
adcs x6, x2, x23
adcs x16, x9, x12
adcs x24, x15, x8
adc x14, x10, x10
ldr x3, [x0, #312]
mul x7, x5, x1
mul x23, x5, x28
mul x2, x5, x25
adds x12, x6, x17
adcs x9, x16, x21
adcs x8, x24, x11
adc x15, x14, x4
mul x17, x5, x13
umulh x6, x5, x28
umulh x21, x5, x25
umulh x16, x5, x1
umulh x24, x5, x13
adds x11, x12, x7
adcs x14, x9, x17
adcs x4, x8, x23
adcs x5, x15, x2
adc x7, x10, x10
mul x12, x3, x25
umulh x17, x3, x25
mul x9, x3, x1
umulh x8, x3, x1
umulh x23, x3, x13
mul x15, x3, x13
adds x2, x14, x16
adcs x25, x4, x24
adcs x1, x5, x6
adc x13, x7, x21
mul x14, x3, x28
umulh x16, x3, x28
adds x4, x2, x9
adcs x24, x25, x15
adcs x5, x1, x14
adcs x6, x13, x12
adc x7, x10, x10
ldp x21, x28, [x0, #224]
ldp x3, x2, [x0, #240]
adds x9, x24, x8
adcs x25, x5, x23
adcs x15, x6, x16
adc x1, x7, x17
mul x14, x21, x3
mul x12, x21, x2
umulh x13, x21, x28
umulh x24, x21, x3
mul x8, x21, x28
umulh x5, x27, x1
mul x23, x27, x1
mul x16, x27, x15
umulh x6, x27, x15
mul x17, x27, x9
umulh x7, x27, x9
mul x1, x27, x25
umulh x15, x27, x25
adds x9, x22, x17
adcs x25, x20, x1
adcs x22, x11, x16
adcs x17, x4, x23
adc x20, x5, x10
umulh x1, x21, x2
umulh x16, x28, x2
adds x11, x14, x13
adcs x4, x12, x24
adc x23, x1, x10
adds x5, x17, x6
adc x14, x20, x10
mul x13, x28, x2
mul x12, x28, x3
umulh x24, x28, x3
extr x1, x14, x5, #63
and x17, x5, #0x7fffffffffffffff
adds x6, x4, x12
adcs x20, x23, x13
adc x14, x16, x10
mul x5, x1, x26
umulh x4, x3, x2
mul x12, x3, x2
adds x23, x9, x5
adcs x13, x25, x7
adcs x16, x22, x15
adc x1, x17, x10
extr x9, x6, x11, #63
adds x5, x20, x24
adcs x7, x14, x12
adc x25, x4, x10
extr x22, x11, x8, #63
stp x23, x13, [x0, #480]
extr x15, x7, x5, #63
extr x17, x5, x6, #63
lsr x20, x25, #63
extr x24, x25, x7, #63
lsl x14, x8, #1
stp x16, x1, [x0, #496]
umulh x12, x2, x2
umulh x4, x28, x28
mul x11, x2, x2
mul x23, x28, x28
mul x13, x3, x3
umulh x5, x3, x3
umulh x6, x21, x21
mul x7, x21, x21
adds x25, x14, x6
adcs x8, x22, x23
adcs x16, x9, x4
adcs x1, x17, x13
adcs x2, x15, x5
adcs x28, x24, x11
adc x3, x20, x12
ldp x21, x14, [x0, #272]
ldp x6, x22, [x0, #256]
umulh x23, x6, x22
umulh x9, x6, x21
mul x4, x6, x21
mul x17, x6, x14
mul x13, x6, x22
mul x5, x27, x1
umulh x15, x6, x14
umulh x11, x27, x1
mul x24, x27, x2
umulh x12, x27, x2
mul x20, x27, x28
umulh x1, x27, x28
mul x2, x27, x3
umulh x28, x27, x3
adds x3, x7, x5
adcs x5, x25, x24
adcs x7, x8, x20
adcs x25, x16, x2
adc x24, x28, x10
adds x20, x4, x23
adcs x8, x17, x9
adc x2, x15, x10
mul x16, x22, x14
umulh x28, x22, x14
mul x23, x21, x14
adds x4, x25, x1
adc x9, x24, x10
umulh x17, x22, x21
extr x15, x9, x4, #63
and x1, x4, #0x7fffffffffffffff
mul x25, x15, x26
adds x24, x3, x25
adcs x9, x5, x11
adcs x4, x7, x12
adc x15, x1, x10
mul x3, x22, x21
umulh x25, x21, x14
extr x5, x20, x13, #63
adds x11, x8, x3
adcs x12, x2, x16
adc x7, x28, x10
stp x24, x9, [x0, #352]
lsl x1, x13, #1
stp x4, x15, [x0, #368]
umulh x8, x22, x22
mul x3, x22, x22
umulh x2, x6, x6
mul x16, x21, x21
umulh x28, x21, x21
extr x24, x11, x20, #63
adds x9, x12, x17
adcs x13, x7, x23
adc x15, x25, x10
mul x4, x14, x14
umulh x22, x14, x14
mul x21, x6, x6
lsr x20, x15, #63
extr x17, x9, x11, #63
extr x12, x13, x9, #63
extr x7, x15, x13, #63
adds x23, x1, x2
adcs x25, x5, x3
adcs x14, x24, x8
adcs x6, x17, x16
adcs x11, x12, x28
adcs x9, x7, x4
adc x13, x20, x22
ldp x15, x1, [x0, #480]
ldp x2, x3, [x0, #464]
ldp x5, x8, [x0, #448]
ldp x24, x16, [x0, #496]
subs x17, x5, x15
sbcs x12, x8, x1
sbcs x28, x2, x24
sbcs x7, x3, x16
csel x4, x10, x27, hs
mul x22, x27, x11
mul x20, x27, x13
umulh x15, x27, x13
mul x5, x27, x9
umulh x1, x27, x9
umulh x8, x27, x11
mul x2, x27, x6
umulh x24, x27, x6
adds x3, x21, x2
adcs x16, x23, x22
adcs x13, x25, x5
adcs x9, x14, x20
adc x11, x15, x10
subs x6, x17, x4
sbcs x2, x12, x10
sbcs x21, x28, x10
sbc x23, x7, x10
adds x22, x9, x1
adc x25, x11, x10
umulh x5, x6, x21
mul x20, x6, x21
umulh x14, x6, x23
umulh x15, x6, x2
mul x4, x6, x23
mul x17, x2, x23
extr x12, x25, x22, #63
and x28, x22, #0x7fffffffffffffff
umulh x7, x2, x23
mul x9, x2, x21
mul x1, x12, x26
adds x11, x3, x1
adcs x25, x16, x24
adcs x22, x13, x8
adc x12, x28, x10
adds x3, x20, x15
adcs x1, x4, x5
adc x16, x14, x10
umulh x24, x21, x23
umulh x13, x2, x21
mul x8, x21, x23
mul x28, x6, x2
stp x11, x25, [x0, #384]
stp x22, x12, [x0, #400]
adds x20, x1, x9
adcs x15, x16, x17
adc x4, x7, x10
umulh x5, x23, x23
mul x14, x23, x23
mul x11, x2, x2
umulh x25, x2, x2
umulh x22, x6, x6
mul x12, x6, x6
mul x1, x21, x21
umulh x9, x21, x21
extr x16, x3, x28, #63
adds x17, x15, x13
adcs x7, x4, x8
adc x23, x24, x10
extr x2, x20, x3, #63
lsl x6, x28, #1
lsr x21, x23, #63
extr x13, x23, x7, #63
extr x15, x7, x17, #63
extr x4, x17, x20, #63
adds x8, x6, x22
adcs x24, x16, x11
adcs x3, x2, x25
adcs x28, x4, x1
adcs x23, x15, x9
adcs x7, x13, x14
adc x17, x21, x5
ldp x20, x6, [x0, #464]
ldp x22, x16, [x0, #448]
ldp x11, x2, [x0, #480]
ldp x25, x1, [x0, #496]
adds x4, x22, x11
adcs x9, x16, x2
adcs x15, x20, x25
adcs x14, x6, x1
csel x13, x27, x10, hs
mul x5, x27, x17
umulh x21, x27, x17
mul x22, x27, x7
umulh x11, x27, x7
mul x16, x27, x23
umulh x2, x27, x23
mul x20, x27, x28
umulh x25, x27, x28
adds x6, x12, x20
adcs x1, x8, x16
adcs x17, x24, x22
adcs x7, x3, x5
adc x23, x21, x10
adds x28, x4, x13
adcs x20, x9, x10
adc x12, x15, x10
umulh x8, x28, x20
mul x16, x28, x12
umulh x22, x28, x14
adds x24, x7, x11
adc x5, x23, x10
umulh x3, x28, x12
mul x21, x28, x14
mul x4, x20, x12
umulh x13, x20, x14
mul x9, x20, x14
extr x15, x5, x24, #63
and x11, x24, #0x7fffffffffffffff
mul x7, x15, x26
adds x23, x16, x8
adcs x5, x21, x3
adc x24, x22, x10
umulh x15, x12, x14
mul x16, x28, x20
adds x8, x6, x7
adcs x21, x1, x25
adcs x3, x17, x2
adc x22, x11, x10
umulh x6, x20, x12
mul x7, x12, x14
adds x1, x5, x4
adcs x25, x24, x9
adc x17, x13, x10
stp x8, x21, [x0, #192]
stp x3, x22, [x0, #208]
umulh x2, x28, x28
mul x11, x12, x12
umulh x5, x12, x12
adds x4, x25, x6
adcs x24, x17, x7
adc x9, x15, x10
umulh x13, x20, x20
lsl x8, x16, #1
extr x21, x23, x16, #63
mul x3, x20, x20
extr x22, x1, x23, #63
mul x12, x14, x14
umulh x25, x14, x14
mul x6, x28, x28
lsr x17, x9, #63
extr x7, x4, x1, #63
extr x15, x9, x24, #63
extr x16, x24, x4, #63
adds x20, x8, x2
adcs x23, x21, x3
adcs x14, x22, x13
adcs x28, x7, x11
adcs x1, x16, x5
adcs x9, x15, x12
adc x4, x17, x25
ldp x24, x8, [x0, #192]
ldp x2, x21, [x0, #208]
ldr x3, [x0, #64]
mul x22, x3, x8
mul x13, x3, x2
mul x7, x3, x21
umulh x11, x27, x4
mul x5, x27, x4
mul x16, x27, x28
umulh x12, x3, x24
umulh x15, x27, x28
mul x25, x27, x1
umulh x17, x27, x1
mul x4, x27, x9
umulh x28, x27, x9
adds x1, x6, x16
adcs x9, x20, x25
adcs x16, x23, x4
adcs x6, x14, x5
adc x20, x11, x10
umulh x25, x3, x8
umulh x4, x3, x2
adds x23, x6, x28
adc x14, x20, x10
umulh x5, x3, x21
mul x11, x3, x24
extr x28, x14, x23, #63
and x6, x23, #0x7fffffffffffffff
mul x20, x28, x26
adds x3, x22, x12
adcs x14, x13, x25
adcs x23, x7, x4
adc x28, x5, x10
ldr x12, [x0, #72]
adds x22, x1, x20
adcs x13, x9, x15
adcs x25, x16, x17
adc x7, x6, x10
mul x4, x12, x24
mul x5, x12, x8
mul x1, x12, x21
mul x20, x12, x2
umulh x9, x12, x24
stp x22, x13, [x0, #160]
umulh x15, x12, x21
umulh x17, x12, x8
umulh x16, x12, x2
stp x25, x7, [x0, #176]
ldr x6, [x0, #80]
adds x22, x3, x4
adcs x13, x14, x5
adcs x12, x23, x20
adcs x7, x28, x1
adc x25, x10, x10
ldr x4, [x0, #88]
mul x3, x6, x24
mul x5, x6, x8
mul x14, x6, x2
adds x23, x13, x9
adcs x20, x12, x17
adcs x28, x7, x16
adc x1, x25, x15
umulh x13, x6, x21
umulh x9, x6, x8
mul x12, x6, x21
umulh x17, x6, x24
umulh x7, x6, x2
adds x16, x23, x3
adcs x25, x20, x5
adcs x15, x28, x14
adcs x6, x1, x12
adc x23, x10, x10
mul x3, x4, x24
umulh x20, x4, x24
mul x5, x4, x8
umulh x28, x4, x8
mul x14, x4, x21
umulh x12, x4, x21
adds x1, x25, x17
adcs x24, x15, x9
adcs x8, x6, x7
adc x21, x23, x13
mul x25, x4, x2
umulh x17, x4, x2
adds x15, x1, x3
adcs x9, x24, x5
adcs x7, x8, x25
adcs x6, x21, x14
adc x13, x10, x10
ldp x23, x2, [x0, #352]
ldp x4, x1, [x0, #384]
ldp x3, x5, [x0, #368]
adds x24, x9, x20
adcs x25, x7, x28
adcs x8, x6, x17
adc x14, x13, x12
ldp x21, x20, [x0, #400]
umulh x9, x27, x14
mul x28, x27, x14
mul x7, x27, x8
umulh x17, x27, x8
subs x6, x23, x4
sbcs x12, x2, x1
sbcs x13, x3, x21
sbcs x14, x5, x20
csel x8, x10, x27, hs
mul x4, x27, x25
umulh x23, x27, x25
mul x1, x27, x24
umulh x2, x27, x24
adds x3, x11, x1
adcs x21, x22, x4
adcs x5, x16, x7
adcs x20, x15, x28
adc x25, x9, x10
subs x24, x6, x8
sbcs x1, x12, x10
sbcs x11, x13, x10
sbc x4, x14, x10
ldp x22, x16, [x0, #384]
ldr x7, [x0, #352]
ldp x28, x15, [x0, #400]
adds x9, x20, x17
adc x8, x25, x10
stp x11, x4, [x0, #432]
stp x24, x1, [x0, #416]
mul x6, x7, x16
mul x12, x7, x15
mul x13, x7, x28
extr x14, x8, x9, #63
umulh x20, x7, x22
and x17, x9, #0x7fffffffffffffff
umulh x25, x7, x16
mul x11, x14, x26
umulh x4, x7, x28
mul x24, x7, x22
adds x1, x3, x11
adcs x8, x21, x2
adcs x9, x5, x23
adc x14, x17, x10
umulh x3, x7, x15
adds x11, x6, x20
adcs x21, x13, x25
adcs x2, x12, x4
adc x5, x3, x10
stp x9, x14, [x0, #208]
stp x1, x8, [x0, #192]
ldr x23, [x0, #360]
ldr x17, [x0, #368]
mul x7, x23, x22
mul x20, x23, x16
mul x6, x23, x15
mul x25, x23, x28
umulh x13, x23, x16
umulh x4, x23, x22
umulh x12, x23, x15
umulh x3, x23, x28
mul x9, x17, x15
adds x14, x11, x7
adcs x1, x21, x20
adcs x8, x2, x25
adcs x23, x5, x6
adc x7, x10, x10
mul x11, x17, x28
mul x20, x17, x22
mul x21, x17, x16
adds x25, x1, x4
adcs x2, x8, x13
adcs x6, x23, x3
adc x5, x7, x12
ldr x4, [x0, #376]
umulh x1, x17, x22
umulh x13, x17, x16
umulh x8, x17, x15
umulh x23, x17, x28
adds x3, x25, x20
adcs x7, x2, x21
adcs x12, x6, x11
adcs x17, x5, x9
adc x20, x10, x10
mul x25, x4, x28
umulh x21, x4, x28
umulh x2, x4, x16
mul x6, x4, x16
umulh x11, x4, x22
mul x5, x4, x22
adds x9, x7, x1
adcs x28, x12, x13
adcs x16, x17, x23
adc x22, x20, x8
mul x7, x4, x15
umulh x1, x4, x15
adds x12, x9, x5
adcs x13, x28, x6
adcs x17, x16, x25
adcs x23, x22, x7
adc x20, x10, x10
ldp x8, x15, [x0, #416]
ldp x4, x9, [x0, #368]
ldp x5, x28, [x0, #352]
adds x6, x13, x11
adcs x16, x17, x2
adcs x25, x23, x21
adc x7, x20, x1
movz x22, #56129, lsl #0
ldp x13, x11, [x0, #432]
movk x22, #1, lsl #16
mul x17, x8, x22
umulh x2, x27, x7
mul x21, x27, x7
mul x23, x27, x6
umulh x1, x27, x6
mul x20, x27, x16
umulh x7, x27, x16
mul x6, x27, x25
umulh x16, x27, x25
adds x25, x24, x23
adcs x24, x14, x20
adcs x23, x3, x6
adcs x14, x12, x21
adc x20, x2, x10
umulh x6, x8, x22
umulh x3, x11, x22
mul x12, x11, x22
adds x21, x14, x16
adc x2, x20, x10
mul x8, x13, x22
umulh x11, x13, x22
extr x14, x2, x21, #63
and x16, x21, #0x7fffffffffffffff
mul x20, x14, x26
adds x13, x25, x20
adcs x2, x24, x1
adcs x21, x23, x7
adc x14, x16, x10
mul x25, x15, x22
umulh x20, x15, x22
adds x1, x5, x17
adcs x24, x28, x25
adcs x23, x4, x8
adcs x7, x9, x12
adc x16, x3, x10
stp x21, x14, [x0, #112]
stp x13, x2, [x0, #96]
ldr x15, [x0, #416]
ldr x22, [x0, #424]
adds x5, x7, x7
adc x17, x16, x16
mul x28, x17, x26
lsr x25, x5, #1
adds x8, x1, x28
adcs x4, x24, x6
adcs x12, x23, x20
adc x9, x25, x11
stp x8, x4, [x0, #128]
stp x12, x9, [x0, #144]
ldp x3, x21, [x0, #128]
ldp x14, x13, [x0, #144]
ldr x2, [x0, #432]
umulh x7, x15, x3
umulh x16, x15, x14
mul x17, x15, x13
umulh x5, x15, x21
mul x1, x15, x14
umulh x28, x15, x13
mul x6, x22, x21
mul x24, x15, x21
mul x20, x22, x3
mul x23, x22, x14
mul x11, x22, x13
umulh x25, x22, x3
mul x4, x15, x3
adds x8, x24, x7
adcs x12, x1, x5
adcs x9, x17, x16
adc x15, x28, x10
umulh x24, x22, x13
umulh x7, x22, x21
umulh x1, x22, x14
mul x5, x2, x13
adds x17, x8, x20
adcs x16, x12, x6
adcs x28, x9, x23
adcs x22, x15, x11
adc x8, x10, x10
mul x20, x2, x3
mul x12, x2, x14
mul x6, x2, x21
adds x9, x16, x25
adcs x23, x28, x7
adcs x11, x22, x1
adc x15, x8, x24
umulh x16, x2, x21
umulh x25, x2, x13
umulh x28, x2, x14
umulh x7, x2, x3
ldr x1, [x0, #440]
adds x22, x9, x20
adcs x24, x23, x6
adcs x8, x11, x12
adcs x2, x15, x5
adc x9, x10, x10
mul x20, x1, x3
umulh x6, x1, x3
mul x23, x1, x14
umulh x12, x1, x14
mul x11, x1, x13
umulh x5, x1, x13
adds x15, x24, x7
adcs x3, x8, x16
adcs x14, x2, x28
adc x13, x9, x25
mul x7, x1, x21
umulh x24, x1, x21
adds x16, x15, x20
adcs x8, x3, x7
adcs x28, x14, x23
adcs x2, x13, x11
adc x25, x10, x10
adds x9, x8, x6
adcs x1, x28, x24
adcs x21, x2, x12
adc x20, x25, x5
umulh x15, x27, x20
mul x7, x27, x1
mul x3, x27, x9
mul x23, x27, x21
mul x14, x27, x20
umulh x11, x27, x21
umulh x13, x27, x9
umulh x6, x27, x1
adds x8, x4, x3
adcs x24, x17, x7
adcs x28, x22, x23
adcs x2, x16, x14
adc x12, x15, x10
adds x25, x2, x11
adc x5, x12, x10
extr x20, x5, x25, #63
and x21, x25, #0x7fffffffffffffff
mul x9, x20, x26
adds x1, x8, x9
adcs x4, x24, x13
adcs x3, x28, x6
adc x17, x21, x10
stp x1, x4, [x0, #128]
stp x3, x17, [x0, #144]
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
.globl lab_sc_o1_19_15_0
lab_sc_o1_19_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
ldr x17, [x0, #320]
ldr x1, [x0, #328]
umulh x12, x17, x9
umulh x14, x17, x7
umulh x20, x17, x16
umulh x13, x17, x21
mul x4, x17, x7
mul x22, x17, x16
mul x6, x17, x21
mul x2, x1, x9
mul x11, x1, x7
mul x15, x1, x16
mul x8, x17, x9
mul x28, x1, x21
umulh x23, x1, x9
umulh x25, x1, x7
adds x24, x4, x12
adcs x3, x22, x14
adcs x5, x6, x20
adc x17, x13, x10
umulh x4, x1, x16
umulh x12, x1, x21
ldr x22, [x0, #336]
adds x14, x24, x2
adcs x6, x3, x11
adcs x20, x5, x15
adcs x13, x17, x28
adc x1, x10, x10
mul x2, x22, x9
mul x24, x22, x7
mul x3, x22, x16
mul x11, x22, x21
adds x5, x6, x23
adcs x15, x20, x25
adcs x17, x13, x4
adc x28, x1, x12
umulh x6, x22, x9
umulh x23, x22, x7
umulh x20, x22, x16
umulh x25, x22, x21
ldr x13, [x0, #344]
adds x4, x5, x2
adcs x12, x15, x24
adcs x1, x17, x3
adcs x22, x28, x11
adc x5, x10, x10
mul x2, x13, x9
umulh x15, x13, x9
mul x24, x13, x7
umulh x3, x13, x7
mul x17, x13, x16
adds x11, x12, x6
adcs x28, x1, x23
adcs x9, x22, x20
adc x7, x5, x25
umulh x12, x13, x16
mul x6, x13, x21
umulh x23, x13, x21
adds x1, x11, x2
adcs x20, x28, x24
adcs x22, x9, x17
adcs x25, x7, x6
adc x5, x10, x10
adds x16, x20, x15
adcs x21, x22, x3
adcs x13, x25, x12
adc x2, x5, x23
umulh x11, x27, x2
mul x24, x27, x16
mul x28, x27, x21
mul x17, x27, x13
mul x9, x27, x2
umulh x6, x27, x13
umulh x7, x27, x16
umulh x15, x27, x21
adds x20, x8, x24
adcs x3, x14, x28
adcs x22, x4, x17
adcs x12, x1, x9
adc x25, x11, x10
ldp x5, x23, [x0, #256]
ldp x2, x13, [x0, #272]
ldr x16, [x0, #288]
adds x21, x12, x6
adc x24, x25, x10
mul x8, x16, x23
mul x14, x16, x2
mul x28, x16, x13
mul x4, x16, x5
extr x17, x24, x21, #63
umulh x9, x16, x5
and x1, x21, #0x7fffffffffffffff
umulh x11, x16, x23
mul x12, x17, x26
umulh x6, x16, x2
adds x25, x20, x12
adcs x24, x3, x7
adcs x21, x22, x15
adc x17, x1, x10
umulh x20, x16, x13
adds x12, x8, x9
adcs x3, x14, x11
adcs x7, x28, x6
adc x22, x20, x10
stp x25, x24, [x0, #448]
stp x21, x17, [x0, #464]
ldr x15, [x0, #296]
mul x1, x15, x5
mul x16, x15, x23
mul x9, x15, x2
mul x8, x15, x13
umulh x11, x15, x5
umulh x14, x15, x23
umulh x6, x15, x2
umulh x28, x15, x13
ldr x20, [x0, #304]
adds x25, x12, x1
adcs x24, x3, x16
adcs x21, x7, x9
adcs x17, x22, x8
adc x15, x10, x10
mul x1, x20, x5
mul x12, x20, x23
mul x16, x20, x2
mul x3, x20, x13
adds x9, x24, x11
adcs x7, x21, x14
adcs x8, x17, x6
adc x22, x15, x28
umulh x11, x20, x5
umulh x24, x20, x23
umulh x14, x20, x2
umulh x21, x20, x13
ldr x17, [x0, #312]
adds x6, x9, x1
adcs x15, x7, x12
adcs x28, x8, x16
adcs x20, x22, x3
adc x1, x10, x10
mul x9, x17, x5
umulh x12, x17, x5
mul x7, x17, x23
umulh x8, x17, x23
mul x16, x17, x2
adds x22, x15, x11
adcs x3, x28, x24
adcs x5, x20, x14
adc x23, x1, x21
umulh x15, x17, x2
mul x11, x17, x13
umulh x28, x17, x13
adds x24, x22, x9
adcs x20, x3, x7
adcs x14, x5, x16
adcs x1, x23, x11
adc x21, x10, x10
adds x2, x20, x12
adcs x13, x14, x8
adcs x17, x1, x15
adc x22, x21, x28
umulh x9, x27, x22
mul x3, x27, x2
mul x7, x27, x13
mul x5, x27, x17
mul x16, x27, x22
umulh x11, x27, x17
umulh x23, x27, x2
umulh x20, x27, x13
adds x12, x4, x3
adcs x14, x25, x7
adcs x8, x6, x5
adcs x15, x24, x16
adc x1, x9, x10
ldp x28, x21, [x0, #224]
ldp x22, x17, [x0, #240]
adds x2, x15, x11
adc x13, x1, x10
umulh x4, x28, x21
umulh x3, x28, x22
mul x25, x28, x22
mul x7, x28, x17
mul x5, x28, x21
extr x6, x13, x2, #63
umulh x24, x28, x17
and x16, x2, #0x7fffffffffffffff
mul x9, x21, x22
mul x15, x6, x26
mul x11, x21, x17
adds x1, x12, x15
adcs x13, x14, x23
adcs x2, x8, x20
adc x6, x16, x10
umulh x12, x21, x17
umulh x15, x21, x22
umulh x23, x22, x17
stp x1, x13, [x0, #480]
adds x14, x25, x4
adcs x8, x7, x3
adc x20, x24, x10
mul x16, x22, x17
stp x2, x6, [x0, #496]
umulh x1, x28, x28
mul x13, x28, x28
mul x25, x21, x21
lsl x4, x5, #1
adds x7, x8, x9
adcs x3, x20, x11
adc x24, x12, x10
umulh x2, x21, x21
extr x6, x14, x5, #63
umulh x28, x22, x22
mul x8, x22, x22
adds x9, x3, x15
adcs x20, x24, x16
adc x11, x23, x10
extr x12, x7, x14, #63
umulh x21, x17, x17
mul x5, x17, x17
lsr x22, x11, #63
extr x3, x11, x20, #63
extr x15, x20, x9, #63
extr x24, x9, x7, #63
adds x16, x4, x1
adcs x23, x6, x25
adcs x14, x12, x2
adcs x17, x24, x8
adcs x11, x15, x28
adcs x20, x3, x5
adc x9, x22, x21
umulh x7, x27, x9
mul x4, x27, x17
mul x1, x27, x11
mul x6, x27, x20
mul x25, x27, x9
umulh x12, x27, x20
umulh x2, x27, x17
umulh x24, x27, x11
adds x8, x13, x4
adcs x28, x16, x1
adcs x15, x23, x6
adcs x5, x14, x25
adc x3, x7, x10
ldp x21, x22, [x0, #256]
ldp x9, x20, [x0, #272]
adds x17, x5, x12
adc x11, x3, x10
umulh x4, x21, x22
umulh x13, x21, x9
mul x16, x21, x9
mul x1, x21, x20
mul x6, x21, x22
extr x23, x11, x17, #63
umulh x25, x21, x20
and x14, x17, #0x7fffffffffffffff
mul x7, x22, x9
mul x12, x23, x26
mul x5, x22, x20
adds x3, x8, x12
adcs x11, x28, x2
adcs x17, x15, x24
adc x23, x14, x10
umulh x8, x22, x20
umulh x12, x22, x9
umulh x28, x9, x20
stp x3, x11, [x0, #352]
adds x2, x16, x4
adcs x24, x1, x13
adc x15, x25, x10
mul x14, x9, x20
stp x17, x23, [x0, #368]
umulh x3, x21, x21
mul x11, x21, x21
mul x4, x22, x22
lsl x16, x6, #1
adds x13, x24, x7
adcs x1, x15, x5
adc x25, x8, x10
umulh x23, x22, x22
extr x17, x2, x6, #63
umulh x21, x9, x9
mul x24, x9, x9
adds x7, x1, x12
adcs x15, x25, x14
adc x5, x28, x10
extr x8, x13, x2, #63
umulh x22, x20, x20
mul x6, x20, x20
lsr x9, x5, #63
extr x12, x5, x15, #63
extr x1, x15, x7, #63
extr x25, x7, x13, #63
adds x14, x16, x3
adcs x28, x17, x4
adcs x2, x8, x23
adcs x20, x25, x24
adcs x5, x1, x21
adcs x15, x12, x6
adc x13, x9, x22
umulh x7, x27, x13
mul x16, x27, x20
mul x3, x27, x5
mul x4, x27, x15
mul x17, x27, x13
umulh x23, x27, x15
umulh x8, x27, x20
umulh x24, x27, x5
adds x25, x11, x16
adcs x1, x14, x3
adcs x21, x28, x4
adcs x12, x2, x17
adc x6, x7, x10
ldp x22, x9, [x0, #448]
ldp x13, x15, [x0, #464]
ldp x20, x5, [x0, #480]
ldp x16, x11, [x0, #496]
adds x14, x12, x23
adc x3, x6, x10
subs x28, x22, x20
sbcs x4, x9, x5
sbcs x17, x13, x16
sbcs x2, x15, x11
csel x7, x10, x27, hs
extr x12, x3, x14, #63
and x23, x14, #0x7fffffffffffffff
mul x6, x12, x26
adds x20, x25, x6
adcs x22, x1, x8
adcs x5, x21, x24
adc x9, x23, x10
subs x13, x28, x7
sbcs x16, x4, x10
sbcs x15, x17, x10
sbc x11, x2, x10
stp x20, x22, [x0, #384]
stp x5, x9, [x0, #400]
umulh x3, x13, x16
umulh x14, x13, x15
umulh x12, x13, x11
mul x25, x13, x15
mul x6, x13, x11
umulh x1, x16, x11
mul x8, x16, x15
mul x21, x16, x11
umulh x24, x16, x15
umulh x23, x15, x11
mul x7, x15, x11
mul x28, x13, x16
adds x4, x25, x3
adcs x17, x6, x14
adc x2, x12, x10
umulh x20, x13, x13
mul x22, x13, x13
mul x5, x16, x16
lsl x9, x28, #1
adds x25, x17, x8
adcs x3, x2, x21
adc x6, x1, x10
umulh x14, x16, x16
extr x12, x4, x28, #63
umulh x13, x15, x15
mul x17, x15, x15
adds x8, x3, x24
adcs x2, x6, x7
adc x21, x23, x10
extr x1, x25, x4, #63
umulh x16, x11, x11
mul x28, x11, x11
lsr x15, x21, #63
extr x24, x21, x2, #63
extr x3, x2, x8, #63
extr x6, x8, x25, #63
adds x7, x9, x20
adcs x23, x12, x5
adcs x4, x1, x14
adcs x11, x6, x17
adcs x21, x3, x13
adcs x2, x24, x28
adc x8, x15, x16
umulh x25, x27, x8
mul x9, x27, x11
mul x20, x27, x21
mul x12, x27, x2
mul x5, x27, x8
umulh x1, x27, x2
umulh x14, x27, x11
umulh x17, x27, x21
adds x6, x22, x9
adcs x13, x7, x20
adcs x3, x23, x12
adcs x28, x4, x5
adc x24, x25, x10
ldp x16, x15, [x0, #448]
ldp x8, x2, [x0, #464]
ldp x11, x21, [x0, #480]
ldp x9, x22, [x0, #496]
adds x7, x28, x1
adc x20, x24, x10
adds x12, x16, x11
adcs x23, x15, x21
adcs x5, x8, x9
adcs x4, x2, x22
csel x25, x27, x10, hs
extr x1, x20, x7, #63
and x28, x7, #0x7fffffffffffffff
mul x24, x1, x26
adds x16, x6, x24
adcs x11, x13, x14
adcs x15, x3, x17
adc x21, x28, x10
adds x8, x12, x25
adcs x9, x23, x10
adc x2, x5, x10
stp x16, x11, [x0, #192]
stp x15, x21, [x0, #208]
umulh x22, x8, x9
umulh x20, x8, x2
umulh x7, x8, x4
mul x1, x8, x2
mul x6, x8, x4
umulh x24, x9, x4
mul x13, x9, x2
mul x14, x9, x4
umulh x3, x9, x2
umulh x17, x2, x4
mul x28, x2, x4
mul x12, x8, x9
adds x25, x1, x22
adcs x23, x6, x20
adc x5, x7, x10
umulh x16, x8, x8
mul x11, x8, x8
mul x15, x9, x9
lsl x21, x12, #1
adds x1, x23, x13
adcs x22, x5, x14
adc x6, x24, x10
umulh x20, x9, x9
extr x7, x25, x12, #63
umulh x8, x2, x2
mul x23, x2, x2
adds x13, x22, x3
adcs x5, x6, x28
adc x14, x17, x10
extr x24, x1, x25, #63
umulh x9, x4, x4
mul x12, x4, x4
lsr x2, x14, #63
extr x22, x14, x5, #63
extr x3, x5, x13, #63
extr x6, x13, x1, #63
adds x28, x21, x16
adcs x17, x7, x15
adcs x25, x24, x20
adcs x4, x6, x23
adcs x14, x3, x8
adcs x5, x22, x12
adc x13, x2, x9
umulh x1, x27, x13
mul x21, x27, x4
mul x16, x27, x14
mul x7, x27, x5
mul x15, x27, x13
umulh x24, x27, x5
umulh x20, x27, x4
umulh x6, x27, x14
adds x23, x11, x21
adcs x8, x28, x16
adcs x3, x17, x7
adcs x12, x25, x15
adc x22, x1, x10
ldp x9, x2, [x0, #192]
ldp x13, x5, [x0, #208]
ldr x4, [x0, #64]
adds x14, x12, x24
adc x21, x22, x10
mul x11, x4, x2
mul x28, x4, x13
mul x16, x4, x5
mul x7, x4, x9
extr x17, x21, x14, #63
umulh x25, x4, x9
and x15, x14, #0x7fffffffffffffff
umulh x1, x4, x2
mul x24, x17, x26
umulh x12, x4, x13
adds x22, x23, x24
adcs x21, x8, x20
adcs x14, x3, x6
adc x17, x15, x10
umulh x23, x4, x5
adds x24, x11, x25
adcs x8, x28, x1
adcs x20, x16, x12
adc x6, x23, x10
stp x22, x21, [x0, #160]
stp x14, x17, [x0, #176]
ldr x3, [x0, #72]
mul x15, x3, x9
mul x4, x3, x2
mul x25, x3, x13
mul x11, x3, x5
umulh x28, x3, x9
umulh x1, x3, x2
umulh x16, x3, x13
umulh x12, x3, x5
ldr x23, [x0, #80]
adds x22, x24, x15
adcs x21, x8, x4
adcs x17, x20, x25
adcs x14, x6, x11
adc x3, x10, x10
mul x15, x23, x9
mul x24, x23, x2
mul x4, x23, x13
mul x8, x23, x5
adds x20, x21, x28
adcs x25, x17, x1
adcs x6, x14, x16
adc x11, x3, x12
umulh x21, x23, x9
umulh x28, x23, x2
umulh x17, x23, x13
umulh x1, x23, x5
ldr x14, [x0, #88]
adds x16, x20, x15
adcs x3, x25, x24
adcs x12, x6, x4
adcs x23, x11, x8
adc x20, x10, x10
mul x15, x14, x9
umulh x25, x14, x9
mul x24, x14, x2
umulh x6, x14, x2
mul x4, x14, x13
adds x8, x3, x21
adcs x11, x12, x28
adcs x9, x23, x17
adc x2, x20, x1
umulh x3, x14, x13
mul x21, x14, x5
umulh x12, x14, x5
adds x28, x8, x15
adcs x17, x11, x24
adcs x23, x9, x4
adcs x1, x2, x21
adc x20, x10, x10
adds x13, x17, x25
adcs x5, x23, x6
adcs x14, x1, x3
adc x8, x20, x12
umulh x15, x27, x8
mul x24, x27, x13
mul x11, x27, x5
mul x4, x27, x14
mul x9, x27, x8
umulh x21, x27, x14
umulh x2, x27, x13
umulh x25, x27, x5
adds x17, x7, x24
adcs x6, x22, x11
adcs x23, x16, x4
adcs x3, x28, x9
adc x1, x15, x10
ldp x12, x20, [x0, #352]
ldp x8, x14, [x0, #368]
ldp x13, x5, [x0, #384]
ldp x24, x7, [x0, #400]
adds x11, x3, x21
adc x22, x1, x10
subs x16, x12, x13
sbcs x4, x20, x5
sbcs x9, x8, x24
sbcs x28, x14, x7
csel x15, x10, x27, hs
extr x3, x22, x11, #63
and x21, x11, #0x7fffffffffffffff
mul x1, x3, x26
adds x13, x17, x1
adcs x12, x6, x2
adcs x5, x23, x25
adc x20, x21, x10
subs x8, x16, x15
sbcs x24, x4, x10
sbcs x14, x9, x10
sbc x7, x28, x10
stp x13, x12, [x0, #192]
stp x5, x20, [x0, #208]
ldp x22, x11, [x0, #384]
ldp x3, x17, [x0, #400]
stp x14, x7, [x0, #432]
stp x8, x24, [x0, #416]
ldr x1, [x0, #352]
ldr x6, [x0, #360]
umulh x2, x1, x22
umulh x23, x1, x11
umulh x25, x1, x3
umulh x21, x1, x17
mul x15, x1, x11
mul x16, x1, x3
mul x4, x1, x17
mul x9, x6, x22
mul x28, x6, x11
mul x13, x6, x3
mul x12, x1, x22
mul x5, x6, x17
umulh x20, x6, x22
umulh x14, x6, x11
adds x7, x15, x2
adcs x8, x16, x23
adcs x24, x4, x25
adc x1, x21, x10
umulh x2, x6, x3
umulh x15, x6, x17
ldr x23, [x0, #368]
adds x16, x7, x9
adcs x25, x8, x28
adcs x4, x24, x13
adcs x21, x1, x5
adc x6, x10, x10
mul x9, x23, x22
mul x7, x23, x11
mul x28, x23, x3
mul x8, x23, x17
adds x13, x25, x20
adcs x24, x4, x14
adcs x5, x21, x2
adc x1, x6, x15
umulh x20, x23, x22
umulh x25, x23, x11
umulh x14, x23, x3
umulh x4, x23, x17
ldr x21, [x0, #376]
adds x2, x13, x9
adcs x6, x24, x7
adcs x15, x5, x28
adcs x23, x1, x8
adc x9, x10, x10
mul x13, x21, x22
umulh x7, x21, x22
mul x24, x21, x11
umulh x5, x21, x11
mul x28, x21, x3
adds x1, x6, x20
adcs x8, x15, x25
adcs x22, x23, x14
adc x11, x9, x4
umulh x6, x21, x3
mul x20, x21, x17
umulh x15, x21, x17
adds x25, x1, x13
adcs x23, x8, x24
adcs x14, x22, x28
adcs x9, x11, x20
adc x4, x10, x10
adds x3, x23, x7
adcs x17, x14, x5
adcs x21, x9, x6
adc x1, x4, x15
umulh x13, x27, x1
mul x8, x27, x3
mul x24, x27, x17
mul x22, x27, x21
mul x28, x27, x1
umulh x20, x27, x21
umulh x11, x27, x3
umulh x23, x27, x17
adds x7, x12, x8
adcs x14, x16, x24
adcs x5, x2, x22
adcs x6, x25, x28
adc x9, x13, x10
ldp x15, x4, [x0, #432]
ldp x1, x21, [x0, #416]
movz x3, #56129, lsl #0
ldp x17, x12, [x0, #352]
ldp x8, x16, [x0, #368]
adds x24, x6, x20
adc x22, x9, x10
movk x3, #1, lsl #16
mul x2, x1, x3
extr x25, x22, x24, #63
mul x28, x21, x3
and x13, x24, #0x7fffffffffffffff
mul x6, x15, x3
mul x20, x25, x26
adds x9, x7, x20
adcs x22, x14, x11
adcs x24, x5, x23
adc x25, x13, x10
umulh x7, x4, x3
mul x20, x4, x3
adds x11, x17, x2
adcs x14, x12, x28
adcs x5, x8, x6
adcs x23, x16, x20
adc x13, x7, x10
stp x9, x22, [x0, #96]
stp x24, x25, [x0, #112]
umulh x4, x1, x3
umulh x17, x21, x3
umulh x2, x15, x3
ldr x12, [x0, #416]
adds x28, x23, x23
adc x6, x13, x13
mul x8, x6, x26
lsr x20, x28, #1
adds x16, x11, x8
adcs x7, x14, x4
adcs x9, x5, x17
adc x22, x20, x2
stp x16, x7, [x0, #128]
stp x9, x22, [x0, #144]
ldr x24, [x0, #424]
ldp x25, x1, [x0, #128]
ldp x21, x15, [x0, #144]
umulh x3, x12, x25
umulh x23, x12, x1
umulh x13, x12, x21
umulh x6, x12, x15
mul x28, x12, x1
mul x11, x12, x21
mul x8, x12, x15
mul x4, x24, x25
mul x14, x24, x1
mul x17, x24, x21
mul x5, x12, x25
mul x2, x24, x15
umulh x20, x24, x25
umulh x7, x24, x1
adds x16, x28, x3
adcs x9, x11, x23
adcs x22, x8, x13
adc x12, x6, x10
umulh x28, x24, x21
umulh x3, x24, x15
ldr x11, [x0, #432]
adds x23, x16, x4
adcs x8, x9, x14
adcs x13, x22, x17
adcs x6, x12, x2
adc x24, x10, x10
mul x16, x11, x25
mul x4, x11, x1
mul x9, x11, x21
mul x14, x11, x15
adds x22, x8, x20
adcs x17, x13, x7
adcs x2, x6, x28
adc x12, x24, x3
umulh x8, x11, x25
umulh x20, x11, x1
umulh x13, x11, x21
umulh x7, x11, x15
ldr x28, [x0, #440]
adds x6, x22, x16
adcs x3, x17, x4
adcs x24, x2, x9
adcs x11, x12, x14
adc x22, x10, x10
mul x16, x28, x25
umulh x4, x28, x25
mul x17, x28, x1
umulh x9, x28, x1
mul x2, x28, x21
adds x14, x3, x8
adcs x12, x24, x20
adcs x25, x11, x13
adc x1, x22, x7
umulh x8, x28, x21
mul x3, x28, x15
umulh x20, x28, x15
adds x24, x14, x16
adcs x13, x12, x17
adcs x11, x25, x2
adcs x7, x1, x3
adc x22, x10, x10
adds x21, x13, x4
adcs x28, x11, x9
adcs x15, x7, x8
adc x16, x22, x20
umulh x14, x27, x16
mul x17, x27, x21
mul x12, x27, x28
mul x2, x27, x15
mul x25, x27, x16
umulh x3, x27, x15
umulh x1, x27, x21
umulh x4, x27, x28
adds x13, x5, x17
adcs x9, x23, x12
adcs x11, x6, x2
adcs x7, x24, x25
adc x8, x14, x10
adds x22, x7, x3
adc x20, x8, x10
extr x16, x20, x22, #63
and x15, x22, #0x7fffffffffffffff
mul x21, x16, x26
adds x28, x13, x21
adcs x5, x9, x1
adcs x17, x11, x4
adc x23, x15, x10
stp x28, x5, [x0, #128]
stp x17, x23, [x0, #144]
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
.globl lab_sc_o1_19_15_1
lab_sc_o1_19_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
umulh x11, x3, x6
mul x4, x3, x15
umulh x8, x3, x15
mul x2, x3, x16
umulh x13, x3, x23
mul x17, x7, x16
umulh x5, x3, x16
mul x1, x3, x23
mul x9, x7, x23
mul x12, x7, x6
mul x21, x3, x6
umulh x20, x7, x6
umulh x22, x7, x16
mul x28, x7, x15
adds x24, x2, x11
adcs x25, x1, x5
adcs x14, x4, x13
adc x3, x8, x10
umulh x2, x7, x15
umulh x11, x7, x23
ldr x1, [x0, #336]
adds x5, x24, x12
adcs x4, x25, x17
adcs x13, x14, x9
adcs x8, x3, x28
adc x7, x10, x10
mul x12, x1, x6
mul x24, x1, x15
mul x25, x1, x16
mul x17, x1, x23
adds x14, x4, x20
adcs x9, x13, x22
adcs x3, x8, x11
adc x28, x7, x2
umulh x4, x1, x6
umulh x20, x1, x15
umulh x13, x1, x23
umulh x22, x1, x16
ldr x8, [x0, #344]
adds x11, x14, x12
adcs x2, x9, x25
adcs x7, x3, x17
adcs x1, x28, x24
adc x14, x10, x10
mul x12, x8, x6
umulh x9, x8, x6
mul x25, x8, x16
umulh x17, x8, x16
mul x3, x8, x15
adds x24, x2, x4
adcs x28, x7, x22
adcs x6, x1, x13
adc x16, x14, x20
umulh x2, x8, x15
mul x4, x8, x23
umulh x22, x8, x23
adds x7, x24, x12
adcs x13, x28, x25
adcs x1, x6, x4
adcs x20, x16, x3
adc x14, x10, x10
adds x15, x13, x9
adcs x23, x1, x17
adcs x8, x20, x22
adc x12, x14, x2
umulh x24, x27, x12
mul x25, x27, x15
mul x28, x27, x12
mul x4, x27, x23
mul x6, x27, x8
umulh x3, x27, x8
umulh x16, x27, x23
umulh x9, x27, x15
adds x13, x21, x25
adcs x17, x5, x4
adcs x1, x11, x6
adcs x22, x7, x28
adc x20, x24, x10
ldp x14, x2, [x0, #272]
ldp x12, x8, [x0, #256]
ldr x23, [x0, #288]
adds x15, x22, x3
adc x25, x20, x10
mul x21, x23, x8
mul x5, x23, x2
mul x4, x23, x14
mul x11, x23, x12
extr x6, x25, x15, #63
umulh x28, x23, x12
and x7, x15, #0x7fffffffffffffff
umulh x24, x23, x8
mul x22, x6, x26
umulh x3, x23, x14
adds x20, x13, x22
adcs x25, x17, x9
adcs x15, x1, x16
adc x6, x7, x10
umulh x13, x23, x2
adds x22, x21, x28
adcs x17, x4, x24
adcs x9, x5, x3
adc x1, x13, x10
stp x15, x6, [x0, #464]
stp x20, x25, [x0, #448]
ldr x16, [x0, #296]
mul x7, x16, x12
mul x23, x16, x8
mul x28, x16, x14
mul x21, x16, x2
umulh x24, x16, x2
ldr x4, [x0, #304]
umulh x3, x16, x14
umulh x5, x16, x12
umulh x13, x16, x8
adds x15, x22, x7
adcs x6, x17, x23
adcs x20, x9, x28
adcs x25, x1, x21
adc x16, x10, x10
mul x7, x4, x12
mul x22, x4, x14
mul x23, x4, x2
mul x17, x4, x8
adds x28, x6, x5
adcs x9, x20, x13
adcs x21, x25, x3
adc x1, x16, x24
umulh x5, x4, x14
ldr x6, [x0, #312]
umulh x13, x4, x2
umulh x20, x4, x12
umulh x25, x4, x8
adds x3, x28, x7
adcs x16, x9, x17
adcs x24, x21, x22
adcs x4, x1, x23
adc x7, x10, x10
mul x28, x6, x2
mul x17, x6, x12
umulh x9, x6, x12
umulh x21, x6, x8
mul x22, x6, x8
adds x1, x16, x20
adcs x23, x24, x25
adcs x12, x4, x5
adc x8, x7, x13
umulh x16, x6, x2
mul x20, x6, x14
umulh x24, x6, x14
adds x25, x1, x17
adcs x4, x23, x22
adcs x5, x12, x20
adcs x7, x8, x28
adc x13, x10, x10
adds x2, x4, x9
adcs x14, x5, x21
adcs x6, x7, x24
adc x1, x13, x16
umulh x17, x27, x1
mul x23, x27, x6
mul x22, x27, x14
mul x12, x27, x1
mul x20, x27, x2
umulh x28, x27, x6
umulh x8, x27, x14
umulh x4, x27, x2
adds x9, x11, x20
adcs x5, x15, x22
adcs x21, x3, x23
adcs x24, x25, x12
adc x7, x17, x10
ldp x16, x13, [x0, #224]
ldp x1, x6, [x0, #240]
adds x14, x24, x28
adc x2, x7, x10
mul x11, x16, x1
mul x20, x16, x6
umulh x15, x16, x13
umulh x22, x16, x1
mul x23, x16, x13
extr x3, x2, x14, #63
umulh x25, x16, x6
and x12, x14, #0x7fffffffffffffff
mul x17, x13, x1
mul x24, x3, x26
mul x28, x13, x6
adds x7, x9, x24
adcs x2, x5, x4
adcs x14, x21, x8
adc x3, x12, x10
umulh x9, x13, x6
umulh x24, x13, x1
umulh x4, x1, x6
stp x7, x2, [x0, #480]
adds x5, x11, x15
adcs x21, x20, x22
adc x8, x25, x10
stp x14, x3, [x0, #496]
mul x12, x1, x6
mul x7, x13, x13
umulh x2, x16, x16
mul x11, x16, x16
lsl x15, x23, #1
adds x20, x21, x17
adcs x22, x8, x28
adc x25, x9, x10
umulh x14, x13, x13
extr x3, x5, x23, #63
mul x16, x1, x1
umulh x21, x1, x1
adds x17, x22, x24
adcs x8, x25, x12
adc x28, x4, x10
extr x9, x20, x5, #63
umulh x13, x6, x6
mul x23, x6, x6
lsr x1, x28, #63
extr x22, x17, x20, #63
extr x24, x8, x17, #63
extr x25, x28, x8, #63
adds x12, x15, x2
adcs x4, x3, x7
adcs x5, x9, x14
adcs x6, x22, x16
adcs x20, x24, x21
adcs x17, x25, x23
adc x8, x1, x13
umulh x28, x27, x8
mul x15, x27, x6
mul x2, x27, x20
mul x3, x27, x17
mul x7, x27, x8
umulh x9, x27, x17
umulh x14, x27, x6
umulh x22, x27, x20
adds x16, x11, x15
adcs x21, x12, x2
adcs x24, x4, x3
adcs x23, x5, x7
adc x25, x28, x10
ldp x13, x1, [x0, #272]
ldp x8, x17, [x0, #256]
adds x6, x23, x9
adc x20, x25, x10
umulh x15, x8, x13
umulh x11, x8, x17
mul x12, x8, x13
mul x2, x8, x1
mul x3, x8, x17
extr x4, x20, x6, #63
umulh x7, x8, x1
and x5, x6, #0x7fffffffffffffff
mul x28, x17, x13
mul x9, x4, x26
mul x23, x17, x1
adds x25, x16, x9
adcs x20, x21, x14
adcs x6, x24, x22
adc x4, x5, x10
umulh x16, x17, x1
mul x9, x13, x1
umulh x21, x17, x13
stp x25, x20, [x0, #352]
adds x14, x12, x11
adcs x22, x2, x15
adc x24, x7, x10
umulh x5, x13, x1
stp x6, x4, [x0, #368]
umulh x25, x8, x8
mul x20, x17, x17
mul x11, x8, x8
lsl x12, x3, #1
adds x15, x22, x28
adcs x2, x24, x23
adc x7, x16, x10
umulh x4, x17, x17
extr x6, x14, x3, #63
mul x8, x13, x13
umulh x22, x13, x13
adds x28, x2, x21
adcs x24, x7, x9
adc x23, x5, x10
extr x16, x15, x14, #63
mul x17, x1, x1
umulh x3, x1, x1
lsr x13, x23, #63
extr x21, x28, x15, #63
extr x2, x24, x28, #63
extr x7, x23, x24, #63
adds x9, x12, x25
adcs x5, x6, x20
adcs x14, x16, x4
adcs x1, x21, x8
adcs x15, x2, x22
adcs x28, x7, x17
adc x24, x13, x3
umulh x23, x27, x24
mul x12, x27, x15
mul x25, x27, x24
mul x20, x27, x28
umulh x6, x27, x28
mul x4, x27, x1
umulh x16, x27, x15
umulh x8, x27, x1
adds x21, x11, x4
adcs x2, x9, x12
adcs x22, x5, x20
adcs x7, x14, x25
adc x17, x23, x10
ldp x3, x13, [x0, #480]
ldp x24, x28, [x0, #464]
ldp x15, x1, [x0, #448]
ldp x4, x11, [x0, #496]
adds x9, x7, x6
adc x12, x17, x10
subs x5, x15, x3
sbcs x20, x1, x13
sbcs x25, x24, x4
sbcs x14, x28, x11
csel x23, x10, x27, hs
extr x7, x12, x9, #63
and x6, x9, #0x7fffffffffffffff
mul x17, x7, x26
adds x3, x21, x17
adcs x15, x2, x8
adcs x13, x22, x16
adc x1, x6, x10
subs x24, x5, x23
sbcs x4, x20, x10
sbcs x28, x25, x10
sbc x11, x14, x10
stp x3, x15, [x0, #384]
stp x13, x1, [x0, #400]
umulh x12, x24, x4
umulh x9, x24, x28
mul x7, x24, x28
umulh x21, x24, x11
umulh x17, x4, x11
umulh x2, x28, x11
mul x8, x24, x11
mul x22, x4, x11
mul x16, x4, x28
umulh x6, x4, x28
mul x23, x28, x11
mul x5, x24, x4
adds x20, x7, x12
adcs x25, x8, x9
adc x14, x21, x10
mul x3, x4, x4
umulh x15, x24, x24
mul x13, x24, x24
lsl x1, x5, #1
adds x7, x25, x16
adcs x12, x14, x22
adc x8, x17, x10
umulh x9, x4, x4
extr x21, x20, x5, #63
mul x24, x28, x28
umulh x25, x28, x28
adds x16, x12, x6
adcs x14, x8, x23
adc x22, x2, x10
extr x17, x7, x20, #63
umulh x4, x11, x11
mul x5, x11, x11
lsr x28, x22, #63
extr x6, x22, x14, #63
extr x12, x14, x16, #63
extr x8, x16, x7, #63
adds x23, x1, x15
adcs x2, x21, x3
adcs x20, x17, x9
adcs x11, x8, x24
adcs x22, x12, x25
adcs x14, x6, x5
adc x16, x28, x4
umulh x7, x27, x16
mul x1, x27, x16
mul x15, x27, x14
mul x21, x27, x22
umulh x3, x27, x14
mul x17, x27, x11
umulh x9, x27, x22
umulh x24, x27, x11
adds x8, x13, x17
adcs x25, x23, x21
adcs x12, x2, x15
adcs x5, x20, x1
adc x6, x7, x10
ldp x4, x28, [x0, #464]
ldp x16, x14, [x0, #448]
ldp x22, x11, [x0, #480]
ldp x17, x13, [x0, #496]
adds x23, x5, x3
adc x21, x6, x10
adds x15, x16, x22
adcs x2, x14, x11
adcs x1, x4, x17
adcs x20, x28, x13
csel x7, x27, x10, hs
extr x3, x21, x23, #63
and x5, x23, #0x7fffffffffffffff
mul x6, x3, x26
adds x16, x8, x6
adcs x22, x25, x24
adcs x14, x12, x9
adc x11, x5, x10
adds x4, x15, x7
adcs x17, x2, x10
adc x28, x1, x10
stp x16, x22, [x0, #192]
stp x14, x11, [x0, #208]
mul x13, x4, x28
umulh x21, x4, x20
umulh x23, x4, x28
umulh x3, x4, x17
mul x8, x4, x20
mul x6, x17, x28
umulh x25, x17, x20
umulh x24, x28, x20
mul x12, x17, x20
mul x9, x4, x17
umulh x5, x17, x28
mul x15, x28, x20
adds x7, x13, x3
adcs x2, x8, x23
adc x1, x21, x10
umulh x16, x4, x4
lsl x22, x9, #1
mul x14, x17, x17
mul x11, x4, x4
adds x13, x2, x6
adcs x3, x1, x12
adc x8, x25, x10
umulh x23, x17, x17
extr x21, x7, x9, #63
mul x4, x28, x28
umulh x2, x28, x28
adds x6, x3, x5
adcs x1, x8, x15
adc x12, x24, x10
extr x25, x13, x7, #63
mul x17, x20, x20
umulh x9, x20, x20
lsr x28, x12, #63
extr x3, x6, x13, #63
extr x5, x12, x1, #63
extr x8, x1, x6, #63
adds x15, x22, x16
adcs x24, x21, x14
adcs x7, x25, x23
adcs x20, x3, x4
adcs x13, x8, x2
adcs x12, x5, x17
adc x6, x28, x9
umulh x1, x27, x6
mul x22, x27, x20
mul x16, x27, x12
mul x21, x27, x13
mul x14, x27, x6
umulh x25, x27, x12
umulh x23, x27, x20
umulh x3, x27, x13
adds x4, x11, x22
adcs x2, x15, x21
adcs x8, x24, x16
adcs x17, x7, x14
adc x5, x1, x10
ldp x9, x28, [x0, #192]
ldp x6, x12, [x0, #208]
ldr x20, [x0, #64]
adds x13, x17, x25
adc x22, x5, x10
mul x11, x20, x28
mul x15, x20, x6
mul x21, x20, x12
mul x16, x20, x9
extr x24, x22, x13, #63
umulh x7, x20, x9
and x14, x13, #0x7fffffffffffffff
umulh x1, x20, x28
mul x25, x24, x26
umulh x17, x20, x6
adds x5, x4, x25
adcs x22, x2, x23
adcs x13, x8, x3
adc x24, x14, x10
umulh x4, x20, x12
adds x25, x11, x7
adcs x2, x15, x1
adcs x23, x21, x17
adc x3, x4, x10
stp x5, x22, [x0, #160]
stp x13, x24, [x0, #176]
ldr x8, [x0, #72]
mul x14, x8, x9
mul x20, x8, x28
mul x7, x8, x12
mul x11, x8, x6
umulh x15, x8, x9
ldr x1, [x0, #80]
umulh x21, x8, x12
umulh x17, x8, x28
umulh x4, x8, x6
adds x5, x25, x14
adcs x22, x2, x20
adcs x24, x23, x11
adcs x13, x3, x7
adc x8, x10, x10
mul x14, x1, x9
mul x25, x1, x28
mul x20, x1, x6
umulh x2, x1, x28
adds x23, x22, x15
adcs x11, x24, x17
adcs x3, x13, x4
adc x7, x8, x21
umulh x22, x1, x12
mul x15, x1, x12
umulh x24, x1, x9
umulh x17, x1, x6
ldr x13, [x0, #88]
adds x4, x23, x14
adcs x8, x11, x25
adcs x21, x3, x20
adcs x1, x7, x15
adc x23, x10, x10
mul x14, x13, x9
umulh x11, x13, x9
mul x25, x13, x28
umulh x3, x13, x28
mul x20, x13, x12
adds x15, x8, x24
adcs x7, x21, x2
adcs x9, x1, x17
adc x28, x23, x22
umulh x8, x13, x12
mul x24, x13, x6
umulh x21, x13, x6
adds x2, x15, x14
adcs x17, x7, x25
adcs x1, x9, x24
adcs x22, x28, x20
adc x23, x10, x10
adds x12, x17, x11
adcs x6, x1, x3
adcs x13, x22, x21
adc x15, x23, x8
umulh x14, x27, x15
mul x25, x27, x13
mul x7, x27, x6
mul x24, x27, x15
mul x9, x27, x12
umulh x20, x27, x13
umulh x28, x27, x6
umulh x11, x27, x12
adds x17, x16, x9
adcs x3, x5, x7
adcs x1, x4, x25
adcs x21, x2, x24
adc x22, x14, x10
ldp x8, x23, [x0, #352]
ldp x15, x13, [x0, #384]
ldp x6, x12, [x0, #400]
ldp x9, x16, [x0, #368]
adds x7, x21, x20
adc x5, x22, x10
subs x4, x8, x15
sbcs x25, x23, x13
sbcs x24, x9, x6
sbcs x2, x16, x12
csel x14, x10, x27, hs
extr x21, x5, x7, #63
and x20, x7, #0x7fffffffffffffff
mul x22, x21, x26
adds x15, x17, x22
adcs x8, x3, x11
adcs x13, x1, x28
adc x23, x20, x10
subs x9, x4, x14
sbcs x6, x25, x10
sbcs x16, x24, x10
sbc x12, x2, x10
stp x15, x8, [x0, #192]
stp x13, x23, [x0, #208]
ldp x5, x7, [x0, #384]
ldr x21, [x0, #352]
stp x16, x12, [x0, #432]
stp x9, x6, [x0, #416]
ldp x17, x22, [x0, #400]
ldr x3, [x0, #360]
umulh x11, x21, x5
umulh x1, x21, x7
mul x28, x21, x7
umulh x20, x21, x22
mul x14, x21, x22
umulh x4, x21, x17
mul x25, x3, x7
mul x24, x3, x5
mul x2, x3, x17
mul x15, x21, x17
mul x8, x21, x5
mul x13, x3, x22
umulh x23, x3, x7
umulh x16, x3, x5
adds x12, x28, x11
adcs x9, x15, x1
adcs x6, x14, x4
adc x21, x20, x10
umulh x11, x3, x22
umulh x28, x3, x17
ldr x1, [x0, #368]
adds x15, x12, x24
adcs x4, x9, x25
adcs x14, x6, x2
adcs x20, x21, x13
adc x3, x10, x10
mul x24, x1, x5
mul x12, x1, x22
mul x25, x1, x17
mul x9, x1, x7
adds x2, x4, x16
adcs x6, x14, x23
adcs x13, x20, x28
adc x21, x3, x11
ldr x16, [x0, #376]
umulh x4, x1, x5
umulh x23, x1, x7
umulh x14, x1, x22
umulh x20, x1, x17
adds x28, x2, x24
adcs x3, x6, x9
adcs x11, x13, x25
adcs x1, x21, x12
adc x24, x10, x10
mul x2, x16, x17
umulh x9, x16, x7
mul x6, x16, x7
umulh x13, x16, x5
mul x25, x16, x5
adds x21, x3, x4
adcs x12, x11, x23
adcs x7, x1, x20
adc x5, x24, x14
umulh x3, x16, x17
mul x4, x16, x22
umulh x11, x16, x22
adds x23, x21, x25
adcs x1, x12, x6
adcs x20, x7, x2
adcs x24, x5, x4
adc x14, x10, x10
adds x17, x1, x13
adcs x22, x20, x9
adcs x16, x24, x3
adc x21, x14, x11
umulh x25, x27, x21
mul x12, x27, x21
mul x6, x27, x22
umulh x7, x27, x16
mul x2, x27, x17
mul x4, x27, x16
umulh x5, x27, x22
umulh x1, x27, x17
adds x13, x8, x2
adcs x20, x15, x6
adcs x9, x28, x4
adcs x3, x23, x12
adc x24, x25, x10
ldp x11, x14, [x0, #432]
movz x21, #56129, lsl #0
ldp x16, x22, [x0, #416]
ldp x17, x8, [x0, #368]
ldp x2, x15, [x0, #352]
adds x6, x3, x7
adc x4, x24, x10
movk x21, #1, lsl #16
mul x28, x16, x21
extr x23, x4, x6, #63
mul x12, x22, x21
and x25, x6, #0x7fffffffffffffff
mul x3, x11, x21
mul x7, x23, x26
adds x24, x13, x7
adcs x4, x20, x1
adcs x6, x9, x5
adc x23, x25, x10
umulh x13, x14, x21
mul x7, x14, x21
adds x1, x2, x28
adcs x20, x15, x12
adcs x9, x17, x3
adcs x5, x8, x7
adc x25, x13, x10
stp x6, x23, [x0, #112]
stp x24, x4, [x0, #96]
umulh x14, x16, x21
umulh x2, x11, x21
umulh x28, x22, x21
ldr x15, [x0, #416]
adds x12, x5, x5
adc x3, x25, x25
mul x17, x3, x26
lsr x7, x12, #1
adds x8, x1, x17
adcs x13, x20, x14
adcs x6, x9, x28
adc x23, x7, x2
stp x8, x13, [x0, #128]
stp x6, x23, [x0, #144]
ldr x24, [x0, #424]
ldp x4, x16, [x0, #128]
ldp x11, x22, [x0, #144]
umulh x21, x15, x4
umulh x5, x15, x11
mul x25, x15, x22
umulh x3, x15, x16
mul x12, x15, x11
umulh x1, x15, x22
mul x17, x24, x16
mul x14, x15, x16
mul x20, x24, x4
mul x28, x24, x11
mul x9, x15, x4
mul x2, x24, x22
umulh x7, x24, x4
umulh x13, x24, x16
adds x8, x14, x21
adcs x6, x12, x3
adcs x23, x25, x5
adc x15, x1, x10
umulh x14, x24, x22
umulh x21, x24, x11
ldr x12, [x0, #432]
adds x3, x8, x20
adcs x25, x6, x17
adcs x5, x23, x28
adcs x1, x15, x2
adc x24, x10, x10
mul x8, x12, x4
mul x20, x12, x22
mul x6, x12, x11
mul x17, x12, x16
adds x23, x25, x7
adcs x28, x5, x13
adcs x2, x1, x21
adc x15, x24, x14
umulh x25, x12, x16
umulh x7, x12, x22
umulh x5, x12, x11
umulh x13, x12, x4
ldr x21, [x0, #440]
adds x1, x23, x8
adcs x14, x28, x17
adcs x24, x2, x6
adcs x12, x15, x20
adc x23, x10, x10
mul x8, x21, x4
umulh x17, x21, x4
mul x28, x21, x11
mul x6, x21, x22
adds x2, x14, x13
adcs x20, x24, x25
adcs x15, x12, x5
adc x4, x23, x7
umulh x13, x21, x11
umulh x14, x21, x22
mul x25, x21, x16
umulh x24, x21, x16
adds x5, x2, x8
adcs x12, x20, x25
adcs x7, x15, x28
adcs x23, x4, x6
adc x11, x10, x10
adds x22, x12, x17
adcs x21, x7, x24
adcs x16, x23, x13
adc x8, x11, x14
umulh x2, x27, x8
mul x25, x27, x21
mul x20, x27, x22
mul x28, x27, x16
mul x15, x27, x8
umulh x6, x27, x16
umulh x4, x27, x22
umulh x17, x27, x21
adds x12, x9, x20
adcs x24, x3, x25
adcs x7, x1, x28
adcs x23, x5, x15
adc x13, x2, x10
adds x11, x23, x6
adc x14, x13, x10
extr x8, x14, x11, #63
and x16, x11, #0x7fffffffffffffff
mul x22, x8, x26
adds x21, x12, x22
adcs x9, x24, x4
adcs x20, x7, x17
adc x3, x16, x10
stp x21, x9, [x0, #128]
stp x20, x3, [x0, #144]
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
.globl lab_sc_o1_21_30_0
lab_sc_o1_21_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x11, x16, x5
adcs x25, x1, x28
csel x24, x27, x10, hs
stp x9, x21, [x0, #224]
stp x17, x3, [x0, #240]
stp x6, x15, [x0, #256]
stp x8, x23, [x0, #272]
subs x7, x12, x14
sbcs x16, x20, x10
sbcs x5, x13, x10
sbc x28, x4, x10
adds x1, x22, x24
adcs x9, x2, x10
adc x21, x11, x10
ldp x17, x3, [x0, #224]
ldp x6, x15, [x0, #240]
stp x7, x16, [x0, #320]
stp x1, x9, [x0, #288]
stp x21, x25, [x0, #304]
stp x5, x28, [x0, #336]
ldr x8, [x0, #320]
ldr x23, [x0, #328]
ldr x12, [x0, #336]
umulh x14, x8, x17
umulh x20, x8, x3
umulh x13, x8, x6
umulh x4, x8, x15
mul x22, x8, x3
mul x24, x8, x6
mul x2, x8, x15
mul x11, x23, x17
mul x7, x23, x3
mul x16, x23, x6
mul x1, x23, x15
umulh x9, x23, x17
umulh x21, x23, x3
umulh x25, x23, x6
umulh x5, x23, x15
adds x28, x22, x14
adcs x23, x24, x20
adcs x22, x2, x13
adc x14, x4, x10
mul x24, x8, x17
mul x20, x12, x17
mul x2, x12, x3
mul x13, x12, x6
adds x4, x28, x11
adcs x8, x23, x7
adcs x11, x22, x16
adcs x28, x14, x1
adc x23, x10, x10
mul x7, x12, x15
umulh x22, x12, x17
umulh x16, x12, x3
adds x14, x8, x9
adcs x1, x11, x21
adcs x8, x28, x25
adc x9, x23, x5
umulh x11, x12, x6
umulh x21, x12, x15
ldr x28, [x0, #344]
adds x25, x14, x20
adcs x5, x1, x2
adcs x23, x8, x13
adcs x12, x9, x7
adc x14, x10, x10
mul x20, x28, x17
umulh x1, x28, x17
mul x2, x28, x3
umulh x13, x28, x3
mul x8, x28, x6
umulh x7, x28, x6
mul x9, x28, x15
umulh x17, x28, x15
adds x3, x5, x22
adcs x6, x23, x16
adcs x15, x12, x11
adc x28, x14, x21
adds x5, x3, x20
adcs x22, x6, x2
adcs x16, x15, x8
adcs x23, x28, x9
adc x11, x10, x10
ldp x12, x21, [x0, #256]
ldp x14, x20, [x0, #272]
ldr x3, [x0, #288]
adds x2, x22, x1
adcs x6, x16, x13
adcs x8, x23, x7
adc x15, x11, x17
mul x9, x3, x21
mul x28, x3, x14
mul x1, x3, x20
mul x22, x3, x12
umulh x13, x27, x15
mul x16, x27, x15
mul x7, x27, x2
umulh x23, x3, x12
umulh x11, x27, x2
mul x17, x27, x6
umulh x15, x27, x6
mul x2, x27, x8
umulh x6, x27, x8
adds x8, x24, x7
adcs x7, x4, x17
adcs x24, x25, x2
adcs x4, x5, x16
adc x17, x13, x10
umulh x25, x3, x21
umulh x2, x3, x14
umulh x16, x3, x20
ldr x5, [x0, #296]
adds x13, x9, x23
adcs x3, x28, x25
adcs x23, x1, x2
adc x9, x16, x10
adds x25, x4, x6
adc x28, x17, x10
mul x2, x5, x12
mul x1, x5, x21
mul x16, x5, x14
mul x4, x5, x20
extr x6, x28, x25, #63
and x17, x25, #0x7fffffffffffffff
mul x28, x6, x26
adds x25, x13, x2
adcs x6, x3, x1
adcs x2, x23, x16
adcs x13, x9, x4
adc x1, x10, x10
adds x3, x8, x28
adcs x16, x7, x11
adcs x23, x24, x15
adc x4, x17, x10
umulh x9, x5, x12
umulh x8, x5, x21
umulh x28, x5, x14
umulh x7, x5, x20
stp x3, x16, [x0, #448]
stp x23, x4, [x0, #464]
ldr x11, [x0, #304]
adds x24, x6, x9
adcs x15, x2, x8
adcs x17, x13, x28
adc x5, x1, x7
ldr x3, [x0, #312]
mul x16, x11, x12
mul x23, x11, x21
mul x4, x11, x14
mul x9, x11, x20
umulh x6, x11, x12
umulh x8, x11, x21
umulh x2, x11, x14
umulh x13, x11, x20
mul x28, x3, x12
umulh x1, x3, x12
mul x7, x3, x21
adds x11, x24, x16
adcs x12, x15, x23
adcs x16, x17, x4
adcs x24, x5, x9
adc x23, x10, x10
umulh x15, x3, x21
mul x17, x3, x14
umulh x4, x3, x14
mul x5, x3, x20
umulh x9, x3, x20
adds x21, x12, x6
adcs x14, x16, x8
adcs x20, x24, x2
adc x3, x23, x13
adds x12, x21, x28
adcs x6, x14, x7
adcs x16, x20, x17
adcs x8, x3, x5
adc x24, x10, x10
ldp x2, x23, [x0, #224]
ldp x13, x21, [x0, #240]
adds x28, x6, x1
adcs x14, x16, x15
adcs x7, x8, x4
adc x20, x24, x9
umulh x17, x2, x23
umulh x5, x2, x13
mul x3, x2, x13
mul x6, x2, x21
mul x1, x2, x23
umulh x16, x27, x20
mul x15, x27, x20
mul x4, x27, x28
umulh x8, x2, x21
umulh x9, x27, x28
mul x24, x27, x14
umulh x20, x27, x14
mul x28, x27, x7
umulh x14, x27, x7
adds x7, x22, x4
adcs x22, x25, x24
adcs x4, x11, x28
adcs x25, x12, x15
adc x24, x16, x10
umulh x28, x23, x21
adds x11, x3, x17
adcs x12, x6, x5
adc x15, x8, x10
mul x16, x23, x13
mul x3, x23, x21
umulh x17, x23, x13
umulh x6, x13, x21
adds x5, x12, x16
adcs x8, x15, x3
adc x12, x28, x10
adds x16, x25, x14
adc x15, x24, x10
mul x3, x13, x21
extr x28, x15, x16, #63
and x25, x16, #0x7fffffffffffffff
adds x14, x8, x17
adcs x24, x12, x3
adc x15, x6, x10
mul x16, x28, x26
adds x8, x7, x16
adcs x17, x22, x9
adcs x12, x4, x20
adc x3, x25, x10
lsr x6, x15, #63
extr x28, x15, x24, #63
extr x7, x24, x14, #63
extr x16, x14, x5, #63
extr x9, x5, x11, #63
extr x22, x11, x1, #63
stp x8, x17, [x0, #480]
lsl x4, x1, #1
stp x12, x3, [x0, #496]
umulh x20, x2, x2
umulh x25, x23, x23
umulh x15, x13, x13
umulh x24, x21, x21
mul x14, x23, x23
mul x5, x13, x13
mul x11, x21, x21
mul x8, x2, x2
adds x17, x4, x20
adcs x1, x22, x14
adcs x12, x9, x25
adcs x3, x16, x5
adcs x23, x7, x15
adcs x13, x28, x11
adc x21, x6, x24
ldp x2, x4, [x0, #256]
ldp x20, x22, [x0, #272]
umulh x14, x2, x4
umulh x9, x2, x20
mul x25, x2, x20
mul x16, x2, x22
mul x5, x2, x4
umulh x15, x27, x21
mul x7, x27, x21
mul x11, x27, x3
umulh x28, x2, x22
umulh x24, x27, x3
mul x6, x27, x23
umulh x21, x27, x23
mul x3, x27, x13
umulh x23, x27, x13
adds x13, x8, x11
adcs x11, x17, x6
adcs x8, x1, x3
adcs x17, x12, x7
adc x6, x15, x10
umulh x3, x4, x22
adds x1, x25, x14
adcs x7, x16, x9
adc x12, x28, x10
mul x15, x4, x20
mul x14, x4, x22
umulh x25, x4, x20
umulh x9, x20, x22
adds x16, x7, x15
adcs x28, x12, x14
adc x7, x3, x10
mul x15, x20, x22
adds x12, x17, x23
adc x14, x6, x10
adds x3, x28, x25
adcs x23, x7, x15
adc x17, x9, x10
extr x6, x14, x12, #63
and x25, x12, #0x7fffffffffffffff
mul x28, x6, x26
lsr x7, x17, #63
extr x15, x17, x23, #63
adds x9, x13, x28
adcs x14, x11, x24
adcs x12, x8, x21
adc x6, x25, x10
extr x17, x23, x3, #63
extr x13, x3, x16, #63
extr x28, x16, x1, #63
extr x11, x1, x5, #63
stp x9, x14, [x0, #352]
lsl x24, x5, #1
stp x12, x6, [x0, #368]
umulh x21, x2, x2
umulh x8, x4, x4
umulh x25, x20, x20
umulh x23, x22, x22
mul x3, x4, x4
mul x16, x20, x20
mul x1, x22, x22
mul x9, x2, x2
adds x14, x24, x21
adcs x5, x11, x3
adcs x6, x28, x8
adcs x12, x13, x16
adcs x4, x17, x25
adcs x20, x15, x1
adc x22, x7, x23
ldp x2, x24, [x0, #448]
ldp x21, x3, [x0, #464]
ldp x11, x8, [x0, #480]
ldp x28, x16, [x0, #496]
subs x13, x2, x11
sbcs x17, x24, x8
sbcs x25, x21, x28
sbcs x15, x3, x16
csel x1, x10, x27, hs
umulh x23, x27, x22
mul x7, x27, x12
mul x11, x27, x4
mul x2, x27, x22
umulh x8, x27, x12
umulh x24, x27, x4
mul x21, x27, x20
umulh x28, x27, x20
adds x3, x9, x7
adcs x16, x14, x11
adcs x22, x5, x21
adcs x12, x6, x2
adc x4, x23, x10
subs x20, x13, x1
sbcs x7, x17, x10
sbcs x9, x25, x10
sbc x14, x15, x10
adds x11, x12, x28
adc x5, x4, x10
umulh x21, x20, x7
umulh x2, x20, x9
umulh x6, x20, x14
mul x23, x20, x9
mul x1, x20, x14
mul x13, x7, x9
extr x17, x5, x11, #63
and x25, x11, #0x7fffffffffffffff
umulh x15, x7, x14
mul x12, x7, x14
mul x28, x17, x26
umulh x4, x7, x9
umulh x5, x9, x14
adds x11, x3, x28
adcs x17, x16, x8
adcs x3, x22, x24
adc x28, x25, x10
adds x16, x23, x21
adcs x8, x1, x2
adc x22, x6, x10
mul x24, x9, x14
mul x25, x20, x7
stp x11, x17, [x0, #384]
stp x3, x28, [x0, #400]
adds x23, x8, x13
adcs x21, x22, x12
adc x1, x15, x10
umulh x2, x20, x20
umulh x6, x7, x7
umulh x11, x9, x9
umulh x17, x14, x14
mul x3, x7, x7
mul x28, x9, x9
mul x8, x14, x14
mul x13, x20, x20
extr x22, x16, x25, #63
adds x12, x21, x4
adcs x15, x1, x24
adc x7, x5, x10
extr x9, x23, x16, #63
lsl x14, x25, #1
lsr x20, x7, #63
extr x4, x7, x15, #63
extr x21, x15, x12, #63
extr x1, x12, x23, #63
adds x24, x14, x2
adcs x5, x22, x3
adcs x16, x9, x6
adcs x25, x1, x28
adcs x7, x21, x11
adcs x15, x4, x8
adc x12, x20, x17
ldp x23, x14, [x0, #448]
ldp x2, x22, [x0, #464]
ldp x3, x9, [x0, #480]
ldp x6, x28, [x0, #496]
adds x1, x23, x3
adcs x11, x14, x9
adcs x21, x2, x6
adcs x8, x22, x28
csel x4, x27, x10, hs
umulh x17, x27, x12
mul x20, x27, x25
mul x23, x27, x7
mul x3, x27, x12
umulh x14, x27, x25
umulh x9, x27, x7
mul x2, x27, x15
umulh x6, x27, x15
adds x22, x13, x20
adcs x28, x24, x23
adcs x12, x5, x2
adcs x25, x16, x3
adc x7, x17, x10
adds x15, x1, x4
adcs x20, x11, x10
adc x13, x21, x10
umulh x24, x15, x20
umulh x23, x15, x13
umulh x2, x15, x8
adds x5, x25, x6
adc x3, x7, x10
mul x16, x15, x13
mul x17, x15, x8
umulh x1, x20, x8
mul x4, x20, x13
mul x11, x20, x8
umulh x21, x20, x13
extr x6, x3, x5, #63
and x25, x5, #0x7fffffffffffffff
umulh x7, x13, x8
mul x3, x6, x26
adds x5, x16, x24
adcs x6, x17, x23
adc x16, x2, x10
mul x24, x13, x8
mul x17, x15, x20
adds x23, x22, x3
adcs x2, x28, x14
adcs x22, x12, x9
adc x3, x25, x10
adds x28, x6, x4
adcs x14, x16, x11
adc x12, x1, x10
stp x23, x2, [x0, #192]
stp x22, x3, [x0, #208]
adds x9, x14, x21
adcs x25, x12, x24
adc x6, x7, x10
umulh x4, x15, x15
umulh x16, x20, x20
umulh x11, x13, x13
umulh x1, x8, x8
mul x23, x20, x20
mul x2, x13, x13
mul x22, x8, x8
extr x3, x28, x5, #63
extr x14, x5, x17, #63
lsr x21, x6, #63
extr x12, x6, x25, #63
extr x24, x25, x9, #63
extr x7, x9, x28, #63
lsl x20, x17, #1
mul x13, x15, x15
adds x8, x20, x4
adcs x5, x14, x23
adcs x6, x3, x16
adcs x25, x7, x2
adcs x9, x24, x11
adcs x28, x12, x22
adc x17, x21, x1
ldp x15, x20, [x0, #192]
ldp x4, x14, [x0, #208]
ldr x23, [x0, #64]
mul x3, x23, x20
mul x16, x23, x4
mul x7, x23, x14
umulh x2, x27, x17
mul x11, x27, x17
mul x24, x27, x25
umulh x22, x23, x15
umulh x12, x27, x25
mul x1, x27, x9
umulh x21, x23, x20
umulh x17, x27, x9
mul x25, x27, x28
umulh x9, x27, x28
adds x28, x13, x24
adcs x24, x8, x1
adcs x13, x5, x25
adcs x8, x6, x11
adc x1, x2, x10
umulh x25, x23, x4
umulh x5, x23, x14
ldr x6, [x0, #72]
mul x11, x23, x15
adds x2, x3, x22
adcs x23, x16, x21
adcs x22, x7, x25
adc x3, x5, x10
adds x16, x8, x9
adc x21, x1, x10
mul x7, x6, x15
mul x25, x6, x20
mul x5, x6, x4
mul x9, x6, x14
extr x8, x21, x16, #63
and x1, x16, #0x7fffffffffffffff
mul x21, x8, x26
adds x16, x2, x7
adcs x8, x23, x25
adcs x7, x22, x5
adcs x2, x3, x9
adc x25, x10, x10
adds x23, x28, x21
adcs x22, x24, x12
adcs x5, x13, x17
adc x3, x1, x10
umulh x9, x6, x15
umulh x28, x6, x20
umulh x21, x6, x4
umulh x24, x6, x14
stp x23, x22, [x0, #160]
stp x5, x3, [x0, #176]
ldr x12, [x0, #80]
adds x17, x8, x9
adcs x13, x7, x28
adcs x1, x2, x21
adc x6, x25, x24
ldr x23, [x0, #88]
mul x22, x12, x15
mul x3, x12, x20
mul x5, x12, x4
mul x8, x12, x14
umulh x9, x12, x15
umulh x7, x12, x20
umulh x28, x12, x4
umulh x2, x12, x14
mul x21, x23, x15
umulh x25, x23, x15
mul x24, x23, x20
adds x12, x17, x22
adcs x15, x13, x3
adcs x17, x1, x5
adcs x22, x6, x8
adc x13, x10, x10
umulh x3, x23, x20
mul x1, x23, x4
umulh x5, x23, x4
mul x8, x23, x14
umulh x6, x23, x14
adds x20, x15, x9
adcs x4, x17, x7
adcs x14, x22, x28
adc x23, x13, x2
adds x15, x20, x21
adcs x9, x4, x24
adcs x17, x14, x1
adcs x7, x23, x8
adc x28, x10, x10
ldp x22, x2, [x0, #352]
ldp x13, x20, [x0, #368]
ldp x21, x24, [x0, #384]
adds x4, x9, x25
adcs x1, x17, x3
adcs x14, x7, x5
adc x8, x28, x6
ldp x23, x25, [x0, #400]
umulh x9, x27, x8
mul x3, x27, x8
mul x17, x27, x4
umulh x5, x27, x4
subs x7, x22, x21
sbcs x6, x2, x24
sbcs x28, x13, x23
sbcs x8, x20, x25
csel x4, x10, x27, hs
mul x21, x27, x1
umulh x22, x27, x1
mul x24, x27, x14
umulh x2, x27, x14
adds x13, x11, x17
adcs x23, x16, x21
adcs x20, x12, x24
adcs x25, x15, x3
adc x1, x9, x10
subs x14, x7, x4
sbcs x17, x6, x10
sbcs x11, x28, x10
sbc x21, x8, x10
ldp x16, x12, [x0, #384]
ldp x24, x3, [x0, #400]
ldr x15, [x0, #352]
adds x9, x25, x2
adc x4, x1, x10
stp x11, x21, [x0, #432]
stp x14, x17, [x0, #416]
mul x7, x15, x12
mul x6, x15, x24
mul x28, x15, x3
mul x8, x15, x16
extr x25, x4, x9, #63
umulh x2, x15, x16
and x1, x9, #0x7fffffffffffffff
umulh x11, x15, x12
mul x21, x25, x26
umulh x14, x15, x24
adds x17, x13, x21
adcs x4, x23, x5
adcs x9, x20, x22
adc x25, x1, x10
umulh x13, x15, x3
adds x21, x7, x2
adcs x23, x6, x11
adcs x5, x28, x14
adc x20, x13, x10
stp x17, x4, [x0, #192]
stp x9, x25, [x0, #208]
ldr x22, [x0, #360]
ldr x1, [x0, #368]
mul x15, x22, x16
mul x2, x22, x12
mul x7, x22, x24
mul x11, x22, x3
umulh x6, x22, x16
umulh x14, x22, x12
umulh x28, x22, x24
umulh x13, x22, x3
mul x17, x1, x16
mul x4, x1, x12
mul x9, x1, x24
adds x25, x21, x15
adcs x22, x23, x2
adcs x15, x5, x7
adcs x21, x20, x11
adc x2, x10, x10
mul x23, x1, x3
umulh x7, x1, x16
umulh x5, x1, x12
adds x11, x22, x6
adcs x20, x15, x14
adcs x6, x21, x28
adc x22, x2, x13
umulh x14, x1, x24
umulh x15, x1, x3
ldr x21, [x0, #376]
adds x28, x11, x17
adcs x2, x20, x4
adcs x13, x6, x9
adcs x1, x22, x23
adc x17, x10, x10
mul x11, x21, x16
umulh x4, x21, x16
mul x20, x21, x12
umulh x6, x21, x12
mul x9, x21, x24
umulh x22, x21, x24
mul x23, x21, x3
umulh x16, x21, x3
adds x12, x2, x7
adcs x24, x13, x5
adcs x3, x1, x14
adc x21, x17, x15
adds x2, x12, x11
adcs x7, x24, x20
adcs x13, x3, x9
adcs x5, x21, x23
adc x1, x10, x10
ldp x14, x17, [x0, #416]
ldp x15, x12, [x0, #352]
ldp x11, x24, [x0, #368]
adds x20, x7, x4
adcs x3, x13, x6
adcs x9, x5, x22
adc x23, x1, x16
ldp x21, x7, [x0, #432]
movz x4, #56129, lsl #0
movk x4, #1, lsl #16
mul x13, x14, x4
umulh x6, x27, x23
mul x22, x27, x23
mul x5, x27, x20
mul x16, x17, x4
umulh x1, x27, x20
mul x23, x27, x3
umulh x20, x27, x3
mul x3, x27, x9
umulh x9, x27, x9
adds x8, x8, x5
adcs x5, x25, x23
adcs x25, x28, x3
adcs x23, x2, x22
adc x3, x6, x10
umulh x28, x14, x4
umulh x2, x17, x4
umulh x22, x7, x4
mul x6, x7, x4
mul x14, x21, x4
umulh x17, x21, x4
adds x7, x15, x13
adcs x21, x12, x16
adcs x4, x11, x14
adcs x15, x24, x6
adc x13, x22, x10
adds x12, x23, x9
adc x16, x3, x10
extr x14, x16, x12, #63
and x11, x12, #0x7fffffffffffffff
mul x6, x14, x26
adds x24, x15, x15
adc x22, x13, x13
adds x23, x8, x6
adcs x9, x5, x1
adcs x3, x25, x20
adc x16, x11, x10
mul x12, x22, x26
lsr x14, x24, #1
adds x15, x7, x12
adcs x13, x21, x28
adcs x8, x4, x2
adc x6, x14, x17
stp x23, x9, [x0, #96]
stp x3, x16, [x0, #112]
ldr x1, [x0, #416]
ldr x5, [x0, #424]
stp x15, x13, [x0, #128]
stp x8, x6, [x0, #144]
ldp x25, x20, [x0, #128]
ldp x11, x22, [x0, #144]
ldr x24, [x0, #432]
umulh x7, x1, x25
umulh x12, x1, x20
umulh x28, x1, x11
umulh x21, x1, x22
mul x2, x1, x20
mul x4, x1, x11
mul x17, x1, x22
mul x14, x5, x25
mul x23, x5, x20
mul x9, x5, x11
mul x3, x5, x22
umulh x16, x5, x25
umulh x13, x5, x20
umulh x15, x5, x11
umulh x8, x5, x22
adds x6, x2, x7
adcs x5, x4, x12
adcs x2, x17, x28
adc x7, x21, x10
mul x4, x1, x25
mul x12, x24, x25
mul x17, x24, x20
mul x28, x24, x11
adds x21, x6, x14
adcs x1, x5, x23
adcs x6, x2, x9
adcs x14, x7, x3
adc x5, x10, x10
mul x23, x24, x22
umulh x2, x24, x25
umulh x9, x24, x20
adds x3, x1, x16
adcs x7, x6, x13
adcs x1, x14, x15
adc x16, x5, x8
umulh x6, x24, x11
umulh x13, x24, x22
ldr x15, [x0, #440]
adds x14, x3, x12
adcs x8, x7, x17
adcs x5, x1, x28
adcs x24, x16, x23
adc x3, x10, x10
mul x12, x15, x25
umulh x17, x15, x25
mul x7, x15, x20
umulh x28, x15, x20
mul x1, x15, x11
umulh x23, x15, x11
mul x16, x15, x22
umulh x25, x15, x22
adds x20, x8, x2
adcs x11, x5, x9
adcs x15, x24, x6
adc x22, x3, x13
adds x2, x20, x12
adcs x8, x11, x7
adcs x9, x15, x1
adcs x5, x22, x16
adc x6, x10, x10
adds x24, x8, x17
adcs x13, x9, x28
adcs x3, x5, x23
adc x12, x6, x25
umulh x20, x27, x12
mul x7, x27, x24
mul x11, x27, x13
mul x1, x27, x3
mul x15, x27, x12
umulh x16, x27, x3
umulh x22, x27, x24
umulh x17, x27, x13
adds x8, x4, x7
adcs x28, x21, x11
adcs x9, x14, x1
adcs x5, x2, x15
adc x23, x20, x10
adds x6, x5, x16
adc x25, x23, x10
extr x12, x25, x6, #63
and x3, x6, #0x7fffffffffffffff
mul x24, x12, x26
adds x13, x8, x24
adcs x4, x28, x22
adcs x7, x9, x17
adc x21, x3, x10
stp x13, x4, [x0, #128]
stp x7, x21, [x0, #144]
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
.globl lab_sc_o1_21_30_1
lab_sc_o1_21_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
ldr x11, [x0, #336]
umulh x4, x3, x12
mul x8, x3, x24
umulh x2, x3, x24
mul x13, x3, x9
umulh x17, x3, x25
mul x14, x7, x9
umulh x1, x3, x9
mul x6, x3, x25
mul x20, x7, x25
mul x22, x7, x12
umulh x16, x7, x12
umulh x23, x7, x9
mul x15, x7, x24
umulh x21, x7, x24
umulh x5, x7, x25
mul x28, x3, x12
adds x7, x13, x4
adcs x3, x6, x1
adcs x13, x8, x17
adc x4, x2, x10
mul x6, x11, x12
mul x1, x11, x24
mul x8, x11, x9
adds x17, x7, x22
adcs x2, x3, x14
adcs x22, x13, x20
adcs x7, x4, x15
adc x3, x10, x10
mul x14, x11, x25
umulh x13, x11, x12
umulh x20, x11, x24
adds x4, x2, x16
adcs x15, x22, x23
adcs x2, x7, x5
adc x16, x3, x21
umulh x22, x11, x25
umulh x23, x11, x9
ldr x7, [x0, #344]
adds x5, x4, x6
adcs x21, x15, x8
adcs x3, x2, x14
adcs x11, x16, x1
adc x4, x10, x10
mul x6, x7, x12
umulh x15, x7, x12
mul x8, x7, x9
umulh x14, x7, x9
mul x2, x7, x24
umulh x1, x7, x24
mul x16, x7, x25
umulh x12, x7, x25
adds x9, x21, x13
adcs x24, x3, x23
adcs x25, x11, x22
adc x7, x4, x20
adds x21, x9, x6
adcs x13, x24, x8
adcs x23, x25, x16
adcs x3, x7, x2
adc x22, x10, x10
ldp x11, x20, [x0, #272]
ldp x4, x6, [x0, #256]
ldr x9, [x0, #288]
adds x8, x13, x15
adcs x24, x23, x14
adcs x16, x3, x12
adc x25, x22, x1
mul x2, x9, x20
mul x7, x9, x6
mul x15, x9, x11
mul x13, x9, x4
umulh x14, x27, x25
mul x23, x27, x25
mul x12, x27, x8
umulh x3, x9, x4
mul x22, x27, x24
umulh x1, x27, x24
umulh x25, x27, x8
mul x24, x27, x16
umulh x8, x27, x16
adds x16, x28, x12
adcs x12, x17, x22
adcs x28, x5, x24
adcs x17, x21, x23
adc x22, x14, x10
umulh x5, x9, x11
umulh x24, x9, x20
umulh x23, x9, x6
ldr x21, [x0, #296]
adds x14, x7, x3
adcs x9, x15, x23
adcs x3, x2, x5
adc x7, x24, x10
adds x23, x17, x8
adc x15, x22, x10
mul x5, x21, x6
mul x2, x21, x11
mul x24, x21, x4
mul x17, x21, x20
extr x8, x15, x23, #63
and x22, x23, #0x7fffffffffffffff
mul x15, x8, x26
adds x23, x14, x24
adcs x8, x9, x5
adcs x24, x3, x2
adcs x14, x7, x17
adc x5, x10, x10
adds x9, x16, x15
adcs x2, x12, x25
adcs x3, x28, x1
adc x17, x22, x10
umulh x7, x21, x20
umulh x16, x21, x11
umulh x15, x21, x4
umulh x12, x21, x6
stp x9, x2, [x0, #448]
stp x3, x17, [x0, #464]
ldr x25, [x0, #304]
adds x28, x8, x15
adcs x1, x24, x12
adcs x22, x14, x16
adc x21, x5, x7
ldr x9, [x0, #312]
mul x2, x25, x4
mul x3, x25, x11
mul x17, x25, x20
mul x15, x25, x6
umulh x8, x25, x11
umulh x12, x25, x20
umulh x24, x25, x4
umulh x14, x25, x6
mul x16, x9, x20
umulh x5, x9, x20
mul x7, x9, x4
adds x25, x28, x2
adcs x20, x1, x15
adcs x2, x22, x3
adcs x28, x21, x17
adc x15, x10, x10
umulh x1, x9, x4
umulh x22, x9, x6
mul x3, x9, x6
mul x21, x9, x11
umulh x17, x9, x11
adds x4, x20, x24
adcs x6, x2, x14
adcs x11, x28, x8
adc x9, x15, x12
adds x20, x4, x7
adcs x24, x6, x3
adcs x2, x11, x21
adcs x14, x9, x16
adc x28, x10, x10
ldp x8, x15, [x0, #224]
ldp x12, x4, [x0, #240]
adds x7, x24, x1
adcs x6, x2, x22
adcs x3, x14, x17
adc x11, x28, x5
mul x21, x8, x12
mul x16, x8, x4
umulh x9, x8, x15
umulh x24, x8, x12
mul x1, x8, x15
umulh x2, x27, x11
mul x22, x27, x11
mul x17, x27, x3
umulh x14, x27, x3
mul x5, x27, x6
umulh x28, x27, x6
mul x11, x27, x7
umulh x3, x27, x7
adds x6, x13, x11
adcs x7, x23, x5
adcs x13, x25, x17
adcs x11, x20, x22
adc x23, x2, x10
umulh x5, x8, x4
umulh x17, x15, x4
mul x25, x15, x4
mul x20, x15, x12
adds x22, x21, x9
adcs x2, x16, x24
adc x21, x5, x10
adds x9, x11, x14
adc x16, x23, x10
umulh x24, x15, x12
umulh x5, x12, x4
mul x11, x12, x4
extr x14, x16, x9, #63
adds x23, x2, x20
adcs x16, x21, x25
adc x2, x17, x10
mul x20, x14, x26
and x21, x9, #0x7fffffffffffffff
adds x25, x6, x20
adcs x17, x7, x3
adcs x14, x13, x28
adc x9, x21, x10
adds x6, x16, x24
adcs x20, x2, x11
adc x3, x5, x10
extr x7, x23, x22, #63
extr x13, x22, x1, #63
lsr x28, x3, #63
extr x21, x6, x23, #63
extr x16, x20, x6, #63
extr x24, x3, x20, #63
stp x14, x9, [x0, #496]
stp x25, x17, [x0, #480]
umulh x2, x4, x4
umulh x11, x15, x15
mul x5, x4, x4
mul x22, x15, x15
mul x23, x12, x12
umulh x6, x12, x12
umulh x20, x8, x8
lsl x3, x1, #1
mul x14, x8, x8
adds x9, x3, x20
adcs x25, x13, x22
adcs x17, x7, x11
adcs x4, x21, x23
adcs x15, x16, x6
adcs x12, x24, x5
adc x1, x28, x2
ldp x8, x3, [x0, #272]
ldp x20, x13, [x0, #256]
umulh x22, x20, x13
umulh x7, x20, x8
mul x11, x20, x8
mul x21, x20, x3
mul x23, x20, x13
mul x6, x27, x4
umulh x16, x20, x3
umulh x5, x27, x4
mul x24, x27, x15
mul x2, x13, x8
umulh x28, x27, x15
mul x4, x27, x12
umulh x15, x27, x12
mul x12, x27, x1
umulh x1, x27, x1
adds x6, x14, x6
adcs x14, x9, x24
adcs x9, x25, x4
adcs x24, x17, x12
adc x4, x1, x10
adds x25, x11, x22
adcs x12, x21, x7
adc x17, x16, x10
mul x1, x13, x3
umulh x22, x13, x3
mul x11, x8, x3
umulh x7, x13, x8
adds x21, x24, x15
adc x16, x4, x10
adds x15, x12, x2
adcs x24, x17, x1
adc x4, x22, x10
umulh x12, x8, x3
extr x2, x16, x21, #63
and x17, x21, #0x7fffffffffffffff
mul x1, x2, x26
adds x22, x24, x7
adcs x16, x4, x11
adc x21, x12, x10
adds x2, x6, x1
adcs x7, x14, x5
adcs x24, x9, x28
adc x4, x17, x10
extr x11, x15, x25, #63
extr x12, x25, x23, #63
lsr x6, x21, #63
extr x1, x22, x15, #63
extr x14, x16, x22, #63
extr x5, x21, x16, #63
stp x2, x7, [x0, #352]
lsl x28, x23, #1
stp x24, x4, [x0, #368]
umulh x9, x13, x13
umulh x17, x20, x20
mul x25, x8, x8
mul x15, x13, x13
mul x22, x3, x3
umulh x16, x8, x8
umulh x21, x3, x3
mul x2, x20, x20
adds x7, x28, x17
adcs x23, x12, x15
adcs x4, x11, x9
adcs x24, x1, x25
adcs x13, x14, x16
adcs x8, x5, x22
adc x3, x6, x21
ldp x20, x28, [x0, #480]
ldp x17, x15, [x0, #464]
ldp x12, x9, [x0, #448]
ldp x11, x25, [x0, #496]
subs x1, x12, x20
sbcs x14, x9, x28
sbcs x16, x17, x11
sbcs x5, x15, x25
csel x22, x10, x27, hs
mul x21, x27, x13
mul x6, x27, x3
mul x20, x27, x8
umulh x12, x27, x3
umulh x28, x27, x8
umulh x9, x27, x13
mul x17, x27, x24
umulh x11, x27, x24
adds x15, x2, x17
adcs x25, x7, x21
adcs x3, x23, x20
adcs x8, x4, x6
adc x13, x12, x10
subs x24, x1, x22
sbcs x17, x14, x10
sbcs x2, x16, x10
sbc x7, x5, x10
adds x21, x8, x28
adc x23, x13, x10
umulh x20, x24, x2
mul x6, x24, x2
umulh x4, x24, x7
umulh x12, x24, x17
mul x22, x24, x7
mul x1, x17, x7
extr x14, x23, x21, #63
and x16, x21, #0x7fffffffffffffff
umulh x5, x17, x7
mul x8, x17, x2
mul x28, x14, x26
umulh x13, x2, x7
umulh x23, x17, x2
adds x21, x15, x28
adcs x14, x25, x11
adcs x15, x3, x9
adc x28, x16, x10
adds x25, x6, x12
adcs x11, x22, x20
adc x3, x4, x10
mul x9, x2, x7
mul x16, x24, x17
stp x21, x14, [x0, #384]
stp x15, x28, [x0, #400]
adds x6, x11, x8
adcs x12, x3, x1
adc x22, x5, x10
umulh x20, x7, x7
mul x4, x7, x7
mul x21, x17, x17
umulh x14, x17, x17
umulh x15, x24, x24
mul x28, x2, x2
umulh x11, x2, x2
mul x8, x24, x24
extr x3, x25, x16, #63
adds x1, x12, x23
adcs x5, x22, x9
adc x7, x13, x10
extr x17, x6, x25, #63
lsl x2, x16, #1
lsr x24, x7, #63
extr x23, x7, x5, #63
extr x12, x5, x1, #63
extr x22, x1, x6, #63
adds x9, x2, x15
adcs x13, x3, x21
adcs x25, x17, x14
adcs x16, x22, x28
adcs x7, x12, x11
adcs x5, x23, x4
adc x1, x24, x20
ldp x6, x2, [x0, #464]
ldp x15, x3, [x0, #448]
ldp x21, x17, [x0, #480]
ldp x14, x28, [x0, #496]
adds x22, x15, x21
adcs x11, x3, x17
adcs x12, x6, x14
adcs x4, x2, x28
csel x23, x27, x10, hs
mul x20, x27, x1
mul x24, x27, x5
umulh x15, x27, x1
mul x21, x27, x7
umulh x3, x27, x5
umulh x17, x27, x7
mul x6, x27, x16
umulh x14, x27, x16
adds x2, x8, x6
adcs x28, x9, x21
adcs x1, x13, x24
adcs x5, x25, x20
adc x7, x15, x10
adds x16, x22, x23
adcs x6, x11, x10
adc x8, x12, x10
umulh x9, x16, x6
mul x21, x16, x8
umulh x24, x16, x4
adds x13, x5, x3
adc x20, x7, x10
umulh x25, x16, x8
mul x15, x16, x4
mul x22, x6, x8
umulh x23, x6, x4
mul x11, x6, x4
mul x12, x16, x6
extr x3, x20, x13, #63
and x5, x13, #0x7fffffffffffffff
umulh x7, x8, x4
mul x20, x3, x26
adds x13, x21, x9
adcs x3, x15, x25
adc x21, x24, x10
umulh x9, x6, x8
mul x15, x8, x4
adds x25, x2, x20
adcs x24, x28, x14
adcs x2, x1, x17
adc x20, x5, x10
adds x28, x3, x22
adcs x14, x21, x11
adc x1, x23, x10
stp x25, x24, [x0, #192]
stp x2, x20, [x0, #208]
umulh x17, x16, x16
mul x5, x8, x8
umulh x3, x8, x8
adds x22, x14, x9
adcs x21, x1, x15
adc x11, x7, x10
umulh x23, x6, x6
lsl x25, x12, #1
extr x24, x13, x12, #63
mul x2, x4, x4
umulh x20, x4, x4
mul x8, x6, x6
extr x14, x28, x13, #63
mul x9, x16, x16
lsr x1, x11, #63
extr x15, x22, x28, #63
extr x7, x11, x21, #63
extr x12, x21, x22, #63
adds x4, x25, x17
adcs x6, x24, x8
adcs x13, x14, x23
adcs x16, x15, x5
adcs x28, x12, x3
adcs x11, x7, x2
adc x22, x1, x20
ldp x21, x25, [x0, #192]
ldp x17, x24, [x0, #208]
ldr x8, [x0, #64]
mul x14, x8, x25
mul x23, x8, x17
mul x15, x8, x24
umulh x5, x27, x22
mul x3, x27, x22
mul x12, x27, x16
umulh x2, x8, x21
umulh x7, x27, x16
mul x20, x27, x11
umulh x1, x27, x11
mul x22, x27, x28
umulh x16, x27, x28
adds x11, x9, x12
adcs x28, x4, x22
adcs x12, x6, x20
adcs x9, x13, x3
adc x4, x5, x10
umulh x22, x8, x25
umulh x20, x8, x17
umulh x6, x8, x24
ldr x13, [x0, #72]
mul x3, x8, x21
adds x5, x14, x2
adcs x8, x23, x22
adcs x2, x15, x20
adc x14, x6, x10
adds x23, x9, x1
adc x22, x4, x10
mul x15, x13, x25
mul x20, x13, x24
mul x6, x13, x17
mul x1, x13, x21
extr x9, x22, x23, #63
and x4, x23, #0x7fffffffffffffff
mul x22, x9, x26
adds x23, x5, x1
adcs x9, x8, x15
adcs x1, x2, x6
adcs x5, x14, x20
adc x15, x10, x10
adds x8, x11, x22
adcs x2, x28, x7
adcs x6, x12, x16
adc x14, x4, x10
umulh x20, x13, x21
umulh x11, x13, x24
umulh x22, x13, x25
umulh x28, x13, x17
stp x8, x2, [x0, #160]
stp x6, x14, [x0, #176]
ldr x7, [x0, #80]
adds x16, x9, x20
adcs x12, x1, x22
adcs x4, x5, x28
adc x13, x15, x11
ldr x8, [x0, #88]
mul x2, x7, x21
mul x14, x7, x25
mul x6, x7, x17
umulh x9, x7, x24
umulh x20, x7, x25
mul x1, x7, x24
umulh x22, x7, x21
umulh x5, x7, x17
mul x28, x8, x21
umulh x15, x8, x21
mul x11, x8, x25
umulh x7, x8, x25
adds x21, x16, x2
adcs x25, x12, x14
adcs x16, x4, x6
adcs x2, x13, x1
adc x12, x10, x10
mul x14, x8, x24
umulh x4, x8, x24
mul x6, x8, x17
umulh x1, x8, x17
adds x13, x25, x22
adcs x24, x16, x20
adcs x17, x2, x5
adc x8, x12, x9
adds x25, x13, x28
adcs x22, x24, x11
adcs x16, x17, x6
adcs x20, x8, x14
adc x5, x10, x10
ldp x2, x9, [x0, #352]
ldp x12, x13, [x0, #384]
ldp x28, x11, [x0, #368]
adds x24, x22, x15
adcs x6, x16, x7
adcs x17, x20, x1
adc x14, x5, x4
ldp x8, x15, [x0, #400]
umulh x22, x27, x14
mul x7, x27, x14
mul x16, x27, x17
umulh x1, x27, x17
subs x20, x2, x12
sbcs x4, x9, x13
sbcs x5, x28, x8
sbcs x14, x11, x15
csel x17, x10, x27, hs
mul x12, x27, x6
umulh x2, x27, x6
mul x13, x27, x24
umulh x9, x27, x24
adds x28, x3, x13
adcs x8, x23, x12
adcs x11, x21, x16
adcs x15, x25, x7
adc x6, x22, x10
subs x24, x20, x17
sbcs x13, x4, x10
sbcs x3, x5, x10
sbc x12, x14, x10
ldp x23, x21, [x0, #384]
ldr x16, [x0, #352]
ldp x7, x25, [x0, #400]
adds x22, x15, x1
adc x17, x6, x10
stp x3, x12, [x0, #432]
stp x24, x13, [x0, #416]
mul x20, x16, x21
mul x4, x16, x25
mul x5, x16, x7
mul x14, x16, x23
extr x15, x17, x22, #63
umulh x1, x16, x23
and x6, x22, #0x7fffffffffffffff
umulh x3, x16, x21
mul x12, x15, x26
umulh x24, x16, x7
adds x13, x28, x12
adcs x17, x8, x9
adcs x22, x11, x2
adc x15, x6, x10
umulh x28, x16, x25
adds x12, x20, x1
adcs x8, x5, x3
adcs x9, x4, x24
adc x11, x28, x10
stp x22, x15, [x0, #208]
stp x13, x17, [x0, #192]
ldr x2, [x0, #360]
ldr x6, [x0, #368]
mul x16, x2, x23
mul x1, x2, x21
mul x20, x2, x25
mul x3, x2, x7
umulh x5, x2, x21
umulh x24, x2, x23
umulh x4, x2, x25
umulh x28, x2, x7
mul x22, x6, x25
mul x15, x6, x7
mul x13, x6, x23
adds x17, x12, x16
adcs x2, x8, x1
adcs x16, x9, x3
adcs x12, x11, x20
adc x1, x10, x10
mul x8, x6, x21
ldr x3, [x0, #376]
umulh x9, x6, x23
adds x20, x2, x24
adcs x11, x16, x5
adcs x24, x12, x28
adc x2, x1, x4
umulh x5, x6, x21
umulh x16, x6, x25
umulh x12, x6, x7
mul x28, x3, x7
umulh x1, x3, x7
umulh x4, x3, x21
mul x6, x3, x21
adds x7, x20, x13
adcs x21, x11, x8
adcs x13, x24, x15
adcs x20, x2, x22
adc x8, x10, x10
umulh x11, x3, x23
mul x24, x3, x23
mul x15, x3, x25
umulh x2, x3, x25
adds x22, x21, x9
adcs x23, x13, x5
adcs x25, x20, x12
adc x3, x8, x16
adds x21, x22, x24
adcs x9, x23, x6
adcs x13, x25, x28
adcs x5, x3, x15
adc x20, x10, x10
ldp x12, x8, [x0, #416]
ldp x16, x22, [x0, #368]
ldp x24, x23, [x0, #352]
adds x6, x9, x11
adcs x25, x13, x4
adcs x28, x5, x1
adc x15, x20, x2
ldp x3, x9, [x0, #432]
movz x11, #56129, lsl #0
movk x11, #1, lsl #16
mul x13, x12, x11
umulh x4, x27, x15
mul x1, x27, x15
mul x5, x27, x25
umulh x2, x27, x25
umulh x20, x27, x28
mul x15, x27, x28
mul x25, x27, x6
umulh x28, x27, x6
adds x6, x14, x25
adcs x14, x17, x5
adcs x25, x7, x15
adcs x17, x21, x1
adc x5, x4, x10
umulh x15, x12, x11
umulh x7, x9, x11
mul x21, x9, x11
mul x1, x3, x11
umulh x4, x3, x11
mul x12, x8, x11
umulh x9, x8, x11
adds x3, x24, x13
adcs x8, x23, x12
adcs x11, x16, x1
adcs x24, x22, x21
adc x13, x7, x10
adds x23, x17, x20
adc x12, x5, x10
extr x1, x12, x23, #63
and x16, x23, #0x7fffffffffffffff
mul x21, x1, x26
adds x22, x24, x24
adc x7, x13, x13
adds x17, x6, x21
adcs x20, x14, x28
adcs x5, x25, x2
adc x12, x16, x10
mul x23, x7, x26
lsr x1, x22, #1
adds x24, x3, x23
adcs x13, x8, x15
adcs x6, x11, x9
adc x21, x1, x4
stp x5, x12, [x0, #112]
stp x17, x20, [x0, #96]
ldr x28, [x0, #416]
ldr x14, [x0, #424]
stp x24, x13, [x0, #128]
stp x6, x21, [x0, #144]
ldp x25, x2, [x0, #128]
ldp x16, x7, [x0, #144]
ldr x22, [x0, #432]
umulh x3, x28, x25
umulh x23, x28, x16
mul x15, x28, x7
umulh x8, x28, x2
mul x9, x28, x16
umulh x11, x28, x7
mul x4, x14, x2
mul x1, x28, x2
mul x5, x14, x25
mul x12, x14, x16
mul x17, x14, x7
umulh x20, x14, x25
umulh x13, x14, x7
umulh x24, x14, x2
umulh x6, x14, x16
mul x21, x28, x25
adds x14, x1, x3
adcs x28, x9, x8
adcs x1, x15, x23
adc x3, x11, x10
mul x9, x22, x7
mul x8, x22, x25
mul x15, x22, x16
adds x23, x14, x5
adcs x11, x28, x4
adcs x14, x1, x12
adcs x5, x3, x17
adc x28, x10, x10
mul x4, x22, x2
umulh x1, x22, x2
umulh x12, x22, x7
adds x17, x11, x20
adcs x3, x14, x24
adcs x11, x5, x6
adc x20, x28, x13
umulh x14, x22, x16
umulh x24, x22, x25
ldr x6, [x0, #440]
adds x5, x17, x8
adcs x13, x3, x4
adcs x28, x11, x15
adcs x22, x20, x9
adc x17, x10, x10
mul x8, x6, x25
umulh x4, x6, x25
mul x3, x6, x16
umulh x15, x6, x16
mul x11, x6, x7
umulh x9, x6, x7
mul x20, x6, x2
umulh x25, x6, x2
adds x16, x13, x24
adcs x7, x28, x1
adcs x6, x22, x14
adc x2, x17, x12
adds x24, x16, x8
adcs x13, x7, x20
adcs x1, x6, x3
adcs x28, x2, x11
adc x14, x10, x10
adds x22, x13, x4
adcs x12, x1, x25
adcs x17, x28, x15
adc x8, x14, x9
umulh x16, x27, x8
mul x20, x27, x12
mul x7, x27, x22
mul x3, x27, x17
mul x6, x27, x8
umulh x11, x27, x17
umulh x2, x27, x22
umulh x4, x27, x12
adds x13, x21, x7
adcs x25, x23, x20
adcs x1, x5, x3
adcs x28, x24, x6
adc x15, x16, x10
adds x14, x28, x11
adc x9, x15, x10
extr x8, x9, x14, #63
and x17, x14, #0x7fffffffffffffff
mul x22, x8, x26
adds x12, x13, x22
adcs x21, x25, x2
adcs x7, x1, x4
adc x23, x17, x10
stp x12, x21, [x0, #128]
stp x7, x23, [x0, #144]
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
.globl lab_sc_o1_21_15_0
lab_sc_o1_21_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
ldr x17, [x0, #320]
ldr x1, [x0, #328]
umulh x12, x17, x9
umulh x14, x17, x7
umulh x20, x17, x16
umulh x13, x17, x21
mul x4, x17, x7
mul x22, x17, x16
mul x6, x17, x21
mul x2, x1, x9
mul x11, x1, x7
mul x15, x1, x16
mul x8, x17, x9
mul x28, x1, x21
umulh x23, x1, x9
umulh x25, x1, x7
adds x24, x4, x12
adcs x3, x22, x14
adcs x5, x6, x20
adc x17, x13, x10
umulh x4, x1, x16
umulh x12, x1, x21
ldr x22, [x0, #336]
adds x14, x24, x2
adcs x6, x3, x11
adcs x20, x5, x15
adcs x13, x17, x28
adc x1, x10, x10
mul x2, x22, x9
mul x24, x22, x7
mul x3, x22, x16
mul x11, x22, x21
umulh x5, x22, x9
umulh x15, x22, x7
adds x17, x6, x23
adcs x28, x20, x25
adcs x6, x13, x4
adc x23, x1, x12
umulh x20, x22, x16
umulh x25, x22, x21
ldr x13, [x0, #344]
adds x4, x17, x2
adcs x12, x28, x24
adcs x1, x6, x3
adcs x22, x23, x11
adc x17, x10, x10
mul x2, x13, x9
umulh x28, x13, x9
mul x24, x13, x7
umulh x3, x13, x7
mul x6, x13, x16
mul x11, x13, x21
adds x23, x12, x5
adcs x9, x1, x15
adcs x7, x22, x20
adc x12, x17, x25
umulh x5, x13, x16
umulh x15, x13, x21
adds x1, x23, x2
adcs x20, x9, x24
adcs x22, x7, x6
adcs x25, x12, x11
adc x17, x10, x10
adds x16, x20, x28
adcs x21, x22, x3
adcs x13, x25, x5
adc x2, x17, x15
umulh x23, x27, x2
mul x24, x27, x16
mul x9, x27, x21
mul x6, x27, x13
mul x7, x27, x2
umulh x11, x27, x13
umulh x12, x27, x16
umulh x28, x27, x21
adds x20, x8, x24
adcs x3, x14, x9
adcs x22, x4, x6
adcs x5, x1, x7
adc x25, x23, x10
ldp x17, x15, [x0, #256]
ldp x2, x13, [x0, #272]
ldr x16, [x0, #288]
adds x21, x5, x11
adc x24, x25, x10
mul x8, x16, x15
mul x14, x16, x2
mul x9, x16, x13
mul x4, x16, x17
extr x6, x24, x21, #63
umulh x7, x16, x17
and x1, x21, #0x7fffffffffffffff
umulh x23, x16, x15
mul x5, x6, x26
umulh x11, x16, x2
adds x25, x20, x5
adcs x24, x3, x12
adcs x21, x22, x28
adc x6, x1, x10
umulh x20, x16, x13
adds x5, x8, x7
adcs x3, x14, x23
adcs x12, x9, x11
adc x22, x20, x10
stp x25, x24, [x0, #448]
stp x21, x6, [x0, #464]
ldr x28, [x0, #296]
mul x1, x28, x17
mul x16, x28, x15
mul x7, x28, x2
mul x8, x28, x13
umulh x23, x28, x17
umulh x14, x28, x15
umulh x11, x28, x2
umulh x9, x28, x13
ldr x20, [x0, #304]
adds x25, x5, x1
adcs x24, x3, x16
adcs x21, x12, x7
adcs x6, x22, x8
adc x28, x10, x10
mul x1, x20, x17
mul x5, x20, x15
mul x16, x20, x2
mul x3, x20, x13
umulh x7, x20, x17
umulh x12, x20, x15
adds x8, x24, x23
adcs x22, x21, x14
adcs x23, x6, x11
adc x24, x28, x9
umulh x14, x20, x2
umulh x21, x20, x13
ldr x6, [x0, #312]
adds x11, x8, x1
adcs x28, x22, x5
adcs x9, x23, x16
adcs x20, x24, x3
adc x1, x10, x10
mul x8, x6, x17
umulh x5, x6, x17
mul x22, x6, x15
umulh x23, x6, x15
mul x16, x6, x2
mul x24, x6, x13
adds x3, x28, x7
adcs x17, x9, x12
adcs x15, x20, x14
adc x28, x1, x21
umulh x7, x6, x2
umulh x9, x6, x13
adds x12, x3, x8
adcs x20, x17, x22
adcs x14, x15, x16
adcs x1, x28, x24
adc x21, x10, x10
adds x2, x20, x5
adcs x13, x14, x23
adcs x6, x1, x7
adc x3, x21, x9
umulh x8, x27, x3
mul x17, x27, x2
mul x22, x27, x13
mul x15, x27, x6
mul x16, x27, x3
umulh x24, x27, x6
umulh x28, x27, x2
umulh x20, x27, x13
adds x5, x4, x17
adcs x14, x25, x22
adcs x23, x11, x15
adcs x7, x12, x16
adc x1, x8, x10
ldp x9, x21, [x0, #224]
ldp x3, x6, [x0, #240]
adds x2, x7, x24
adc x13, x1, x10
umulh x4, x9, x21
umulh x17, x9, x3
mul x25, x9, x3
mul x22, x9, x6
mul x15, x9, x21
extr x11, x13, x2, #63
umulh x12, x9, x6
and x16, x2, #0x7fffffffffffffff
mul x8, x21, x3
mul x7, x11, x26
mul x24, x21, x6
adds x1, x5, x7
adcs x13, x14, x28
adcs x2, x23, x20
adc x11, x16, x10
umulh x5, x21, x6
umulh x7, x21, x3
umulh x28, x3, x6
mul x14, x3, x6
stp x1, x13, [x0, #480]
adds x23, x25, x4
adcs x20, x22, x17
adc x16, x12, x10
stp x2, x11, [x0, #496]
umulh x1, x9, x9
mul x13, x21, x21
mul x25, x9, x9
lsl x4, x15, #1
adds x22, x20, x8
adcs x17, x16, x24
adc x12, x5, x10
umulh x2, x21, x21
umulh x11, x3, x3
mul x9, x3, x3
extr x20, x23, x15, #63
adds x8, x17, x7
adcs x16, x12, x14
adc x24, x28, x10
umulh x5, x6, x6
mul x21, x6, x6
extr x3, x22, x23, #63
lsr x15, x24, #63
extr x17, x24, x16, #63
extr x7, x16, x8, #63
extr x12, x8, x22, #63
adds x14, x4, x1
adcs x28, x20, x13
adcs x6, x3, x2
adcs x23, x12, x9
adcs x24, x7, x11
adcs x16, x17, x21
adc x8, x15, x5
umulh x22, x27, x8
mul x4, x27, x23
mul x1, x27, x24
mul x20, x27, x16
mul x13, x27, x8
umulh x3, x27, x16
umulh x2, x27, x23
umulh x12, x27, x24
adds x9, x25, x4
adcs x11, x14, x1
adcs x7, x28, x20
adcs x21, x6, x13
adc x17, x22, x10
ldp x5, x15, [x0, #256]
ldp x8, x16, [x0, #272]
adds x23, x21, x3
adc x24, x17, x10
umulh x4, x5, x15
umulh x25, x5, x8
mul x14, x5, x8
mul x1, x5, x16
mul x20, x5, x15
extr x28, x24, x23, #63
umulh x13, x5, x16
and x6, x23, #0x7fffffffffffffff
mul x22, x15, x8
mul x3, x28, x26
mul x21, x15, x16
adds x17, x9, x3
adcs x24, x11, x2
adcs x23, x7, x12
adc x28, x6, x10
umulh x9, x15, x16
umulh x3, x15, x8
umulh x11, x8, x16
mul x2, x8, x16
stp x17, x24, [x0, #352]
adds x12, x14, x4
adcs x7, x1, x25
adc x6, x13, x10
stp x23, x28, [x0, #368]
umulh x17, x5, x5
mul x24, x15, x15
mul x4, x5, x5
lsl x14, x20, #1
adds x25, x7, x22
adcs x1, x6, x21
adc x13, x9, x10
umulh x28, x15, x15
umulh x23, x8, x8
mul x5, x8, x8
extr x7, x12, x20, #63
adds x22, x1, x3
adcs x6, x13, x2
adc x21, x11, x10
umulh x9, x16, x16
mul x15, x16, x16
extr x8, x25, x12, #63
lsr x20, x21, #63
extr x3, x21, x6, #63
extr x1, x6, x22, #63
extr x13, x22, x25, #63
adds x2, x14, x17
adcs x11, x7, x24
adcs x16, x8, x28
adcs x12, x13, x5
adcs x21, x1, x23
adcs x6, x3, x15
adc x25, x20, x9
umulh x22, x27, x25
mul x14, x27, x12
mul x17, x27, x21
mul x24, x27, x6
mul x7, x27, x25
umulh x28, x27, x6
umulh x8, x27, x12
umulh x5, x27, x21
adds x13, x4, x14
adcs x1, x2, x17
adcs x23, x11, x24
adcs x3, x16, x7
adc x15, x22, x10
ldp x9, x20, [x0, #448]
ldp x25, x6, [x0, #464]
ldp x12, x21, [x0, #480]
ldp x14, x4, [x0, #496]
adds x2, x3, x28
adc x17, x15, x10
subs x11, x9, x12
sbcs x24, x20, x21
sbcs x7, x25, x14
sbcs x16, x6, x4
csel x22, x10, x27, hs
extr x3, x17, x2, #63
and x28, x2, #0x7fffffffffffffff
mul x15, x3, x26
adds x12, x13, x15
adcs x9, x1, x8
adcs x21, x23, x5
adc x20, x28, x10
subs x25, x11, x22
sbcs x14, x24, x10
sbcs x6, x7, x10
sbc x4, x16, x10
stp x12, x9, [x0, #384]
stp x21, x20, [x0, #400]
umulh x17, x25, x14
umulh x2, x25, x6
umulh x3, x25, x4
mul x13, x25, x6
mul x15, x25, x4
umulh x1, x14, x4
mul x8, x14, x6
mul x23, x14, x4
umulh x5, x14, x6
umulh x28, x6, x4
mul x22, x6, x4
mul x11, x25, x14
adds x24, x13, x17
adcs x7, x15, x2
adc x16, x3, x10
umulh x12, x25, x25
mul x9, x14, x14
mul x21, x25, x25
lsl x20, x11, #1
adds x13, x7, x8
adcs x17, x16, x23
adc x15, x1, x10
umulh x2, x14, x14
umulh x3, x6, x6
mul x25, x6, x6
extr x7, x24, x11, #63
adds x8, x17, x5
adcs x16, x15, x22
adc x23, x28, x10
umulh x1, x4, x4
mul x14, x4, x4
extr x6, x13, x24, #63
lsr x11, x23, #63
extr x5, x23, x16, #63
extr x17, x16, x8, #63
extr x15, x8, x13, #63
adds x22, x20, x12
adcs x28, x7, x9
adcs x4, x6, x2
adcs x24, x15, x25
adcs x23, x17, x3
adcs x16, x5, x14
adc x8, x11, x1
umulh x13, x27, x8
mul x20, x27, x24
mul x12, x27, x23
mul x7, x27, x16
mul x9, x27, x8
umulh x6, x27, x16
umulh x2, x27, x24
umulh x25, x27, x23
adds x15, x21, x20
adcs x3, x22, x12
adcs x17, x28, x7
adcs x14, x4, x9
adc x5, x13, x10
ldp x1, x11, [x0, #448]
ldp x8, x16, [x0, #464]
ldp x24, x23, [x0, #480]
ldp x20, x21, [x0, #496]
adds x22, x14, x6
adc x12, x5, x10
adds x7, x1, x24
adcs x28, x11, x23
adcs x9, x8, x20
adcs x4, x16, x21
csel x13, x27, x10, hs
extr x6, x12, x22, #63
and x14, x22, #0x7fffffffffffffff
mul x5, x6, x26
adds x1, x15, x5
adcs x24, x3, x2
adcs x11, x17, x25
adc x23, x14, x10
adds x8, x7, x13
adcs x20, x28, x10
adc x16, x9, x10
stp x1, x24, [x0, #192]
stp x11, x23, [x0, #208]
umulh x21, x8, x20
umulh x12, x8, x16
umulh x22, x8, x4
mul x6, x8, x16
mul x15, x8, x4
umulh x5, x20, x4
mul x3, x20, x16
mul x2, x20, x4
umulh x17, x20, x16
umulh x25, x16, x4
mul x14, x16, x4
mul x7, x8, x20
adds x13, x6, x21
adcs x28, x15, x12
adc x9, x22, x10
umulh x1, x8, x8
mul x24, x20, x20
mul x11, x8, x8
lsl x23, x7, #1
adds x6, x28, x3
adcs x21, x9, x2
adc x15, x5, x10
umulh x12, x20, x20
umulh x22, x16, x16
mul x8, x16, x16
extr x28, x13, x7, #63
adds x3, x21, x17
adcs x9, x15, x14
adc x2, x25, x10
umulh x5, x4, x4
mul x20, x4, x4
extr x16, x6, x13, #63
lsr x7, x2, #63
extr x21, x2, x9, #63
extr x17, x9, x3, #63
extr x15, x3, x6, #63
adds x14, x23, x1
adcs x25, x28, x24
adcs x4, x16, x12
adcs x13, x15, x8
adcs x2, x17, x22
adcs x9, x21, x20
adc x3, x7, x5
umulh x6, x27, x3
mul x23, x27, x13
mul x1, x27, x2
mul x28, x27, x9
mul x24, x27, x3
umulh x16, x27, x9
umulh x12, x27, x13
umulh x15, x27, x2
adds x8, x11, x23
adcs x22, x14, x1
adcs x17, x25, x28
adcs x20, x4, x24
adc x21, x6, x10
ldp x5, x7, [x0, #192]
ldp x3, x9, [x0, #208]
ldr x13, [x0, #64]
adds x2, x20, x16
adc x23, x21, x10
mul x11, x13, x7
mul x14, x13, x3
mul x1, x13, x9
mul x28, x13, x5
extr x25, x23, x2, #63
umulh x4, x13, x5
and x24, x2, #0x7fffffffffffffff
umulh x6, x13, x7
mul x16, x25, x26
umulh x20, x13, x3
adds x21, x8, x16
adcs x23, x22, x12
adcs x2, x17, x15
adc x25, x24, x10
umulh x8, x13, x9
adds x16, x11, x4
adcs x22, x14, x6
adcs x12, x1, x20
adc x15, x8, x10
stp x21, x23, [x0, #160]
stp x2, x25, [x0, #176]
ldr x17, [x0, #72]
mul x24, x17, x5
mul x13, x17, x7
mul x4, x17, x3
mul x11, x17, x9
umulh x14, x17, x5
umulh x6, x17, x7
umulh x1, x17, x3
umulh x20, x17, x9
ldr x8, [x0, #80]
adds x21, x16, x24
adcs x23, x22, x13
adcs x25, x12, x4
adcs x2, x15, x11
adc x17, x10, x10
mul x24, x8, x5
mul x16, x8, x7
mul x13, x8, x3
mul x22, x8, x9
umulh x12, x8, x5
umulh x4, x8, x7
adds x15, x23, x14
adcs x11, x25, x6
adcs x23, x2, x1
adc x14, x17, x20
umulh x25, x8, x3
umulh x6, x8, x9
ldr x2, [x0, #88]
adds x1, x15, x24
adcs x17, x11, x16
adcs x20, x23, x13
adcs x8, x14, x22
adc x15, x10, x10
mul x24, x2, x5
umulh x11, x2, x5
mul x16, x2, x7
umulh x23, x2, x7
mul x13, x2, x3
mul x22, x2, x9
adds x14, x17, x12
adcs x5, x20, x4
adcs x7, x8, x25
adc x17, x15, x6
umulh x12, x2, x3
umulh x20, x2, x9
adds x4, x14, x24
adcs x25, x5, x16
adcs x8, x7, x13
adcs x6, x17, x22
adc x15, x10, x10
adds x3, x25, x11
adcs x9, x8, x23
adcs x2, x6, x12
adc x14, x15, x20
umulh x24, x27, x14
mul x16, x27, x3
mul x5, x27, x9
mul x13, x27, x2
mul x7, x27, x14
umulh x22, x27, x2
umulh x17, x27, x3
umulh x11, x27, x9
adds x25, x28, x16
adcs x23, x21, x5
adcs x8, x1, x13
adcs x12, x4, x7
adc x6, x24, x10
ldp x20, x15, [x0, #352]
ldp x14, x2, [x0, #368]
ldp x3, x9, [x0, #384]
ldp x16, x28, [x0, #400]
adds x5, x12, x22
adc x21, x6, x10
subs x1, x20, x3
sbcs x13, x15, x9
sbcs x7, x14, x16
sbcs x4, x2, x28
csel x24, x10, x27, hs
extr x12, x21, x5, #63
and x22, x5, #0x7fffffffffffffff
mul x6, x12, x26
adds x3, x25, x6
adcs x20, x23, x17
adcs x9, x8, x11
adc x15, x22, x10
subs x14, x1, x24
sbcs x16, x13, x10
sbcs x2, x7, x10
sbc x28, x4, x10
stp x3, x20, [x0, #192]
stp x9, x15, [x0, #208]
ldp x21, x5, [x0, #384]
ldp x12, x25, [x0, #400]
stp x2, x28, [x0, #432]
stp x14, x16, [x0, #416]
ldr x6, [x0, #352]
ldr x23, [x0, #360]
umulh x17, x6, x21
umulh x8, x6, x5
umulh x11, x6, x12
umulh x22, x6, x25
mul x24, x6, x5
mul x1, x6, x12
mul x13, x6, x25
mul x7, x23, x21
mul x4, x23, x5
mul x3, x23, x12
mul x20, x6, x21
mul x9, x23, x25
umulh x15, x23, x21
umulh x2, x23, x5
adds x28, x24, x17
adcs x14, x1, x8
adcs x16, x13, x11
adc x6, x22, x10
umulh x17, x23, x12
umulh x24, x23, x25
ldr x8, [x0, #368]
adds x1, x28, x7
adcs x11, x14, x4
adcs x13, x16, x3
adcs x22, x6, x9
adc x23, x10, x10
mul x7, x8, x21
mul x28, x8, x5
mul x4, x8, x12
mul x14, x8, x25
umulh x3, x8, x21
umulh x16, x8, x5
adds x9, x11, x15
adcs x6, x13, x2
adcs x15, x22, x17
adc x11, x23, x24
umulh x2, x8, x12
umulh x13, x8, x25
ldr x22, [x0, #376]
adds x17, x9, x7
adcs x23, x6, x28
adcs x24, x15, x4
adcs x8, x11, x14
adc x7, x10, x10
mul x9, x22, x21
umulh x28, x22, x21
mul x6, x22, x5
umulh x15, x22, x5
mul x4, x22, x12
mul x11, x22, x25
adds x14, x23, x3
adcs x21, x24, x16
adcs x5, x8, x2
adc x23, x7, x13
umulh x3, x22, x12
umulh x24, x22, x25
adds x16, x14, x9
adcs x8, x21, x6
adcs x2, x5, x4
adcs x7, x23, x11
adc x13, x10, x10
adds x12, x8, x28
adcs x25, x2, x15
adcs x22, x7, x3
adc x14, x13, x24
umulh x9, x27, x14
mul x21, x27, x12
mul x6, x27, x25
mul x5, x27, x22
mul x4, x27, x14
umulh x11, x27, x22
umulh x23, x27, x12
umulh x8, x27, x25
adds x28, x20, x21
adcs x2, x1, x6
adcs x15, x17, x5
adcs x3, x16, x4
adc x7, x9, x10
ldp x24, x13, [x0, #432]
ldp x14, x22, [x0, #416]
movz x12, #56129, lsl #0
ldp x25, x20, [x0, #352]
ldp x21, x1, [x0, #368]
adds x6, x3, x11
adc x5, x7, x10
movk x12, #1, lsl #16
mul x17, x14, x12
extr x16, x5, x6, #63
mul x4, x22, x12
and x9, x6, #0x7fffffffffffffff
mul x3, x24, x12
mul x11, x16, x26
mul x7, x13, x12
adds x5, x28, x11
adcs x6, x2, x23
adcs x16, x15, x8
adc x28, x9, x10
umulh x11, x13, x12
adds x23, x25, x17
adcs x2, x20, x4
adcs x15, x21, x3
adcs x8, x1, x7
adc x9, x11, x10
stp x5, x6, [x0, #96]
stp x16, x28, [x0, #112]
umulh x13, x14, x12
umulh x25, x22, x12
umulh x17, x24, x12
ldr x20, [x0, #416]
adds x4, x8, x8
adc x3, x9, x9
mul x21, x3, x26
lsr x7, x4, #1
adds x1, x23, x21
adcs x11, x2, x13
adcs x5, x15, x25
adc x6, x7, x17
stp x1, x11, [x0, #128]
stp x5, x6, [x0, #144]
ldr x16, [x0, #424]
ldp x28, x14, [x0, #128]
ldp x22, x24, [x0, #144]
umulh x12, x20, x28
umulh x8, x20, x14
umulh x9, x20, x22
umulh x3, x20, x24
mul x4, x20, x14
mul x23, x20, x22
mul x21, x20, x24
mul x13, x16, x28
mul x2, x16, x14
mul x25, x16, x22
mul x15, x20, x28
mul x17, x16, x24
umulh x7, x16, x28
umulh x11, x16, x14
adds x1, x4, x12
adcs x5, x23, x8
adcs x6, x21, x9
adc x20, x3, x10
umulh x4, x16, x22
umulh x12, x16, x24
ldr x23, [x0, #432]
adds x8, x1, x13
adcs x21, x5, x2
adcs x9, x6, x25
adcs x3, x20, x17
adc x16, x10, x10
mul x1, x23, x28
mul x13, x23, x14
mul x5, x23, x22
mul x2, x23, x24
umulh x6, x23, x28
umulh x25, x23, x14
adds x17, x21, x7
adcs x20, x9, x11
adcs x21, x3, x4
adc x7, x16, x12
umulh x9, x23, x22
umulh x11, x23, x24
ldr x4, [x0, #440]
adds x3, x17, x1
adcs x12, x20, x13
adcs x16, x21, x5
adcs x23, x7, x2
adc x17, x10, x10
mul x1, x4, x28
umulh x13, x4, x28
mul x20, x4, x14
umulh x5, x4, x14
mul x21, x4, x22
mul x2, x4, x24
adds x7, x12, x6
adcs x28, x16, x25
adcs x14, x23, x9
adc x6, x17, x11
umulh x12, x4, x22
umulh x25, x4, x24
adds x16, x7, x1
adcs x9, x28, x20
adcs x23, x14, x21
adcs x11, x6, x2
adc x17, x10, x10
adds x22, x9, x13
adcs x4, x23, x5
adcs x24, x11, x12
adc x1, x17, x25
umulh x7, x27, x1
mul x20, x27, x22
mul x28, x27, x4
mul x21, x27, x24
mul x14, x27, x1
umulh x2, x27, x24
umulh x6, x27, x22
umulh x13, x27, x4
adds x9, x15, x20
adcs x5, x8, x28
adcs x23, x3, x21
adcs x11, x16, x14
adc x12, x7, x10
adds x17, x11, x2
adc x25, x12, x10
extr x1, x25, x17, #63
and x24, x17, #0x7fffffffffffffff
mul x22, x1, x26
adds x4, x9, x22
adcs x15, x5, x6
adcs x20, x23, x13
adc x8, x24, x10
stp x4, x15, [x0, #128]
stp x20, x8, [x0, #144]
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
.globl lab_sc_o1_21_15_1
lab_sc_o1_21_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
umulh x11, x3, x6
mul x4, x3, x15
umulh x8, x3, x15
mul x2, x3, x16
umulh x13, x3, x23
mul x17, x7, x16
umulh x5, x3, x16
mul x1, x3, x23
mul x9, x7, x23
mul x12, x7, x6
mul x21, x3, x6
umulh x20, x7, x6
umulh x22, x7, x16
mul x28, x7, x15
adds x24, x2, x11
adcs x25, x1, x5
adcs x14, x4, x13
adc x3, x8, x10
umulh x2, x7, x15
umulh x11, x7, x23
ldr x1, [x0, #336]
adds x5, x24, x12
adcs x4, x25, x17
adcs x13, x14, x9
adcs x8, x3, x28
adc x7, x10, x10
mul x12, x1, x6
mul x24, x1, x15
mul x25, x1, x16
mul x17, x1, x23
umulh x14, x1, x6
umulh x9, x1, x16
adds x3, x4, x20
adcs x28, x13, x22
adcs x4, x8, x11
adc x20, x7, x2
umulh x13, x1, x15
umulh x22, x1, x23
ldr x8, [x0, #344]
adds x11, x3, x12
adcs x2, x28, x25
adcs x7, x4, x17
adcs x1, x20, x24
adc x3, x10, x10
mul x12, x8, x6
umulh x28, x8, x6
mul x25, x8, x16
umulh x17, x8, x16
mul x4, x8, x15
mul x24, x8, x23
adds x20, x2, x14
adcs x6, x7, x9
adcs x16, x1, x22
adc x2, x3, x13
umulh x14, x8, x23
umulh x9, x8, x15
adds x7, x20, x12
adcs x22, x6, x25
adcs x1, x16, x24
adcs x13, x2, x4
adc x3, x10, x10
adds x23, x22, x28
adcs x15, x1, x17
adcs x8, x13, x14
adc x12, x3, x9
umulh x20, x27, x12
mul x25, x27, x23
mul x6, x27, x12
mul x24, x27, x15
mul x16, x27, x8
umulh x4, x27, x8
umulh x2, x27, x15
umulh x28, x27, x23
adds x22, x21, x25
adcs x17, x5, x24
adcs x1, x11, x16
adcs x14, x7, x6
adc x13, x20, x10
ldp x3, x9, [x0, #272]
ldp x12, x8, [x0, #256]
ldr x15, [x0, #288]
adds x23, x14, x4
adc x25, x13, x10
mul x21, x15, x8
mul x5, x15, x9
mul x24, x15, x3
mul x11, x15, x12
extr x16, x25, x23, #63
umulh x6, x15, x12
and x7, x23, #0x7fffffffffffffff
umulh x20, x15, x8
mul x14, x16, x26
umulh x4, x15, x3
adds x13, x22, x14
adcs x25, x17, x28
adcs x23, x1, x2
adc x16, x7, x10
umulh x22, x15, x9
adds x14, x21, x6
adcs x17, x24, x20
adcs x28, x5, x4
adc x1, x22, x10
stp x23, x16, [x0, #464]
stp x13, x25, [x0, #448]
ldr x2, [x0, #296]
mul x7, x2, x12
mul x15, x2, x8
mul x6, x2, x3
mul x21, x2, x9
umulh x20, x2, x9
ldr x24, [x0, #304]
umulh x4, x2, x3
umulh x5, x2, x12
umulh x22, x2, x8
adds x23, x14, x7
adcs x16, x17, x15
adcs x13, x28, x6
adcs x25, x1, x21
adc x2, x10, x10
mul x7, x24, x12
mul x14, x24, x3
mul x15, x24, x9
mul x17, x24, x8
umulh x6, x24, x12
umulh x28, x24, x8
adds x21, x16, x5
adcs x1, x13, x22
adcs x5, x25, x4
adc x16, x2, x20
umulh x22, x24, x3
umulh x13, x24, x9
ldr x25, [x0, #312]
adds x4, x21, x7
adcs x2, x1, x17
adcs x20, x5, x14
adcs x24, x16, x15
adc x7, x10, x10
mul x21, x25, x12
umulh x17, x25, x12
mul x1, x25, x9
umulh x5, x25, x8
mul x14, x25, x8
mul x16, x25, x3
adds x15, x2, x6
adcs x12, x20, x28
adcs x8, x24, x22
adc x2, x7, x13
umulh x6, x25, x3
umulh x20, x25, x9
adds x28, x15, x21
adcs x24, x12, x14
adcs x22, x8, x16
adcs x7, x2, x1
adc x13, x10, x10
adds x3, x24, x17
adcs x9, x22, x5
adcs x25, x7, x6
adc x15, x13, x20
umulh x21, x27, x15
mul x12, x27, x25
mul x14, x27, x9
mul x8, x27, x15
mul x16, x27, x3
umulh x1, x27, x25
umulh x2, x27, x9
umulh x24, x27, x3
adds x17, x11, x16
adcs x22, x23, x14
adcs x5, x4, x12
adcs x6, x28, x8
adc x7, x21, x10
ldp x20, x13, [x0, #224]
ldp x15, x25, [x0, #240]
adds x9, x6, x1
adc x3, x7, x10
mul x11, x20, x15
mul x16, x20, x25
umulh x23, x20, x13
umulh x14, x20, x15
mul x12, x20, x13
extr x4, x3, x9, #63
umulh x28, x20, x25
and x8, x9, #0x7fffffffffffffff
mul x21, x13, x15
mul x6, x4, x26
mul x1, x13, x25
adds x7, x17, x6
adcs x3, x22, x24
adcs x9, x5, x2
adc x4, x8, x10
umulh x17, x13, x25
umulh x6, x13, x15
umulh x24, x15, x25
mul x22, x15, x25
stp x7, x3, [x0, #480]
adds x5, x11, x23
adcs x2, x16, x14
adc x8, x28, x10
stp x9, x4, [x0, #496]
mul x7, x13, x13
umulh x3, x20, x20
mul x11, x20, x20
lsl x23, x12, #1
adds x16, x2, x21
adcs x14, x8, x1
adc x28, x17, x10
umulh x9, x13, x13
mul x4, x15, x15
umulh x20, x15, x15
extr x2, x5, x12, #63
adds x21, x14, x6
adcs x8, x28, x22
adc x1, x24, x10
umulh x17, x25, x25
mul x13, x25, x25
extr x15, x16, x5, #63
lsr x12, x1, #63
extr x14, x21, x16, #63
extr x6, x8, x21, #63
extr x28, x1, x8, #63
adds x22, x23, x3
adcs x24, x2, x7
adcs x25, x15, x9
adcs x5, x14, x4
adcs x16, x6, x20
adcs x21, x28, x13
adc x8, x12, x17
umulh x1, x27, x8
mul x23, x27, x5
mul x3, x27, x16
mul x2, x27, x21
mul x7, x27, x8
umulh x15, x27, x21
umulh x9, x27, x5
umulh x14, x27, x16
adds x4, x11, x23
adcs x20, x22, x3
adcs x6, x24, x2
adcs x13, x25, x7
adc x28, x1, x10
ldp x17, x12, [x0, #272]
ldp x8, x21, [x0, #256]
adds x5, x13, x15
adc x16, x28, x10
umulh x23, x8, x17
umulh x11, x8, x21
mul x22, x8, x17
mul x3, x8, x12
mul x2, x8, x21
extr x24, x16, x5, #63
umulh x7, x8, x12
and x25, x5, #0x7fffffffffffffff
mul x1, x21, x17
mul x15, x24, x26
mul x13, x21, x12
adds x28, x4, x15
adcs x16, x20, x9
adcs x5, x6, x14
adc x24, x25, x10
umulh x4, x21, x12
mul x15, x17, x12
umulh x20, x21, x17
umulh x9, x17, x12
stp x28, x16, [x0, #352]
adds x14, x22, x11
adcs x6, x3, x23
adc x25, x7, x10
stp x5, x24, [x0, #368]
umulh x28, x8, x8
mul x16, x21, x21
mul x11, x8, x8
lsl x22, x2, #1
adds x23, x6, x1
adcs x3, x25, x13
adc x7, x4, x10
umulh x24, x21, x21
mul x5, x17, x17
extr x8, x14, x2, #63
umulh x6, x17, x17
adds x1, x3, x20
adcs x25, x7, x15
adc x13, x9, x10
extr x4, x23, x14, #63
mul x21, x12, x12
umulh x2, x12, x12
lsr x17, x13, #63
extr x20, x1, x23, #63
extr x3, x25, x1, #63
extr x7, x13, x25, #63
adds x15, x22, x28
adcs x9, x8, x16
adcs x14, x4, x24
adcs x12, x20, x5
adcs x23, x3, x6
adcs x1, x7, x21
adc x25, x17, x2
umulh x13, x27, x25
mul x22, x27, x23
mul x28, x27, x25
mul x16, x27, x1
umulh x8, x27, x1
mul x24, x27, x12
umulh x4, x27, x23
umulh x5, x27, x12
adds x20, x11, x24
adcs x3, x15, x22
adcs x6, x9, x16
adcs x7, x14, x28
adc x21, x13, x10
ldp x2, x17, [x0, #480]
ldp x25, x1, [x0, #464]
ldp x23, x12, [x0, #448]
ldp x24, x11, [x0, #496]
adds x15, x7, x8
adc x22, x21, x10
subs x9, x23, x2
sbcs x16, x12, x17
sbcs x28, x25, x24
sbcs x14, x1, x11
csel x13, x10, x27, hs
extr x7, x22, x15, #63
and x8, x15, #0x7fffffffffffffff
mul x21, x7, x26
adds x2, x20, x21
adcs x23, x3, x5
adcs x17, x6, x4
adc x12, x8, x10
subs x25, x9, x13
sbcs x24, x16, x10
sbcs x1, x28, x10
sbc x11, x14, x10
stp x2, x23, [x0, #384]
stp x17, x12, [x0, #400]
umulh x22, x25, x24
umulh x15, x25, x1
mul x7, x25, x1
umulh x20, x25, x11
umulh x21, x24, x11
umulh x3, x1, x11
mul x5, x25, x11
mul x6, x24, x11
mul x4, x24, x1
umulh x8, x24, x1
mul x13, x1, x11
mul x9, x25, x24
adds x16, x7, x22
adcs x28, x5, x15
adc x14, x20, x10
mul x2, x24, x24
umulh x23, x25, x25
mul x17, x25, x25
lsl x12, x9, #1
adds x7, x28, x4
adcs x22, x14, x6
adc x5, x21, x10
umulh x15, x24, x24
mul x20, x1, x1
umulh x25, x1, x1
extr x28, x16, x9, #63
adds x4, x22, x8
adcs x14, x5, x13
adc x6, x3, x10
umulh x21, x11, x11
mul x24, x11, x11
extr x1, x7, x16, #63
lsr x9, x6, #63
extr x8, x6, x14, #63
extr x22, x14, x4, #63
extr x5, x4, x7, #63
adds x13, x12, x23
adcs x3, x28, x2
adcs x11, x1, x15
adcs x16, x5, x20
adcs x6, x22, x25
adcs x14, x8, x24
adc x4, x9, x21
umulh x7, x27, x4
mul x12, x27, x4
mul x23, x27, x14
mul x28, x27, x6
umulh x2, x27, x14
mul x1, x27, x16
umulh x15, x27, x6
umulh x20, x27, x16
adds x5, x17, x1
adcs x25, x13, x28
adcs x22, x3, x23
adcs x24, x11, x12
adc x8, x7, x10
ldp x21, x9, [x0, #464]
ldp x4, x14, [x0, #448]
ldp x6, x16, [x0, #480]
ldp x1, x17, [x0, #496]
adds x13, x24, x2
adc x28, x8, x10
adds x23, x4, x6
adcs x3, x14, x16
adcs x12, x21, x1
adcs x11, x9, x17
csel x7, x27, x10, hs
extr x2, x28, x13, #63
and x24, x13, #0x7fffffffffffffff
mul x8, x2, x26
adds x4, x5, x8
adcs x6, x25, x20
adcs x14, x22, x15
adc x16, x24, x10
adds x21, x23, x7
adcs x1, x3, x10
adc x9, x12, x10
stp x4, x6, [x0, #192]
stp x14, x16, [x0, #208]
mul x17, x21, x9
umulh x28, x21, x11
umulh x13, x21, x9
umulh x2, x21, x1
mul x5, x21, x11
mul x8, x1, x9
umulh x25, x1, x11
umulh x20, x9, x11
mul x22, x1, x11
mul x15, x21, x1
umulh x24, x1, x9
mul x23, x9, x11
adds x7, x17, x2
adcs x3, x5, x13
adc x12, x28, x10
umulh x4, x21, x21
lsl x6, x15, #1
mul x14, x1, x1
mul x16, x21, x21
adds x17, x3, x8
adcs x2, x12, x22
adc x5, x25, x10
mul x13, x9, x9
umulh x28, x9, x9
umulh x21, x1, x1
extr x3, x7, x15, #63
adds x8, x2, x24
adcs x12, x5, x23
adc x22, x20, x10
mul x25, x11, x11
umulh x9, x11, x11
extr x1, x17, x7, #63
lsr x15, x22, #63
extr x2, x8, x17, #63
extr x24, x22, x12, #63
extr x5, x12, x8, #63
adds x23, x6, x4
adcs x20, x3, x14
adcs x11, x1, x21
adcs x7, x2, x13
adcs x17, x5, x28
adcs x22, x24, x25
adc x8, x15, x9
umulh x12, x27, x8
mul x6, x27, x7
mul x4, x27, x22
mul x3, x27, x17
mul x14, x27, x8
umulh x1, x27, x22
umulh x21, x27, x7
umulh x2, x27, x17
adds x13, x16, x6
adcs x28, x23, x3
adcs x5, x20, x4
adcs x25, x11, x14
adc x24, x12, x10
ldp x9, x15, [x0, #192]
ldp x8, x22, [x0, #208]
ldr x7, [x0, #64]
adds x17, x25, x1
adc x6, x24, x10
mul x16, x7, x15
mul x23, x7, x8
mul x3, x7, x22
mul x4, x7, x9
extr x20, x6, x17, #63
umulh x11, x7, x9
and x14, x17, #0x7fffffffffffffff
umulh x12, x7, x15
mul x1, x20, x26
umulh x25, x7, x8
adds x24, x13, x1
adcs x6, x28, x21
adcs x17, x5, x2
adc x20, x14, x10
umulh x13, x7, x22
adds x1, x16, x11
adcs x28, x23, x12
adcs x21, x3, x25
adc x2, x13, x10
stp x24, x6, [x0, #160]
stp x17, x20, [x0, #176]
ldr x5, [x0, #72]
mul x14, x5, x9
mul x7, x5, x15
mul x11, x5, x22
mul x16, x5, x8
umulh x23, x5, x9
ldr x12, [x0, #80]
umulh x3, x5, x22
umulh x25, x5, x15
umulh x13, x5, x8
adds x24, x1, x14
adcs x6, x28, x7
adcs x20, x21, x16
adcs x17, x2, x11
adc x5, x10, x10
mul x14, x12, x9
mul x1, x12, x15
mul x7, x12, x8
umulh x28, x12, x15
mul x21, x12, x22
umulh x16, x12, x9
adds x2, x6, x23
adcs x11, x20, x25
adcs x6, x17, x13
adc x23, x5, x3
umulh x20, x12, x22
umulh x25, x12, x8
ldr x17, [x0, #88]
adds x13, x2, x14
adcs x5, x11, x1
adcs x3, x6, x7
adcs x12, x23, x21
adc x2, x10, x10
mul x14, x17, x9
umulh x11, x17, x9
mul x1, x17, x15
umulh x6, x17, x15
mul x7, x17, x22
mul x21, x17, x8
adds x23, x5, x16
adcs x9, x3, x28
adcs x15, x12, x25
adc x5, x2, x20
umulh x16, x17, x22
umulh x3, x17, x8
adds x28, x23, x14
adcs x25, x9, x1
adcs x12, x15, x21
adcs x20, x5, x7
adc x2, x10, x10
adds x22, x25, x11
adcs x8, x12, x6
adcs x17, x20, x3
adc x23, x2, x16
umulh x14, x27, x23
mul x1, x27, x17
mul x9, x27, x8
mul x21, x27, x23
mul x15, x27, x22
umulh x7, x27, x17
umulh x5, x27, x8
umulh x11, x27, x22
adds x25, x4, x15
adcs x6, x24, x9
adcs x12, x13, x1
adcs x3, x28, x21
adc x20, x14, x10
ldp x16, x2, [x0, #352]
ldp x23, x17, [x0, #384]
ldp x8, x22, [x0, #400]
ldp x15, x4, [x0, #368]
adds x9, x3, x7
adc x24, x20, x10
subs x13, x16, x23
sbcs x1, x2, x17
sbcs x21, x15, x8
sbcs x28, x4, x22
csel x14, x10, x27, hs
extr x3, x24, x9, #63
and x7, x9, #0x7fffffffffffffff
mul x20, x3, x26
adds x23, x25, x20
adcs x16, x6, x11
adcs x17, x12, x5
adc x2, x7, x10
subs x15, x13, x14
sbcs x8, x1, x10
sbcs x4, x21, x10
sbc x22, x28, x10
stp x23, x16, [x0, #192]
stp x17, x2, [x0, #208]
ldp x24, x9, [x0, #384]
ldr x3, [x0, #352]
stp x4, x22, [x0, #432]
stp x15, x8, [x0, #416]
ldp x25, x20, [x0, #400]
ldr x6, [x0, #360]
umulh x11, x3, x24
umulh x12, x3, x9
mul x5, x3, x9
umulh x7, x3, x20
mul x14, x3, x20
umulh x13, x3, x25
mul x1, x6, x9
mul x21, x6, x24
mul x28, x6, x25
mul x23, x3, x25
mul x16, x3, x24
mul x17, x6, x20
umulh x2, x6, x9
umulh x4, x6, x24
adds x22, x5, x11
adcs x15, x23, x12
adcs x8, x14, x13
adc x3, x7, x10
umulh x11, x6, x20
umulh x5, x6, x25
ldr x12, [x0, #368]
adds x23, x22, x21
adcs x13, x15, x1
adcs x14, x8, x28
adcs x7, x3, x17
adc x6, x10, x10
mul x21, x12, x24
mul x22, x12, x20
mul x1, x12, x25
mul x15, x12, x9
umulh x28, x12, x24
umulh x8, x12, x9
adds x17, x13, x4
adcs x3, x14, x2
adcs x4, x7, x5
adc x13, x6, x11
ldr x2, [x0, #376]
umulh x14, x12, x20
umulh x7, x12, x25
adds x5, x17, x21
adcs x6, x3, x15
adcs x11, x4, x1
adcs x12, x13, x22
adc x21, x10, x10
mul x17, x2, x25
umulh x15, x2, x9
mul x3, x2, x9
umulh x4, x2, x24
mul x1, x2, x24
mul x13, x2, x20
adds x22, x6, x28
adcs x9, x11, x8
adcs x24, x12, x7
adc x6, x21, x14
umulh x28, x2, x20
umulh x11, x2, x25
adds x8, x22, x1
adcs x12, x9, x3
adcs x7, x24, x17
adcs x21, x6, x13
adc x14, x10, x10
adds x20, x12, x4
adcs x25, x7, x15
adcs x2, x21, x11
adc x22, x14, x28
umulh x1, x27, x22
mul x9, x27, x22
mul x3, x27, x25
umulh x24, x27, x2
mul x17, x27, x20
mul x13, x27, x2
umulh x6, x27, x25
umulh x12, x27, x20
adds x4, x16, x17
adcs x7, x23, x3
adcs x15, x5, x13
adcs x11, x8, x9
adc x21, x1, x10
ldp x28, x14, [x0, #432]
movz x22, #56129, lsl #0
ldp x2, x25, [x0, #416]
ldp x20, x16, [x0, #368]
ldp x17, x23, [x0, #352]
adds x3, x11, x24
adc x13, x21, x10
movk x22, #1, lsl #16
mul x5, x2, x22
extr x8, x13, x3, #63
mul x9, x25, x22
and x1, x3, #0x7fffffffffffffff
mul x11, x28, x22
mul x24, x8, x26
mul x21, x14, x22
adds x13, x4, x24
adcs x3, x7, x12
adcs x8, x15, x6
adc x4, x1, x10
umulh x24, x14, x22
adds x12, x17, x5
adcs x7, x23, x9
adcs x15, x20, x11
adcs x6, x16, x21
adc x1, x24, x10
stp x8, x4, [x0, #112]
stp x13, x3, [x0, #96]
umulh x14, x2, x22
umulh x17, x28, x22
umulh x5, x25, x22
ldr x23, [x0, #416]
adds x9, x6, x6
adc x11, x1, x1
mul x20, x11, x26
lsr x21, x9, #1
adds x16, x12, x20
adcs x24, x7, x14
adcs x8, x15, x5
adc x4, x21, x17
stp x16, x24, [x0, #128]
stp x8, x4, [x0, #144]
ldr x13, [x0, #424]
ldp x3, x2, [x0, #128]
ldp x28, x25, [x0, #144]
umulh x22, x23, x3
umulh x6, x23, x28
mul x1, x23, x25
umulh x11, x23, x2
mul x9, x23, x28
umulh x12, x23, x25
mul x20, x13, x2
mul x14, x23, x2
mul x7, x13, x3
mul x5, x13, x28
mul x15, x23, x3
mul x17, x13, x25
umulh x21, x13, x3
umulh x24, x13, x2
adds x16, x14, x22
adcs x8, x9, x11
adcs x4, x1, x6
adc x23, x12, x10
umulh x14, x13, x25
umulh x22, x13, x28
ldr x9, [x0, #432]
adds x11, x16, x7
adcs x1, x8, x20
adcs x6, x4, x5
adcs x12, x23, x17
adc x13, x10, x10
mul x16, x9, x3
mul x7, x9, x25
mul x8, x9, x28
mul x20, x9, x2
umulh x4, x9, x2
umulh x5, x9, x3
adds x17, x1, x21
adcs x23, x6, x24
adcs x1, x12, x22
adc x21, x13, x14
umulh x6, x9, x25
umulh x24, x9, x28
ldr x22, [x0, #440]
adds x12, x17, x16
adcs x14, x23, x20
adcs x13, x1, x8
adcs x9, x21, x7
adc x17, x10, x10
mul x16, x22, x3
umulh x20, x22, x3
mul x23, x22, x28
mul x8, x22, x25
mul x1, x22, x2
umulh x7, x22, x2
adds x21, x14, x5
adcs x3, x13, x4
adcs x2, x9, x24
adc x5, x17, x6
umulh x14, x22, x28
umulh x4, x22, x25
adds x13, x21, x16
adcs x24, x3, x1
adcs x9, x2, x23
adcs x6, x5, x8
adc x17, x10, x10
adds x28, x24, x20
adcs x22, x9, x7
adcs x25, x6, x14
adc x16, x17, x4
umulh x21, x27, x16
mul x1, x27, x22
mul x3, x27, x28
mul x23, x27, x25
mul x2, x27, x16
umulh x8, x27, x25
umulh x5, x27, x28
umulh x20, x27, x22
adds x24, x15, x3
adcs x7, x11, x1
adcs x9, x12, x23
adcs x6, x13, x2
adc x14, x21, x10
adds x17, x6, x8
adc x4, x14, x10
extr x16, x4, x17, #63
and x25, x17, #0x7fffffffffffffff
mul x28, x16, x26
adds x22, x24, x28
adcs x15, x7, x5
adcs x3, x9, x20
adc x11, x25, x10
stp x22, x15, [x0, #128]
stp x3, x11, [x0, #144]
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
.globl lab_sc_o1_22_30_0
lab_sc_o1_22_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x11, x16, x5
adcs x25, x1, x28
csel x24, x27, x10, hs
stp x9, x21, [x0, #224]
stp x17, x3, [x0, #240]
stp x6, x15, [x0, #256]
stp x8, x23, [x0, #272]
subs x7, x12, x14
sbcs x16, x20, x10
sbcs x5, x13, x10
sbc x28, x4, x10
adds x1, x22, x24
adcs x9, x2, x10
adc x21, x11, x10
ldp x17, x3, [x0, #224]
ldp x6, x15, [x0, #240]
stp x7, x16, [x0, #320]
stp x1, x9, [x0, #288]
stp x21, x25, [x0, #304]
stp x5, x28, [x0, #336]
ldr x8, [x0, #320]
ldr x23, [x0, #328]
ldr x12, [x0, #336]
umulh x14, x8, x17
umulh x20, x8, x3
umulh x13, x8, x6
umulh x4, x8, x15
mul x22, x8, x3
mul x24, x8, x6
mul x2, x8, x15
mul x11, x23, x17
mul x7, x23, x3
mul x16, x23, x6
mul x1, x23, x15
umulh x9, x23, x17
umulh x21, x23, x3
umulh x25, x23, x6
umulh x5, x23, x15
adds x28, x22, x14
adcs x23, x24, x20
adcs x22, x2, x13
adc x14, x4, x10
mul x24, x8, x17
mul x20, x12, x17
mul x2, x12, x3
mul x13, x12, x6
mul x4, x12, x15
adds x8, x28, x11
adcs x11, x23, x7
adcs x28, x22, x16
adcs x23, x14, x1
adc x7, x10, x10
umulh x22, x12, x17
umulh x16, x12, x3
umulh x14, x12, x6
umulh x1, x12, x15
adds x12, x11, x9
adcs x11, x28, x21
adcs x9, x23, x25
adc x28, x7, x5
ldr x21, [x0, #344]
adds x23, x12, x20
adcs x25, x11, x2
adcs x5, x9, x13
adcs x7, x28, x4
adc x12, x10, x10
mul x20, x21, x17
umulh x11, x21, x17
mul x2, x21, x3
umulh x13, x21, x3
mul x9, x21, x6
umulh x4, x21, x6
mul x28, x21, x15
umulh x17, x21, x15
adds x3, x25, x22
adcs x6, x5, x16
adcs x15, x7, x14
adc x21, x12, x1
adds x25, x3, x20
adcs x22, x6, x2
adcs x16, x15, x9
adcs x5, x21, x28
adc x14, x10, x10
ldp x7, x1, [x0, #256]
ldp x12, x20, [x0, #272]
ldr x3, [x0, #288]
adds x2, x22, x11
adcs x6, x16, x13
adcs x9, x5, x4
adc x15, x14, x17
mul x28, x3, x1
mul x21, x3, x12
mul x11, x3, x20
mul x22, x3, x7
umulh x13, x27, x15
mul x16, x27, x15
mul x4, x27, x2
umulh x5, x3, x7
umulh x14, x27, x2
mul x17, x27, x6
umulh x15, x3, x1
umulh x2, x27, x6
mul x6, x27, x9
umulh x9, x27, x9
adds x4, x24, x4
adcs x24, x8, x17
adcs x8, x23, x6
adcs x17, x25, x16
adc x23, x13, x10
umulh x6, x3, x12
umulh x16, x3, x20
ldr x25, [x0, #296]
adds x13, x28, x5
adcs x3, x21, x15
adcs x5, x11, x6
adc x28, x16, x10
adds x15, x17, x9
adc x21, x23, x10
mul x6, x25, x7
mul x11, x25, x1
mul x16, x25, x12
mul x17, x25, x20
extr x9, x21, x15, #63
and x23, x15, #0x7fffffffffffffff
mul x21, x9, x26
adds x15, x13, x6
adcs x9, x3, x11
adcs x6, x5, x16
adcs x13, x28, x17
adc x11, x10, x10
adds x3, x4, x21
adcs x16, x24, x14
adcs x5, x8, x2
adc x17, x23, x10
umulh x28, x25, x7
umulh x4, x25, x1
umulh x21, x25, x12
umulh x24, x25, x20
stp x3, x16, [x0, #448]
stp x5, x17, [x0, #464]
ldr x14, [x0, #304]
adds x8, x9, x28
adcs x2, x6, x4
adcs x23, x13, x21
adc x25, x11, x24
ldr x3, [x0, #312]
mul x16, x14, x7
mul x5, x14, x1
mul x17, x14, x12
mul x28, x14, x20
umulh x9, x14, x7
umulh x4, x14, x1
umulh x6, x14, x12
umulh x13, x14, x20
mul x21, x3, x7
umulh x11, x3, x7
mul x24, x3, x1
adds x14, x8, x16
adcs x7, x2, x5
adcs x16, x23, x17
adcs x8, x25, x28
adc x5, x10, x10
umulh x2, x3, x1
mul x23, x3, x12
umulh x17, x3, x12
mul x25, x3, x20
umulh x28, x3, x20
adds x1, x7, x9
adcs x12, x16, x4
adcs x20, x8, x6
adc x3, x5, x13
adds x7, x1, x21
adcs x9, x12, x24
adcs x16, x20, x23
adcs x4, x3, x25
adc x8, x10, x10
ldp x6, x5, [x0, #224]
ldp x13, x1, [x0, #240]
adds x21, x9, x11
adcs x12, x16, x2
adcs x24, x4, x17
adc x20, x8, x28
umulh x23, x6, x5
umulh x25, x6, x13
mul x3, x6, x13
mul x9, x6, x1
mul x11, x6, x5
umulh x16, x27, x20
mul x2, x27, x20
mul x17, x27, x21
umulh x4, x6, x1
umulh x28, x27, x21
mul x8, x27, x12
umulh x20, x27, x12
mul x21, x5, x13
mul x12, x27, x24
umulh x24, x27, x24
adds x22, x22, x17
adcs x17, x15, x8
adcs x15, x14, x12
adcs x8, x7, x2
adc x12, x16, x10
adds x14, x3, x23
adcs x7, x9, x25
adc x2, x4, x10
umulh x16, x5, x1
mul x3, x5, x1
umulh x23, x5, x13
umulh x9, x13, x1
mul x25, x13, x1
adds x4, x7, x21
adcs x7, x2, x3
adc x21, x16, x10
adds x2, x8, x24
adc x3, x12, x10
extr x16, x3, x2, #63
adds x8, x7, x23
adcs x24, x21, x25
adc x12, x9, x10
mul x3, x16, x26
and x7, x2, #0x7fffffffffffffff
adds x23, x22, x3
adcs x21, x17, x28
adcs x25, x15, x20
adc x9, x7, x10
lsr x16, x12, #63
extr x2, x12, x24, #63
extr x22, x24, x8, #63
extr x3, x8, x4, #63
extr x28, x4, x14, #63
extr x17, x14, x11, #63
stp x23, x21, [x0, #480]
lsl x15, x11, #1
stp x25, x9, [x0, #496]
umulh x20, x6, x6
umulh x7, x5, x5
umulh x12, x13, x13
umulh x24, x1, x1
mul x8, x5, x5
mul x4, x13, x13
mul x14, x1, x1
mul x23, x6, x6
adds x21, x15, x20
adcs x11, x17, x8
adcs x25, x28, x7
adcs x9, x3, x4
adcs x5, x22, x12
adcs x13, x2, x14
adc x1, x16, x24
ldp x6, x15, [x0, #256]
ldp x20, x17, [x0, #272]
umulh x8, x6, x15
umulh x28, x6, x20
mul x7, x6, x20
mul x3, x6, x17
mul x4, x6, x15
umulh x12, x27, x1
mul x22, x27, x1
mul x14, x27, x9
umulh x2, x6, x17
umulh x24, x27, x9
mul x16, x27, x5
mul x1, x15, x20
umulh x9, x27, x5
mul x5, x27, x13
umulh x13, x27, x13
adds x14, x23, x14
adcs x23, x21, x16
adcs x21, x11, x5
adcs x16, x25, x22
adc x5, x12, x10
adds x11, x7, x8
adcs x22, x3, x28
adc x25, x2, x10
umulh x12, x15, x17
mul x8, x15, x17
umulh x7, x15, x20
umulh x28, x20, x17
mul x3, x20, x17
adds x2, x22, x1
adcs x22, x25, x8
adc x1, x12, x10
adds x25, x16, x13
adc x8, x5, x10
extr x12, x8, x25, #63
adds x13, x22, x7
adcs x16, x1, x3
adc x5, x28, x10
mul x8, x12, x26
and x7, x25, #0x7fffffffffffffff
adds x22, x14, x8
adcs x1, x23, x24
adcs x3, x21, x9
adc x28, x7, x10
lsr x12, x5, #63
extr x25, x5, x16, #63
extr x14, x16, x13, #63
extr x8, x13, x2, #63
extr x23, x2, x11, #63
extr x24, x11, x4, #63
stp x22, x1, [x0, #352]
lsl x9, x4, #1
stp x3, x28, [x0, #368]
umulh x21, x6, x6
umulh x7, x15, x15
umulh x5, x20, x20
umulh x16, x17, x17
mul x13, x15, x15
mul x2, x20, x20
mul x11, x17, x17
mul x22, x6, x6
adds x1, x9, x21
adcs x4, x24, x13
adcs x28, x23, x7
adcs x3, x8, x2
adcs x15, x14, x5
adcs x20, x25, x11
adc x17, x12, x16
ldp x6, x9, [x0, #448]
ldp x21, x13, [x0, #464]
ldp x24, x7, [x0, #480]
ldp x23, x2, [x0, #496]
subs x8, x6, x24
sbcs x14, x9, x7
sbcs x5, x21, x23
sbcs x25, x13, x2
csel x11, x10, x27, hs
umulh x16, x27, x17
mul x12, x27, x3
mul x24, x27, x15
mul x6, x27, x20
mul x7, x27, x17
umulh x9, x27, x20
umulh x21, x27, x3
umulh x23, x27, x15
adds x13, x22, x12
adcs x2, x1, x24
adcs x17, x4, x6
adcs x20, x28, x7
adc x3, x16, x10
subs x15, x8, x11
sbcs x12, x14, x10
sbcs x22, x5, x10
sbc x1, x25, x10
adds x24, x20, x9
adc x4, x3, x10
umulh x6, x15, x12
umulh x7, x15, x22
umulh x28, x15, x1
mul x16, x15, x22
mul x11, x15, x1
mul x8, x12, x22
extr x14, x4, x24, #63
and x5, x24, #0x7fffffffffffffff
umulh x25, x12, x1
mul x20, x12, x1
mul x9, x14, x26
umulh x3, x12, x22
umulh x4, x22, x1
mul x24, x22, x1
adds x14, x13, x9
adcs x13, x2, x21
adcs x9, x17, x23
adc x2, x5, x10
adds x21, x16, x6
adcs x17, x11, x7
adc x23, x28, x10
mul x5, x15, x12
stp x14, x13, [x0, #384]
stp x9, x2, [x0, #400]
adds x16, x17, x8
adcs x6, x23, x20
adc x11, x25, x10
umulh x7, x15, x15
umulh x28, x12, x12
umulh x14, x22, x22
umulh x13, x1, x1
mul x9, x12, x12
mul x2, x22, x22
mul x17, x1, x1
extr x8, x21, x5, #63
lsl x23, x5, #1
adds x20, x6, x3
adcs x25, x11, x24
adc x12, x4, x10
extr x22, x16, x21, #63
mul x1, x15, x15
lsr x5, x12, #63
extr x3, x12, x25, #63
extr x6, x25, x20, #63
extr x11, x20, x16, #63
adds x24, x23, x7
adcs x4, x8, x9
adcs x21, x22, x28
adcs x15, x11, x2
adcs x12, x6, x14
adcs x25, x3, x17
adc x20, x5, x13
ldp x16, x23, [x0, #448]
ldp x7, x8, [x0, #464]
ldp x9, x22, [x0, #480]
ldp x28, x2, [x0, #496]
adds x11, x16, x9
adcs x14, x23, x22
adcs x6, x7, x28
adcs x17, x8, x2
csel x3, x27, x10, hs
umulh x13, x27, x20
mul x5, x27, x15
mul x16, x27, x12
mul x9, x27, x25
mul x23, x27, x20
umulh x22, x27, x25
umulh x7, x27, x15
umulh x28, x27, x12
adds x8, x1, x5
adcs x2, x24, x16
adcs x20, x4, x9
adcs x25, x21, x23
adc x15, x13, x10
adds x12, x11, x3
adcs x5, x14, x10
adc x1, x6, x10
umulh x24, x12, x5
umulh x16, x12, x1
umulh x9, x12, x17
adds x4, x25, x22
adc x23, x15, x10
mul x21, x12, x1
mul x13, x12, x17
umulh x11, x5, x17
mul x3, x5, x1
mul x14, x5, x17
umulh x6, x5, x1
extr x22, x23, x4, #63
and x25, x4, #0x7fffffffffffffff
umulh x15, x1, x17
mul x23, x1, x17
mul x4, x22, x26
adds x22, x21, x24
adcs x21, x13, x16
adc x24, x9, x10
mul x13, x12, x5
adds x16, x8, x4
adcs x9, x2, x7
adcs x8, x20, x28
adc x4, x25, x10
adds x2, x21, x3
adcs x7, x24, x14
adc x20, x11, x10
stp x16, x9, [x0, #192]
stp x8, x4, [x0, #208]
adds x28, x7, x6
adcs x25, x20, x23
adc x21, x15, x10
umulh x3, x12, x12
umulh x24, x5, x5
umulh x14, x1, x1
umulh x11, x17, x17
mul x16, x5, x5
mul x9, x1, x1
mul x8, x17, x17
extr x4, x2, x22, #63
extr x7, x22, x13, #63
lsr x6, x21, #63
extr x20, x21, x25, #63
extr x23, x25, x28, #63
extr x15, x28, x2, #63
lsl x5, x13, #1
mul x1, x12, x12
adds x17, x5, x3
adcs x22, x7, x16
adcs x21, x4, x24
adcs x25, x15, x9
adcs x28, x23, x14
adcs x2, x20, x8
adc x13, x6, x11
ldp x12, x5, [x0, #192]
ldp x3, x7, [x0, #208]
ldr x16, [x0, #64]
mul x4, x16, x5
mul x24, x16, x3
mul x15, x16, x7
umulh x9, x27, x13
mul x14, x27, x13
mul x23, x27, x25
umulh x8, x16, x12
umulh x20, x27, x25
mul x11, x27, x28
umulh x6, x16, x5
umulh x13, x27, x28
mul x25, x27, x2
umulh x28, x27, x2
adds x2, x1, x23
adcs x23, x17, x11
adcs x1, x22, x25
adcs x17, x21, x14
adc x11, x9, x10
umulh x25, x16, x3
umulh x22, x16, x7
ldr x21, [x0, #72]
mul x14, x16, x12
adds x9, x4, x8
adcs x16, x24, x6
adcs x8, x15, x25
adc x4, x22, x10
adds x24, x17, x28
adc x6, x11, x10
mul x15, x21, x12
mul x25, x21, x5
mul x22, x21, x3
mul x28, x21, x7
extr x17, x6, x24, #63
and x11, x24, #0x7fffffffffffffff
mul x6, x17, x26
adds x24, x9, x15
adcs x17, x16, x25
adcs x15, x8, x22
adcs x9, x4, x28
adc x25, x10, x10
adds x16, x2, x6
adcs x8, x23, x20
adcs x22, x1, x13
adc x4, x11, x10
umulh x28, x21, x12
umulh x2, x21, x5
umulh x6, x21, x3
umulh x23, x21, x7
stp x16, x8, [x0, #160]
stp x22, x4, [x0, #176]
ldr x20, [x0, #80]
adds x13, x17, x28
adcs x1, x15, x2
adcs x11, x9, x6
adc x21, x25, x23
ldr x16, [x0, #88]
mul x8, x20, x12
mul x4, x20, x5
mul x22, x20, x3
mul x17, x20, x7
umulh x28, x20, x12
umulh x15, x20, x5
umulh x2, x20, x3
umulh x9, x20, x7
mul x6, x16, x12
umulh x25, x16, x12
mul x23, x16, x5
adds x20, x13, x8
adcs x12, x1, x4
adcs x13, x11, x22
adcs x8, x21, x17
adc x1, x10, x10
umulh x4, x16, x5
mul x11, x16, x3
umulh x22, x16, x3
mul x17, x16, x7
umulh x21, x16, x7
adds x5, x12, x28
adcs x3, x13, x15
adcs x7, x8, x2
adc x16, x1, x9
adds x12, x5, x6
adcs x28, x3, x23
adcs x13, x7, x11
adcs x15, x16, x17
adc x2, x10, x10
ldp x8, x9, [x0, #352]
ldp x1, x5, [x0, #368]
ldp x6, x23, [x0, #384]
adds x3, x28, x25
adcs x11, x13, x4
adcs x7, x15, x22
adc x17, x2, x21
ldp x16, x25, [x0, #400]
umulh x28, x27, x17
mul x4, x27, x17
mul x13, x27, x3
umulh x22, x27, x3
subs x15, x8, x6
sbcs x21, x9, x23
sbcs x2, x1, x16
sbcs x17, x5, x25
csel x3, x10, x27, hs
mul x6, x27, x11
mul x8, x27, x7
umulh x23, x27, x7
umulh x9, x27, x11
adds x1, x14, x13
adcs x16, x24, x6
adcs x5, x20, x8
adcs x25, x12, x4
adc x7, x28, x10
ldp x11, x13, [x0, #384]
subs x14, x15, x3
sbcs x6, x21, x10
sbcs x24, x2, x10
sbc x20, x17, x10
ldp x8, x4, [x0, #400]
ldr x12, [x0, #352]
adds x28, x25, x23
adc x3, x7, x10
stp x24, x20, [x0, #432]
stp x14, x6, [x0, #416]
mul x15, x12, x13
mul x21, x12, x8
mul x2, x12, x4
mul x17, x12, x11
extr x25, x3, x28, #63
umulh x23, x12, x11
and x7, x28, #0x7fffffffffffffff
umulh x24, x12, x13
mul x20, x25, x26
umulh x14, x12, x8
adds x6, x1, x20
adcs x3, x16, x22
adcs x28, x5, x9
adc x25, x7, x10
umulh x1, x12, x4
adds x20, x15, x23
adcs x16, x21, x24
adcs x22, x2, x14
adc x5, x1, x10
stp x6, x3, [x0, #192]
stp x28, x25, [x0, #208]
ldr x9, [x0, #360]
ldr x7, [x0, #368]
mul x12, x9, x11
mul x23, x9, x13
mul x15, x9, x8
mul x24, x9, x4
umulh x21, x9, x11
umulh x14, x9, x13
umulh x2, x9, x8
umulh x1, x9, x4
mul x6, x7, x11
mul x3, x7, x13
mul x28, x7, x8
adds x25, x20, x12
adcs x9, x16, x23
adcs x12, x22, x15
adcs x20, x5, x24
adc x23, x10, x10
mul x16, x7, x4
umulh x15, x7, x11
umulh x22, x7, x13
umulh x24, x7, x8
umulh x5, x7, x4
adds x7, x9, x21
adcs x21, x12, x14
adcs x9, x20, x2
adc x14, x23, x1
ldr x12, [x0, #376]
adds x20, x7, x6
adcs x2, x21, x3
adcs x23, x9, x28
adcs x1, x14, x16
adc x6, x10, x10
mul x7, x12, x11
umulh x3, x12, x11
mul x21, x12, x13
umulh x9, x12, x13
mul x28, x12, x8
umulh x14, x12, x8
mul x16, x12, x4
umulh x11, x12, x4
adds x13, x2, x15
adcs x8, x23, x22
adcs x4, x1, x24
adc x12, x6, x5
adds x2, x13, x7
adcs x15, x8, x21
adcs x23, x4, x28
adcs x22, x12, x16
adc x1, x10, x10
ldp x24, x6, [x0, #416]
ldp x5, x13, [x0, #352]
ldp x7, x8, [x0, #368]
adds x21, x15, x3
adcs x4, x23, x9
adcs x28, x22, x14
adc x16, x1, x11
ldp x12, x15, [x0, #432]
movz x3, #56129, lsl #0
movk x3, #1, lsl #16
mul x23, x24, x3
umulh x9, x27, x16
mul x14, x27, x16
mul x22, x27, x21
mul x11, x6, x3
umulh x1, x27, x21
mul x16, x27, x4
umulh x21, x27, x4
mul x4, x27, x28
umulh x28, x27, x28
adds x17, x17, x22
adcs x22, x25, x16
adcs x25, x20, x4
adcs x16, x2, x14
adc x4, x9, x10
umulh x20, x24, x3
umulh x2, x6, x3
umulh x14, x15, x3
mul x9, x15, x3
mul x24, x12, x3
umulh x6, x12, x3
adds x15, x5, x23
adcs x12, x13, x11
adcs x3, x7, x24
adcs x5, x8, x9
adc x23, x14, x10
adds x13, x16, x28
adc x11, x4, x10
extr x24, x11, x13, #63
and x7, x13, #0x7fffffffffffffff
mul x9, x24, x26
adds x8, x5, x5
adc x14, x23, x23
adds x16, x17, x9
adcs x28, x22, x1
adcs x4, x25, x21
adc x11, x7, x10
mul x13, x14, x26
lsr x24, x8, #1
adds x5, x15, x13
adcs x23, x12, x20
adcs x17, x3, x2
adc x9, x24, x6
stp x16, x28, [x0, #96]
stp x4, x11, [x0, #112]
ldr x1, [x0, #416]
ldr x22, [x0, #424]
stp x5, x23, [x0, #128]
stp x17, x9, [x0, #144]
ldp x25, x21, [x0, #128]
ldp x7, x14, [x0, #144]
ldr x8, [x0, #432]
umulh x15, x1, x25
umulh x13, x1, x21
umulh x20, x1, x7
umulh x12, x1, x14
mul x2, x1, x21
mul x3, x1, x7
mul x6, x1, x14
mul x24, x22, x25
mul x16, x22, x21
mul x28, x22, x7
mul x4, x22, x14
umulh x11, x22, x25
umulh x23, x22, x21
umulh x5, x22, x7
umulh x17, x22, x14
adds x9, x2, x15
adcs x22, x3, x13
adcs x2, x6, x20
adc x15, x12, x10
mul x3, x1, x25
mul x13, x8, x25
mul x6, x8, x21
mul x20, x8, x7
mul x12, x8, x14
adds x1, x9, x24
adcs x9, x22, x16
adcs x24, x2, x28
adcs x22, x15, x4
adc x16, x10, x10
umulh x2, x8, x25
umulh x28, x8, x21
umulh x4, x8, x7
umulh x15, x8, x14
adds x8, x9, x11
adcs x9, x24, x23
adcs x11, x22, x5
adc x24, x16, x17
ldr x23, [x0, #440]
adds x5, x8, x13
adcs x22, x9, x6
adcs x17, x11, x20
adcs x16, x24, x12
adc x8, x10, x10
mul x13, x23, x25
umulh x6, x23, x25
mul x9, x23, x21
umulh x20, x23, x21
mul x11, x23, x7
umulh x12, x23, x7
mul x24, x23, x14
umulh x25, x23, x14
adds x21, x22, x2
adcs x7, x17, x28
adcs x23, x16, x4
adc x14, x8, x15
adds x2, x21, x13
adcs x22, x7, x9
adcs x28, x23, x11
adcs x17, x14, x24
adc x4, x10, x10
adds x16, x22, x6
adcs x15, x28, x20
adcs x8, x17, x12
adc x13, x4, x25
umulh x21, x27, x13
mul x9, x27, x16
mul x7, x27, x15
mul x11, x27, x8
mul x23, x27, x13
umulh x24, x27, x8
umulh x14, x27, x16
umulh x6, x27, x15
adds x22, x3, x9
adcs x20, x1, x7
adcs x28, x5, x11
adcs x17, x2, x23
adc x12, x21, x10
adds x4, x17, x24
adc x25, x12, x10
extr x13, x25, x4, #63
and x8, x4, #0x7fffffffffffffff
mul x16, x13, x26
adds x15, x22, x16
adcs x3, x20, x14
adcs x9, x28, x6
adc x1, x8, x10
stp x15, x3, [x0, #128]
stp x9, x1, [x0, #144]
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
.globl lab_sc_o1_22_30_1
lab_sc_o1_22_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
ldr x11, [x0, #336]
umulh x4, x3, x12
mul x8, x3, x24
umulh x2, x3, x24
mul x13, x3, x9
umulh x17, x3, x25
mul x14, x7, x9
umulh x1, x3, x9
mul x6, x3, x25
mul x20, x7, x25
mul x22, x7, x12
umulh x16, x7, x12
umulh x23, x7, x9
mul x15, x7, x24
umulh x21, x7, x24
umulh x5, x7, x25
mul x28, x3, x12
mul x7, x11, x12
adds x3, x13, x4
adcs x13, x6, x1
adcs x4, x8, x17
adc x6, x2, x10
mul x1, x11, x24
mul x8, x11, x9
mul x17, x11, x25
adds x2, x3, x22
adcs x22, x13, x14
adcs x3, x4, x20
adcs x13, x6, x15
adc x14, x10, x10
umulh x4, x11, x12
umulh x20, x11, x24
umulh x6, x11, x25
umulh x15, x11, x9
adds x11, x22, x16
adcs x22, x3, x23
adcs x16, x13, x5
adc x3, x14, x21
ldr x23, [x0, #344]
adds x13, x11, x7
adcs x5, x22, x8
adcs x21, x16, x17
adcs x14, x3, x1
adc x11, x10, x10
mul x7, x23, x9
umulh x22, x23, x9
umulh x8, x23, x12
mul x17, x23, x12
mul x16, x23, x24
umulh x1, x23, x24
mul x3, x23, x25
umulh x9, x23, x25
adds x12, x5, x4
adcs x24, x21, x15
adcs x25, x14, x6
adc x23, x11, x20
adds x5, x12, x17
adcs x4, x24, x7
adcs x15, x25, x3
adcs x21, x23, x16
adc x6, x10, x10
ldp x14, x20, [x0, #272]
ldp x11, x17, [x0, #256]
ldr x12, [x0, #288]
adds x7, x4, x8
adcs x24, x15, x22
adcs x3, x21, x9
adc x25, x6, x1
mul x16, x12, x20
mul x23, x12, x17
mul x8, x12, x14
mul x4, x12, x11
umulh x22, x27, x25
mul x15, x27, x25
mul x9, x27, x7
umulh x21, x12, x11
mul x6, x27, x24
umulh x1, x12, x17
umulh x25, x27, x24
umulh x24, x27, x7
mul x7, x27, x3
umulh x3, x27, x3
adds x9, x28, x9
adcs x28, x2, x6
adcs x2, x13, x7
adcs x6, x5, x15
adc x13, x22, x10
umulh x7, x12, x14
umulh x15, x12, x20
ldr x5, [x0, #296]
adds x22, x23, x21
adcs x12, x8, x1
adcs x21, x16, x7
adc x23, x15, x10
adds x1, x6, x3
adc x8, x13, x10
mul x7, x5, x17
mul x16, x5, x14
mul x15, x5, x11
mul x6, x5, x20
extr x3, x8, x1, #63
and x13, x1, #0x7fffffffffffffff
mul x8, x3, x26
adds x1, x22, x15
adcs x3, x12, x7
adcs x15, x21, x16
adcs x22, x23, x6
adc x7, x10, x10
adds x12, x9, x8
adcs x16, x28, x24
adcs x21, x2, x25
adc x6, x13, x10
umulh x23, x5, x20
umulh x9, x5, x14
umulh x8, x5, x11
umulh x28, x5, x17
stp x12, x16, [x0, #448]
stp x21, x6, [x0, #464]
ldr x24, [x0, #304]
adds x2, x3, x8
adcs x25, x15, x28
adcs x13, x22, x9
adc x5, x7, x23
ldr x12, [x0, #312]
mul x16, x24, x11
mul x21, x24, x14
mul x6, x24, x20
mul x8, x24, x17
umulh x3, x24, x14
umulh x28, x24, x20
umulh x15, x24, x11
umulh x22, x24, x17
mul x9, x12, x20
umulh x7, x12, x20
mul x23, x12, x11
adds x24, x2, x16
adcs x20, x25, x8
adcs x16, x13, x21
adcs x2, x5, x6
adc x8, x10, x10
umulh x25, x12, x11
umulh x13, x12, x17
mul x21, x12, x17
mul x5, x12, x14
umulh x6, x12, x14
adds x11, x20, x15
adcs x17, x16, x22
adcs x14, x2, x3
adc x12, x8, x28
adds x20, x11, x23
adcs x15, x17, x21
adcs x16, x14, x5
adcs x22, x12, x9
adc x2, x10, x10
ldp x3, x8, [x0, #224]
ldp x28, x11, [x0, #240]
adds x23, x15, x25
adcs x17, x16, x13
adcs x21, x22, x6
adc x14, x2, x7
mul x5, x3, x28
mul x9, x3, x11
umulh x12, x3, x8
umulh x15, x3, x28
mul x25, x3, x8
umulh x16, x27, x14
mul x13, x27, x14
mul x6, x27, x21
umulh x22, x27, x21
mul x7, x27, x17
umulh x2, x27, x17
mul x14, x27, x23
umulh x21, x3, x11
umulh x17, x27, x23
adds x23, x4, x14
adcs x4, x1, x7
adcs x14, x24, x6
adcs x1, x20, x13
adc x7, x16, x10
adds x6, x5, x12
adcs x24, x9, x15
adc x20, x21, x10
umulh x13, x8, x11
mul x16, x8, x11
mul x5, x8, x28
umulh x12, x8, x28
umulh x9, x28, x11
mul x15, x28, x11
adds x21, x24, x5
adcs x24, x20, x16
adc x5, x13, x10
adds x20, x1, x22
adc x16, x7, x10
extr x13, x16, x20, #63
adds x1, x24, x12
adcs x22, x5, x15
adc x7, x9, x10
mul x16, x13, x26
and x24, x20, #0x7fffffffffffffff
adds x12, x23, x16
adcs x5, x4, x17
adcs x15, x14, x2
adc x9, x24, x10
extr x13, x22, x1, #63
lsr x20, x7, #63
extr x23, x1, x21, #63
extr x16, x21, x6, #63
extr x17, x7, x22, #63
extr x4, x6, x25, #63
stp x12, x5, [x0, #480]
lsl x14, x25, #1
stp x15, x9, [x0, #496]
umulh x2, x11, x11
umulh x24, x8, x8
mul x1, x11, x11
mul x21, x8, x8
mul x22, x28, x28
umulh x7, x28, x28
umulh x6, x3, x3
mul x12, x3, x3
adds x5, x14, x6
adcs x25, x4, x21
adcs x15, x16, x24
adcs x9, x23, x22
adcs x11, x13, x7
adcs x8, x17, x1
adc x28, x20, x2
ldp x3, x14, [x0, #272]
ldp x6, x4, [x0, #256]
umulh x21, x6, x4
umulh x16, x6, x3
mul x24, x6, x3
mul x23, x6, x14
mul x22, x6, x4
mul x7, x27, x9
umulh x13, x6, x14
umulh x1, x27, x9
mul x17, x27, x11
mul x2, x4, x3
umulh x20, x27, x11
mul x9, x27, x8
umulh x11, x27, x8
mul x8, x27, x28
umulh x28, x27, x28
adds x7, x12, x7
adcs x12, x5, x17
adcs x5, x25, x9
adcs x17, x15, x8
adc x9, x28, x10
adds x25, x24, x21
adcs x8, x23, x16
adc x15, x13, x10
mul x28, x4, x14
umulh x21, x4, x14
mul x24, x3, x14
umulh x16, x4, x3
umulh x23, x3, x14
adds x13, x17, x11
adc x11, x9, x10
adds x17, x8, x2
adcs x9, x15, x28
adc x8, x21, x10
extr x2, x11, x13, #63
and x15, x13, #0x7fffffffffffffff
mul x28, x2, x26
adds x21, x9, x16
adcs x11, x8, x24
adc x13, x23, x10
adds x2, x7, x28
adcs x16, x12, x1
adcs x9, x5, x20
adc x8, x15, x10
extr x24, x17, x25, #63
extr x23, x25, x22, #63
lsr x7, x13, #63
extr x28, x11, x21, #63
extr x12, x21, x17, #63
extr x1, x13, x11, #63
stp x2, x16, [x0, #352]
lsl x20, x22, #1
stp x9, x8, [x0, #368]
umulh x5, x4, x4
umulh x15, x6, x6
mul x25, x3, x3
mul x17, x4, x4
mul x21, x14, x14
umulh x11, x3, x3
umulh x13, x14, x14
mul x2, x6, x6
adds x16, x20, x15
adcs x22, x23, x17
adcs x8, x24, x5
adcs x9, x12, x25
adcs x4, x28, x11
adcs x3, x1, x21
adc x14, x7, x13
ldp x6, x20, [x0, #480]
ldp x15, x17, [x0, #464]
ldp x23, x5, [x0, #448]
ldp x24, x25, [x0, #496]
subs x12, x23, x6
sbcs x28, x5, x20
sbcs x11, x15, x24
sbcs x1, x17, x25
csel x21, x10, x27, hs
mul x13, x27, x4
mul x7, x27, x14
mul x6, x27, x3
umulh x23, x27, x14
umulh x20, x27, x3
mul x5, x27, x9
umulh x15, x27, x4
umulh x24, x27, x9
adds x17, x2, x5
adcs x25, x16, x13
adcs x14, x22, x6
adcs x3, x8, x7
adc x4, x23, x10
subs x9, x12, x21
sbcs x5, x28, x10
sbcs x2, x11, x10
sbc x16, x1, x10
adds x13, x3, x20
adc x22, x4, x10
umulh x6, x9, x2
mul x7, x9, x2
umulh x8, x9, x16
umulh x23, x9, x5
mul x21, x9, x16
mul x12, x5, x16
extr x28, x22, x13, #63
and x11, x13, #0x7fffffffffffffff
umulh x1, x5, x16
mul x3, x5, x2
mul x20, x28, x26
umulh x4, x2, x16
umulh x22, x5, x2
mul x13, x2, x16
adds x28, x17, x20
adcs x17, x25, x24
adcs x20, x14, x15
adc x25, x11, x10
adds x24, x7, x23
adcs x14, x21, x6
adc x15, x8, x10
mul x11, x9, x5
stp x28, x17, [x0, #384]
stp x20, x25, [x0, #400]
adds x7, x14, x3
adcs x23, x15, x12
adc x21, x1, x10
umulh x6, x16, x16
mul x8, x16, x16
mul x28, x5, x5
umulh x17, x5, x5
umulh x20, x9, x9
mul x25, x2, x2
umulh x14, x2, x2
extr x3, x24, x11, #63
lsl x15, x11, #1
adds x12, x23, x22
adcs x1, x21, x13
adc x16, x4, x10
extr x5, x7, x24, #63
mul x2, x9, x9
lsr x11, x16, #63
extr x22, x1, x12, #63
extr x23, x16, x1, #63
extr x21, x12, x7, #63
adds x13, x15, x20
adcs x4, x3, x28
adcs x24, x5, x17
adcs x9, x21, x25
adcs x1, x22, x14
adcs x16, x23, x8
adc x12, x11, x6
ldp x7, x15, [x0, #464]
ldp x20, x3, [x0, #448]
ldp x28, x5, [x0, #480]
ldp x17, x25, [x0, #496]
adds x21, x20, x28
adcs x14, x3, x5
adcs x22, x7, x17
adcs x8, x15, x25
csel x23, x27, x10, hs
mul x6, x27, x12
mul x11, x27, x16
umulh x20, x27, x12
mul x28, x27, x1
umulh x3, x27, x16
mul x5, x27, x9
umulh x7, x27, x1
umulh x17, x27, x9
adds x15, x2, x5
adcs x25, x13, x28
adcs x12, x4, x11
adcs x16, x24, x6
adc x1, x20, x10
adds x9, x21, x23
adcs x5, x14, x10
adc x2, x22, x10
umulh x13, x9, x5
mul x28, x9, x2
umulh x11, x9, x8
adds x4, x16, x3
adc x6, x1, x10
umulh x24, x9, x2
mul x20, x9, x8
mul x21, x5, x2
umulh x23, x5, x8
mul x14, x5, x8
mul x22, x9, x5
extr x3, x6, x4, #63
and x16, x4, #0x7fffffffffffffff
umulh x1, x2, x8
umulh x6, x5, x2
mul x4, x3, x26
adds x3, x28, x13
adcs x28, x20, x24
adc x13, x11, x10
mul x20, x2, x8
adds x24, x15, x4
adcs x11, x25, x17
adcs x15, x12, x7
adc x4, x16, x10
adds x25, x28, x21
adcs x17, x13, x14
adc x12, x23, x10
stp x24, x11, [x0, #192]
stp x15, x4, [x0, #208]
umulh x7, x9, x9
mul x16, x2, x2
umulh x28, x2, x2
adds x21, x17, x6
adcs x13, x12, x20
adc x14, x1, x10
umulh x23, x5, x5
lsl x24, x22, #1
extr x11, x3, x22, #63
mul x15, x8, x8
umulh x4, x8, x8
mul x2, x5, x5
extr x17, x25, x3, #63
mul x6, x9, x9
lsr x12, x14, #63
extr x20, x21, x25, #63
extr x1, x14, x13, #63
extr x22, x13, x21, #63
adds x8, x24, x7
adcs x5, x11, x2
adcs x3, x17, x23
adcs x9, x20, x16
adcs x25, x22, x28
adcs x14, x1, x15
adc x21, x12, x4
ldp x13, x24, [x0, #192]
ldp x7, x11, [x0, #208]
ldr x2, [x0, #64]
mul x17, x2, x24
mul x23, x2, x7
mul x20, x2, x11
umulh x16, x27, x21
mul x28, x27, x21
mul x22, x27, x9
umulh x15, x2, x13
umulh x1, x27, x9
mul x4, x27, x14
umulh x12, x27, x14
mul x21, x27, x25
umulh x9, x2, x24
umulh x14, x27, x25
adds x25, x6, x22
adcs x22, x8, x21
adcs x6, x5, x4
adcs x8, x3, x28
adc x21, x16, x10
umulh x4, x2, x7
umulh x5, x2, x11
ldr x3, [x0, #72]
mul x28, x2, x13
adds x16, x17, x15
adcs x2, x23, x9
adcs x15, x20, x4
adc x17, x5, x10
adds x23, x8, x12
adc x9, x21, x10
mul x20, x3, x24
mul x4, x3, x11
mul x5, x3, x7
mul x12, x3, x13
extr x8, x9, x23, #63
and x21, x23, #0x7fffffffffffffff
mul x9, x8, x26
adds x23, x16, x12
adcs x8, x2, x20
adcs x12, x15, x5
adcs x16, x17, x4
adc x20, x10, x10
adds x2, x25, x9
adcs x15, x22, x1
adcs x5, x6, x14
adc x17, x21, x10
umulh x4, x3, x13
umulh x25, x3, x11
umulh x9, x3, x24
umulh x22, x3, x7
stp x2, x15, [x0, #160]
stp x5, x17, [x0, #176]
ldr x1, [x0, #80]
adds x14, x8, x4
adcs x6, x12, x9
adcs x21, x16, x22
adc x3, x20, x25
ldr x2, [x0, #88]
mul x15, x1, x13
mul x17, x1, x24
mul x5, x1, x7
umulh x8, x1, x11
umulh x4, x1, x24
mul x12, x1, x11
umulh x9, x1, x13
umulh x16, x1, x7
mul x22, x2, x13
umulh x20, x2, x13
mul x25, x2, x24
umulh x1, x2, x24
mul x13, x2, x11
adds x24, x14, x15
adcs x14, x6, x17
adcs x15, x21, x5
adcs x6, x3, x12
adc x17, x10, x10
umulh x21, x2, x11
mul x5, x2, x7
umulh x12, x2, x7
adds x3, x14, x9
adcs x11, x15, x4
adcs x7, x6, x16
adc x2, x17, x8
adds x14, x3, x22
adcs x9, x11, x25
adcs x15, x7, x5
adcs x4, x2, x13
adc x16, x10, x10
ldp x6, x8, [x0, #352]
ldp x17, x3, [x0, #384]
ldp x22, x25, [x0, #368]
adds x11, x9, x20
adcs x5, x15, x1
adcs x7, x4, x12
adc x13, x16, x21
ldp x2, x20, [x0, #400]
umulh x9, x27, x13
mul x1, x27, x13
mul x15, x27, x7
umulh x12, x27, x7
subs x4, x6, x17
sbcs x21, x8, x3
sbcs x16, x22, x2
sbcs x13, x25, x20
csel x7, x10, x27, hs
mul x17, x27, x5
mul x6, x27, x11
umulh x3, x27, x5
umulh x8, x27, x11
adds x22, x28, x6
adcs x2, x23, x17
adcs x25, x24, x15
adcs x20, x14, x1
adc x5, x9, x10
ldp x11, x6, [x0, #384]
subs x28, x4, x7
sbcs x17, x21, x10
sbcs x23, x16, x10
sbc x24, x13, x10
ldr x15, [x0, #352]
ldp x1, x14, [x0, #400]
adds x9, x20, x12
adc x7, x5, x10
stp x23, x24, [x0, #432]
stp x28, x17, [x0, #416]
mul x4, x15, x6
mul x21, x15, x14
mul x16, x15, x1
mul x13, x15, x11
extr x20, x7, x9, #63
umulh x12, x15, x11
and x5, x9, #0x7fffffffffffffff
umulh x23, x15, x6
mul x24, x20, x26
umulh x28, x15, x1
adds x17, x22, x24
adcs x7, x2, x8
adcs x9, x25, x3
adc x20, x5, x10
umulh x22, x15, x14
adds x24, x4, x12
adcs x2, x16, x23
adcs x8, x21, x28
adc x25, x22, x10
stp x9, x20, [x0, #208]
stp x17, x7, [x0, #192]
ldr x3, [x0, #360]
ldr x5, [x0, #368]
mul x15, x3, x11
mul x12, x3, x6
mul x4, x3, x14
mul x23, x3, x1
umulh x16, x3, x6
umulh x28, x3, x11
umulh x21, x3, x14
umulh x22, x3, x1
mul x9, x5, x14
mul x20, x5, x1
mul x17, x5, x11
adds x7, x24, x15
adcs x3, x2, x12
adcs x15, x8, x23
adcs x24, x25, x4
adc x12, x10, x10
mul x2, x5, x6
ldr x23, [x0, #376]
umulh x8, x5, x11
umulh x4, x5, x6
adds x25, x3, x28
adcs x28, x15, x16
adcs x3, x24, x22
adc x16, x12, x21
umulh x15, x5, x14
umulh x24, x5, x1
mul x22, x23, x1
umulh x12, x23, x1
umulh x21, x23, x6
mul x5, x23, x6
umulh x1, x23, x11
mul x6, x23, x11
adds x11, x25, x17
adcs x17, x28, x2
adcs x25, x3, x20
adcs x2, x16, x9
adc x28, x10, x10
mul x3, x23, x14
umulh x20, x23, x14
adds x16, x17, x8
adcs x9, x25, x4
adcs x14, x2, x24
adc x23, x28, x15
adds x17, x16, x6
adcs x8, x9, x5
adcs x25, x14, x22
adcs x4, x23, x3
adc x2, x10, x10
ldp x24, x28, [x0, #416]
ldp x15, x16, [x0, #368]
ldp x6, x9, [x0, #352]
adds x5, x8, x1
adcs x14, x25, x21
adcs x22, x4, x12
adc x3, x2, x20
ldp x23, x8, [x0, #432]
movz x1, #56129, lsl #0
movk x1, #1, lsl #16
mul x25, x24, x1
umulh x21, x27, x3
mul x12, x27, x3
mul x4, x27, x14
umulh x20, x27, x14
umulh x2, x27, x22
mul x3, x27, x22
mul x14, x27, x5
umulh x22, x27, x5
adds x5, x13, x14
adcs x13, x7, x4
adcs x14, x11, x3
adcs x7, x17, x12
adc x4, x21, x10
umulh x3, x24, x1
umulh x11, x8, x1
mul x17, x8, x1
mul x12, x23, x1
umulh x21, x23, x1
mul x24, x28, x1
umulh x8, x28, x1
adds x23, x6, x25
adcs x28, x9, x24
adcs x1, x15, x12
adcs x6, x16, x17
adc x25, x11, x10
adds x9, x7, x2
adc x24, x4, x10
extr x12, x24, x9, #63
and x15, x9, #0x7fffffffffffffff
mul x17, x12, x26
adds x16, x6, x6
adc x11, x25, x25
adds x7, x5, x17
adcs x2, x13, x22
adcs x4, x14, x20
adc x24, x15, x10
mul x9, x11, x26
lsr x12, x16, #1
adds x6, x23, x9
adcs x25, x28, x3
adcs x5, x1, x8
adc x17, x12, x21
stp x4, x24, [x0, #112]
stp x7, x2, [x0, #96]
ldr x22, [x0, #416]
ldr x13, [x0, #424]
stp x6, x25, [x0, #128]
stp x5, x17, [x0, #144]
ldp x14, x20, [x0, #128]
ldp x15, x11, [x0, #144]
ldr x16, [x0, #432]
umulh x23, x22, x14
umulh x9, x22, x15
mul x3, x22, x11
umulh x28, x22, x20
mul x8, x22, x15
umulh x1, x22, x11
mul x21, x13, x20
mul x12, x22, x20
mul x4, x13, x14
mul x24, x13, x15
mul x7, x13, x11
umulh x2, x13, x14
umulh x25, x13, x11
umulh x6, x13, x20
umulh x5, x13, x15
mul x17, x22, x14
mul x13, x16, x11
adds x22, x12, x23
adcs x12, x8, x28
adcs x23, x3, x9
adc x8, x1, x10
mul x28, x16, x14
mul x3, x16, x15
mul x9, x16, x20
adds x1, x22, x4
adcs x22, x12, x21
adcs x4, x23, x24
adcs x12, x8, x7
adc x21, x10, x10
umulh x23, x16, x20
umulh x24, x16, x11
umulh x7, x16, x15
umulh x8, x16, x14
adds x16, x22, x2
adcs x22, x4, x6
adcs x2, x12, x5
adc x4, x21, x25
ldr x6, [x0, #440]
adds x5, x16, x28
adcs x12, x22, x9
adcs x25, x2, x3
adcs x21, x4, x13
adc x16, x10, x10
mul x28, x6, x15
umulh x9, x6, x15
mul x22, x6, x11
umulh x3, x6, x11
mul x2, x6, x20
umulh x13, x6, x20
mul x4, x6, x14
umulh x15, x6, x14
adds x11, x12, x8
adcs x20, x25, x23
adcs x6, x21, x7
adc x14, x16, x24
adds x8, x11, x4
adcs x12, x20, x2
adcs x23, x6, x28
adcs x25, x14, x22
adc x7, x10, x10
adds x21, x12, x15
adcs x24, x23, x13
adcs x16, x25, x9
adc x4, x7, x3
umulh x11, x27, x4
mul x2, x27, x24
mul x20, x27, x21
mul x28, x27, x16
mul x6, x27, x4
umulh x22, x27, x16
umulh x14, x27, x21
umulh x15, x27, x24
adds x12, x17, x20
adcs x13, x1, x2
adcs x23, x5, x28
adcs x25, x8, x6
adc x9, x11, x10
adds x7, x25, x22
adc x3, x9, x10
extr x4, x3, x7, #63
and x16, x7, #0x7fffffffffffffff
mul x21, x4, x26
adds x24, x12, x21
adcs x17, x13, x14
adcs x20, x23, x15
adc x1, x16, x10
stp x24, x17, [x0, #128]
stp x20, x1, [x0, #144]
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
.globl lab_sc_o1_22_15_0
lab_sc_o1_22_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
ldr x17, [x0, #320]
ldr x1, [x0, #328]
umulh x12, x17, x9
umulh x14, x17, x7
umulh x20, x17, x16
umulh x13, x17, x21
mul x4, x17, x7
mul x22, x17, x16
mul x6, x17, x21
mul x2, x1, x9
mul x11, x1, x7
mul x15, x1, x16
mul x8, x17, x9
mul x28, x1, x21
umulh x23, x1, x9
umulh x25, x1, x7
adds x24, x4, x12
adcs x3, x22, x14
adcs x5, x6, x20
adc x17, x13, x10
umulh x4, x1, x16
umulh x12, x1, x21
ldr x22, [x0, #336]
adds x14, x24, x2
adcs x6, x3, x11
adcs x20, x5, x15
adcs x13, x17, x28
adc x1, x10, x10
mul x2, x22, x9
mul x24, x22, x7
mul x3, x22, x16
mul x11, x22, x21
umulh x5, x22, x9
umulh x15, x22, x7
adds x17, x6, x23
adcs x28, x20, x25
adcs x6, x13, x4
adc x23, x1, x12
umulh x20, x22, x16
umulh x25, x22, x21
ldr x13, [x0, #344]
adds x4, x17, x2
adcs x12, x28, x24
adcs x1, x6, x3
adcs x22, x23, x11
adc x17, x10, x10
mul x2, x13, x9
umulh x28, x13, x9
mul x24, x13, x7
umulh x3, x13, x7
mul x6, x13, x16
mul x11, x13, x21
adds x23, x12, x5
adcs x9, x1, x15
adcs x7, x22, x20
adc x12, x17, x25
umulh x5, x13, x16
umulh x15, x13, x21
adds x1, x23, x2
adcs x20, x9, x24
adcs x22, x7, x6
adcs x25, x12, x11
adc x17, x10, x10
adds x16, x20, x28
adcs x21, x22, x3
adcs x13, x25, x5
adc x2, x17, x15
umulh x23, x27, x2
mul x24, x27, x16
mul x9, x27, x21
mul x6, x27, x13
mul x7, x27, x2
umulh x11, x27, x13
umulh x12, x27, x16
umulh x28, x27, x21
adds x20, x8, x24
adcs x3, x14, x9
adcs x22, x4, x6
adcs x5, x1, x7
adc x25, x23, x10
ldp x17, x15, [x0, #256]
ldp x2, x13, [x0, #272]
ldr x16, [x0, #288]
adds x21, x5, x11
adc x24, x25, x10
mul x8, x16, x15
mul x14, x16, x2
mul x9, x16, x13
mul x4, x16, x17
extr x6, x24, x21, #63
umulh x7, x16, x17
and x1, x21, #0x7fffffffffffffff
umulh x23, x16, x15
mul x5, x6, x26
umulh x11, x16, x2
adds x25, x20, x5
adcs x24, x3, x12
adcs x21, x22, x28
adc x6, x1, x10
umulh x20, x16, x13
adds x5, x8, x7
adcs x3, x14, x23
adcs x12, x9, x11
adc x22, x20, x10
stp x25, x24, [x0, #448]
stp x21, x6, [x0, #464]
ldr x28, [x0, #296]
mul x1, x28, x17
mul x16, x28, x15
mul x7, x28, x2
mul x8, x28, x13
umulh x23, x28, x17
umulh x14, x28, x15
umulh x11, x28, x2
umulh x9, x28, x13
ldr x20, [x0, #304]
adds x25, x5, x1
adcs x24, x3, x16
adcs x21, x12, x7
adcs x6, x22, x8
adc x28, x10, x10
mul x1, x20, x17
mul x5, x20, x15
mul x16, x20, x2
mul x3, x20, x13
umulh x7, x20, x17
umulh x12, x20, x15
adds x8, x24, x23
adcs x22, x21, x14
adcs x23, x6, x11
adc x24, x28, x9
umulh x14, x20, x2
umulh x21, x20, x13
ldr x6, [x0, #312]
adds x11, x8, x1
adcs x28, x22, x5
adcs x9, x23, x16
adcs x20, x24, x3
adc x1, x10, x10
mul x8, x6, x17
umulh x5, x6, x17
mul x22, x6, x15
umulh x23, x6, x15
mul x16, x6, x2
mul x24, x6, x13
adds x3, x28, x7
adcs x17, x9, x12
adcs x15, x20, x14
adc x28, x1, x21
umulh x7, x6, x2
umulh x9, x6, x13
adds x12, x3, x8
adcs x20, x17, x22
adcs x14, x15, x16
adcs x1, x28, x24
adc x21, x10, x10
adds x2, x20, x5
adcs x13, x14, x23
adcs x6, x1, x7
adc x3, x21, x9
umulh x8, x27, x3
mul x17, x27, x2
mul x22, x27, x13
mul x15, x27, x6
mul x16, x27, x3
umulh x24, x27, x6
umulh x28, x27, x2
umulh x20, x27, x13
adds x5, x4, x17
adcs x14, x25, x22
adcs x23, x11, x15
adcs x7, x12, x16
adc x1, x8, x10
ldp x9, x21, [x0, #224]
ldp x3, x6, [x0, #240]
adds x2, x7, x24
adc x13, x1, x10
umulh x4, x9, x21
umulh x17, x9, x3
mul x25, x9, x3
mul x22, x9, x6
mul x15, x9, x21
extr x11, x13, x2, #63
umulh x12, x9, x6
and x16, x2, #0x7fffffffffffffff
mul x8, x21, x3
mul x7, x11, x26
mul x24, x21, x6
adds x1, x5, x7
adcs x13, x14, x28
adcs x2, x23, x20
adc x11, x16, x10
umulh x5, x21, x6
umulh x7, x21, x3
umulh x28, x3, x6
mul x14, x3, x6
stp x1, x13, [x0, #480]
adds x23, x25, x4
adcs x20, x22, x17
adc x16, x12, x10
stp x2, x11, [x0, #496]
umulh x1, x9, x9
mul x13, x21, x21
lsl x25, x15, #1
mul x4, x9, x9
adds x22, x20, x8
adcs x17, x16, x24
adc x12, x5, x10
umulh x2, x21, x21
umulh x11, x3, x3
mul x9, x3, x3
extr x20, x23, x15, #63
adds x8, x17, x7
adcs x16, x12, x14
adc x24, x28, x10
umulh x5, x6, x6
mul x21, x6, x6
extr x3, x22, x23, #63
lsr x15, x24, #63
extr x17, x24, x16, #63
extr x7, x16, x8, #63
extr x12, x8, x22, #63
adds x14, x25, x1
adcs x28, x20, x13
adcs x6, x3, x2
adcs x23, x12, x9
adcs x24, x7, x11
adcs x16, x17, x21
adc x8, x15, x5
umulh x22, x27, x8
mul x25, x27, x23
mul x1, x27, x24
mul x20, x27, x16
mul x13, x27, x8
umulh x3, x27, x16
umulh x2, x27, x23
umulh x12, x27, x24
adds x9, x4, x25
adcs x11, x14, x1
adcs x7, x28, x20
adcs x21, x6, x13
adc x17, x22, x10
ldp x5, x15, [x0, #256]
ldp x8, x16, [x0, #272]
adds x23, x21, x3
adc x24, x17, x10
umulh x25, x5, x15
umulh x4, x5, x8
mul x14, x5, x8
mul x1, x5, x16
mul x20, x5, x15
extr x28, x24, x23, #63
umulh x13, x5, x16
and x6, x23, #0x7fffffffffffffff
mul x22, x15, x8
mul x3, x28, x26
mul x21, x15, x16
adds x17, x9, x3
adcs x24, x11, x2
adcs x23, x7, x12
adc x28, x6, x10
umulh x9, x15, x16
umulh x3, x15, x8
umulh x11, x8, x16
mul x2, x8, x16
stp x17, x24, [x0, #352]
adds x12, x14, x25
adcs x7, x1, x4
adc x6, x13, x10
stp x23, x28, [x0, #368]
umulh x17, x5, x5
mul x24, x15, x15
lsl x25, x20, #1
mul x14, x5, x5
adds x4, x7, x22
adcs x1, x6, x21
adc x13, x9, x10
umulh x28, x15, x15
umulh x23, x8, x8
mul x5, x8, x8
extr x7, x12, x20, #63
adds x22, x1, x3
adcs x6, x13, x2
adc x21, x11, x10
umulh x9, x16, x16
mul x15, x16, x16
extr x8, x4, x12, #63
lsr x20, x21, #63
extr x3, x21, x6, #63
extr x1, x6, x22, #63
extr x13, x22, x4, #63
adds x2, x25, x17
adcs x11, x7, x24
adcs x16, x8, x28
adcs x12, x13, x5
adcs x21, x1, x23
adcs x6, x3, x15
adc x4, x20, x9
umulh x22, x27, x4
mul x25, x27, x12
mul x17, x27, x21
mul x24, x27, x6
mul x7, x27, x4
umulh x28, x27, x6
umulh x8, x27, x12
umulh x5, x27, x21
adds x13, x14, x25
adcs x1, x2, x17
adcs x23, x11, x24
adcs x3, x16, x7
adc x15, x22, x10
ldp x9, x20, [x0, #448]
ldp x4, x6, [x0, #464]
ldp x12, x21, [x0, #480]
ldp x25, x14, [x0, #496]
adds x2, x3, x28
adc x17, x15, x10
subs x11, x9, x12
sbcs x24, x20, x21
sbcs x7, x4, x25
sbcs x16, x6, x14
csel x22, x10, x27, hs
extr x3, x17, x2, #63
and x28, x2, #0x7fffffffffffffff
mul x15, x3, x26
adds x12, x13, x15
adcs x9, x1, x8
adcs x21, x23, x5
adc x20, x28, x10
subs x4, x11, x22
sbcs x25, x24, x10
sbcs x6, x7, x10
sbc x14, x16, x10
stp x12, x9, [x0, #384]
stp x21, x20, [x0, #400]
umulh x17, x4, x25
umulh x2, x4, x6
umulh x3, x4, x14
mul x13, x4, x6
mul x15, x4, x14
umulh x1, x25, x14
mul x8, x25, x6
mul x23, x25, x14
umulh x5, x25, x6
umulh x28, x6, x14
mul x22, x6, x14
mul x11, x4, x25
adds x24, x13, x17
adcs x7, x15, x2
adc x16, x3, x10
umulh x12, x4, x4
mul x9, x25, x25
lsl x21, x11, #1
mul x20, x4, x4
adds x13, x7, x8
adcs x17, x16, x23
adc x15, x1, x10
umulh x2, x25, x25
umulh x3, x6, x6
mul x4, x6, x6
extr x7, x24, x11, #63
adds x8, x17, x5
adcs x16, x15, x22
adc x23, x28, x10
umulh x1, x14, x14
mul x25, x14, x14
extr x6, x13, x24, #63
lsr x11, x23, #63
extr x5, x23, x16, #63
extr x17, x16, x8, #63
extr x15, x8, x13, #63
adds x22, x21, x12
adcs x28, x7, x9
adcs x14, x6, x2
adcs x24, x15, x4
adcs x23, x17, x3
adcs x16, x5, x25
adc x8, x11, x1
umulh x13, x27, x8
mul x21, x27, x24
mul x12, x27, x23
mul x7, x27, x16
mul x9, x27, x8
umulh x6, x27, x16
umulh x2, x27, x24
umulh x4, x27, x23
adds x15, x20, x21
adcs x3, x22, x12
adcs x17, x28, x7
adcs x25, x14, x9
adc x5, x13, x10
ldp x1, x11, [x0, #448]
ldp x8, x16, [x0, #464]
ldp x24, x23, [x0, #480]
ldp x21, x20, [x0, #496]
adds x22, x25, x6
adc x12, x5, x10
adds x7, x1, x24
adcs x28, x11, x23
adcs x9, x8, x21
adcs x14, x16, x20
csel x13, x27, x10, hs
extr x6, x12, x22, #63
and x25, x22, #0x7fffffffffffffff
mul x5, x6, x26
adds x1, x15, x5
adcs x24, x3, x2
adcs x11, x17, x4
adc x23, x25, x10
adds x8, x7, x13
adcs x21, x28, x10
adc x16, x9, x10
stp x1, x24, [x0, #192]
stp x11, x23, [x0, #208]
umulh x20, x8, x21
umulh x12, x8, x16
umulh x22, x8, x14
mul x6, x8, x16
mul x15, x8, x14
umulh x5, x21, x14
mul x3, x21, x16
mul x2, x21, x14
umulh x17, x21, x16
umulh x4, x16, x14
mul x25, x16, x14
mul x7, x8, x21
adds x13, x6, x20
adcs x28, x15, x12
adc x9, x22, x10
umulh x1, x8, x8
mul x24, x21, x21
lsl x11, x7, #1
mul x23, x8, x8
adds x6, x28, x3
adcs x20, x9, x2
adc x15, x5, x10
umulh x12, x21, x21
umulh x22, x16, x16
mul x8, x16, x16
extr x28, x13, x7, #63
adds x3, x20, x17
adcs x9, x15, x25
adc x2, x4, x10
umulh x5, x14, x14
mul x21, x14, x14
extr x16, x6, x13, #63
lsr x7, x2, #63
extr x20, x2, x9, #63
extr x17, x9, x3, #63
extr x15, x3, x6, #63
adds x25, x11, x1
adcs x4, x28, x24
adcs x14, x16, x12
adcs x13, x15, x8
adcs x2, x17, x22
adcs x9, x20, x21
adc x3, x7, x5
umulh x6, x27, x3
mul x11, x27, x13
mul x1, x27, x2
mul x28, x27, x9
mul x24, x27, x3
umulh x16, x27, x9
umulh x12, x27, x13
umulh x15, x27, x2
adds x8, x23, x11
adcs x22, x25, x1
adcs x17, x4, x28
adcs x21, x14, x24
adc x20, x6, x10
ldp x5, x7, [x0, #192]
ldp x3, x9, [x0, #208]
ldr x13, [x0, #64]
adds x2, x21, x16
adc x11, x20, x10
mul x23, x13, x7
mul x25, x13, x3
mul x1, x13, x9
mul x28, x13, x5
extr x4, x11, x2, #63
umulh x14, x13, x5
and x24, x2, #0x7fffffffffffffff
umulh x6, x13, x7
mul x16, x4, x26
umulh x21, x13, x3
adds x20, x8, x16
adcs x11, x22, x12
adcs x2, x17, x15
adc x4, x24, x10
umulh x8, x13, x9
adds x16, x23, x14
adcs x22, x25, x6
adcs x12, x1, x21
adc x15, x8, x10
stp x20, x11, [x0, #160]
stp x2, x4, [x0, #176]
ldr x17, [x0, #72]
mul x24, x17, x5
mul x13, x17, x7
mul x14, x17, x3
mul x23, x17, x9
umulh x25, x17, x5
umulh x6, x17, x7
umulh x1, x17, x3
umulh x21, x17, x9
ldr x8, [x0, #80]
adds x20, x16, x24
adcs x11, x22, x13
adcs x4, x12, x14
adcs x2, x15, x23
adc x17, x10, x10
mul x24, x8, x5
mul x16, x8, x7
mul x13, x8, x3
mul x22, x8, x9
umulh x12, x8, x5
umulh x14, x8, x7
adds x15, x11, x25
adcs x23, x4, x6
adcs x11, x2, x1
adc x25, x17, x21
umulh x4, x8, x3
umulh x6, x8, x9
ldr x2, [x0, #88]
adds x1, x15, x24
adcs x17, x23, x16
adcs x21, x11, x13
adcs x8, x25, x22
adc x15, x10, x10
mul x24, x2, x5
umulh x23, x2, x5
mul x16, x2, x7
umulh x11, x2, x7
mul x13, x2, x3
mul x22, x2, x9
adds x25, x17, x12
adcs x5, x21, x14
adcs x7, x8, x4
adc x17, x15, x6
umulh x12, x2, x3
umulh x21, x2, x9
adds x14, x25, x24
adcs x4, x5, x16
adcs x8, x7, x13
adcs x6, x17, x22
adc x15, x10, x10
adds x3, x4, x23
adcs x9, x8, x11
adcs x2, x6, x12
adc x25, x15, x21
umulh x24, x27, x25
mul x16, x27, x3
mul x5, x27, x9
mul x13, x27, x2
mul x7, x27, x25
umulh x22, x27, x2
umulh x17, x27, x3
umulh x23, x27, x9
adds x4, x28, x16
adcs x11, x20, x5
adcs x8, x1, x13
adcs x12, x14, x7
adc x6, x24, x10
ldp x21, x15, [x0, #352]
ldp x25, x2, [x0, #368]
ldp x3, x9, [x0, #384]
ldp x16, x28, [x0, #400]
adds x5, x12, x22
adc x20, x6, x10
subs x1, x21, x3
sbcs x13, x15, x9
sbcs x7, x25, x16
sbcs x14, x2, x28
csel x24, x10, x27, hs
extr x12, x20, x5, #63
and x22, x5, #0x7fffffffffffffff
mul x6, x12, x26
adds x3, x4, x6
adcs x21, x11, x17
adcs x9, x8, x23
adc x15, x22, x10
subs x25, x1, x24
sbcs x16, x13, x10
sbcs x2, x7, x10
sbc x28, x14, x10
stp x3, x21, [x0, #192]
stp x9, x15, [x0, #208]
ldp x20, x5, [x0, #384]
ldp x12, x4, [x0, #400]
stp x2, x28, [x0, #432]
stp x25, x16, [x0, #416]
ldr x6, [x0, #352]
ldr x11, [x0, #360]
umulh x17, x6, x20
umulh x8, x6, x5
umulh x23, x6, x12
umulh x22, x6, x4
mul x24, x6, x5
mul x1, x6, x12
mul x13, x6, x4
mul x7, x11, x20
mul x14, x11, x5
mul x3, x11, x12
mul x21, x6, x20
mul x9, x11, x4
umulh x15, x11, x20
umulh x2, x11, x5
adds x28, x24, x17
adcs x25, x1, x8
adcs x16, x13, x23
adc x6, x22, x10
umulh x17, x11, x12
umulh x24, x11, x4
ldr x8, [x0, #368]
adds x1, x28, x7
adcs x23, x25, x14
adcs x13, x16, x3
adcs x22, x6, x9
adc x11, x10, x10
mul x7, x8, x20
mul x28, x8, x5
mul x14, x8, x12
mul x25, x8, x4
umulh x3, x8, x20
umulh x16, x8, x5
adds x9, x23, x15
adcs x6, x13, x2
adcs x15, x22, x17
adc x23, x11, x24
umulh x2, x8, x12
umulh x13, x8, x4
ldr x22, [x0, #376]
adds x17, x9, x7
adcs x11, x6, x28
adcs x24, x15, x14
adcs x8, x23, x25
adc x7, x10, x10
mul x9, x22, x20
umulh x28, x22, x20
mul x6, x22, x5
umulh x15, x22, x5
mul x14, x22, x12
mul x23, x22, x4
adds x25, x11, x3
adcs x20, x24, x16
adcs x5, x8, x2
adc x11, x7, x13
umulh x3, x22, x12
umulh x24, x22, x4
adds x16, x25, x9
adcs x8, x20, x6
adcs x2, x5, x14
adcs x7, x11, x23
adc x13, x10, x10
adds x12, x8, x28
adcs x4, x2, x15
adcs x22, x7, x3
adc x25, x13, x24
umulh x9, x27, x25
mul x20, x27, x12
mul x6, x27, x4
mul x5, x27, x22
mul x14, x27, x25
umulh x23, x27, x22
umulh x11, x27, x12
umulh x8, x27, x4
adds x28, x21, x20
adcs x2, x1, x6
adcs x15, x17, x5
adcs x3, x16, x14
adc x7, x9, x10
ldp x24, x13, [x0, #432]
ldp x25, x22, [x0, #416]
movz x12, #56129, lsl #0
ldp x4, x21, [x0, #352]
ldp x20, x1, [x0, #368]
adds x6, x3, x23
adc x5, x7, x10
movk x12, #1, lsl #16
mul x17, x25, x12
extr x16, x5, x6, #63
mul x14, x22, x12
and x9, x6, #0x7fffffffffffffff
mul x3, x24, x12
mul x23, x16, x26
mul x7, x13, x12
adds x5, x28, x23
adcs x6, x2, x11
adcs x16, x15, x8
adc x28, x9, x10
umulh x23, x13, x12
adds x11, x4, x17
adcs x2, x21, x14
adcs x15, x20, x3
adcs x8, x1, x7
adc x9, x23, x10
stp x5, x6, [x0, #96]
stp x16, x28, [x0, #112]
umulh x13, x25, x12
umulh x4, x22, x12
umulh x17, x24, x12
ldr x21, [x0, #416]
adds x14, x8, x8
adc x3, x9, x9
mul x20, x3, x26
lsr x7, x14, #1
adds x1, x11, x20
adcs x23, x2, x13
adcs x5, x15, x4
adc x6, x7, x17
stp x1, x23, [x0, #128]
stp x5, x6, [x0, #144]
ldr x16, [x0, #424]
ldp x28, x25, [x0, #128]
ldp x22, x24, [x0, #144]
umulh x12, x21, x28
umulh x8, x21, x25
umulh x9, x21, x22
umulh x3, x21, x24
mul x14, x21, x25
mul x11, x21, x22
mul x20, x21, x24
mul x13, x16, x28
mul x2, x16, x25
mul x4, x16, x22
mul x15, x21, x28
mul x17, x16, x24
umulh x7, x16, x28
umulh x23, x16, x25
adds x1, x14, x12
adcs x5, x11, x8
adcs x6, x20, x9
adc x21, x3, x10
umulh x14, x16, x22
umulh x12, x16, x24
ldr x11, [x0, #432]
adds x8, x1, x13
adcs x20, x5, x2
adcs x9, x6, x4
adcs x3, x21, x17
adc x16, x10, x10
mul x1, x11, x28
mul x13, x11, x25
mul x5, x11, x22
mul x2, x11, x24
umulh x6, x11, x28
umulh x4, x11, x25
adds x17, x20, x7
adcs x21, x9, x23
adcs x20, x3, x14
adc x7, x16, x12
umulh x9, x11, x22
umulh x23, x11, x24
ldr x14, [x0, #440]
adds x3, x17, x1
adcs x12, x21, x13
adcs x16, x20, x5
adcs x11, x7, x2
adc x17, x10, x10
mul x1, x14, x28
umulh x13, x14, x28
mul x21, x14, x25
umulh x5, x14, x25
mul x20, x14, x22
mul x2, x14, x24
adds x7, x12, x6
adcs x28, x16, x4
adcs x25, x11, x9
adc x6, x17, x23
umulh x12, x14, x22
umulh x4, x14, x24
adds x16, x7, x1
adcs x9, x28, x21
adcs x11, x25, x20
adcs x23, x6, x2
adc x17, x10, x10
adds x22, x9, x13
adcs x14, x11, x5
adcs x24, x23, x12
adc x1, x17, x4
umulh x7, x27, x1
mul x21, x27, x22
mul x28, x27, x14
mul x20, x27, x24
mul x25, x27, x1
umulh x2, x27, x24
umulh x6, x27, x22
umulh x13, x27, x14
adds x9, x15, x21
adcs x5, x8, x28
adcs x11, x3, x20
adcs x23, x16, x25
adc x12, x7, x10
adds x17, x23, x2
adc x4, x12, x10
extr x1, x4, x17, #63
and x24, x17, #0x7fffffffffffffff
mul x22, x1, x26
adds x14, x9, x22
adcs x15, x5, x6
adcs x21, x11, x13
adc x8, x24, x10
stp x14, x15, [x0, #128]
stp x21, x8, [x0, #144]
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
.globl lab_sc_o1_22_15_1
lab_sc_o1_22_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
ldr x3, [x0, #320]
ldr x7, [x0, #328]
umulh x11, x3, x6
mul x4, x3, x15
umulh x8, x3, x15
mul x2, x3, x16
umulh x13, x3, x23
mul x17, x7, x16
umulh x5, x3, x16
mul x1, x3, x23
mul x9, x7, x23
mul x12, x7, x6
mul x21, x3, x6
umulh x20, x7, x6
umulh x22, x7, x16
mul x28, x7, x15
adds x24, x2, x11
adcs x25, x1, x5
adcs x14, x4, x13
adc x3, x8, x10
umulh x2, x7, x15
umulh x11, x7, x23
ldr x1, [x0, #336]
adds x5, x24, x12
adcs x4, x25, x17
adcs x13, x14, x9
adcs x8, x3, x28
adc x7, x10, x10
mul x12, x1, x6
mul x24, x1, x15
mul x25, x1, x16
mul x17, x1, x23
umulh x14, x1, x6
umulh x9, x1, x16
adds x3, x4, x20
adcs x28, x13, x22
adcs x4, x8, x11
adc x20, x7, x2
umulh x13, x1, x15
umulh x22, x1, x23
ldr x8, [x0, #344]
adds x11, x3, x12
adcs x2, x28, x25
adcs x7, x4, x17
adcs x1, x20, x24
adc x3, x10, x10
mul x12, x8, x6
umulh x28, x8, x6
mul x25, x8, x16
umulh x17, x8, x16
mul x4, x8, x15
mul x24, x8, x23
adds x20, x2, x14
adcs x6, x7, x9
adcs x16, x1, x22
adc x2, x3, x13
umulh x14, x8, x23
umulh x9, x8, x15
adds x7, x20, x12
adcs x22, x6, x25
adcs x1, x16, x24
adcs x13, x2, x4
adc x3, x10, x10
adds x23, x22, x28
adcs x15, x1, x17
adcs x8, x13, x14
adc x12, x3, x9
umulh x20, x27, x12
mul x25, x27, x23
mul x6, x27, x12
mul x24, x27, x15
mul x16, x27, x8
umulh x4, x27, x8
umulh x2, x27, x15
umulh x28, x27, x23
adds x22, x21, x25
adcs x17, x5, x24
adcs x1, x11, x16
adcs x14, x7, x6
adc x13, x20, x10
ldp x3, x9, [x0, #272]
ldp x12, x8, [x0, #256]
ldr x15, [x0, #288]
adds x23, x14, x4
adc x25, x13, x10
mul x21, x15, x8
mul x5, x15, x9
mul x24, x15, x3
mul x11, x15, x12
extr x16, x25, x23, #63
umulh x6, x15, x12
and x7, x23, #0x7fffffffffffffff
umulh x20, x15, x8
mul x14, x16, x26
umulh x4, x15, x3
adds x13, x22, x14
adcs x25, x17, x28
adcs x23, x1, x2
adc x16, x7, x10
umulh x22, x15, x9
adds x14, x21, x6
adcs x17, x24, x20
adcs x28, x5, x4
adc x1, x22, x10
stp x23, x16, [x0, #464]
stp x13, x25, [x0, #448]
ldr x2, [x0, #296]
mul x7, x2, x12
mul x15, x2, x8
mul x6, x2, x3
mul x21, x2, x9
umulh x20, x2, x9
ldr x24, [x0, #304]
umulh x4, x2, x3
umulh x5, x2, x12
umulh x22, x2, x8
adds x23, x14, x7
adcs x16, x17, x15
adcs x13, x28, x6
adcs x25, x1, x21
adc x2, x10, x10
mul x7, x24, x12
mul x14, x24, x3
mul x15, x24, x9
mul x17, x24, x8
umulh x6, x24, x12
umulh x28, x24, x8
adds x21, x16, x5
adcs x1, x13, x22
adcs x5, x25, x4
adc x16, x2, x20
umulh x22, x24, x3
umulh x13, x24, x9
ldr x25, [x0, #312]
adds x4, x21, x7
adcs x2, x1, x17
adcs x20, x5, x14
adcs x24, x16, x15
adc x7, x10, x10
mul x21, x25, x12
umulh x17, x25, x12
mul x1, x25, x9
umulh x5, x25, x8
mul x14, x25, x8
mul x16, x25, x3
adds x15, x2, x6
adcs x12, x20, x28
adcs x8, x24, x22
adc x2, x7, x13
umulh x6, x25, x3
umulh x20, x25, x9
adds x28, x15, x21
adcs x24, x12, x14
adcs x22, x8, x16
adcs x7, x2, x1
adc x13, x10, x10
adds x3, x24, x17
adcs x9, x22, x5
adcs x25, x7, x6
adc x15, x13, x20
umulh x21, x27, x15
mul x12, x27, x25
mul x14, x27, x9
mul x8, x27, x15
mul x16, x27, x3
umulh x1, x27, x25
umulh x2, x27, x9
umulh x24, x27, x3
adds x17, x11, x16
adcs x22, x23, x14
adcs x5, x4, x12
adcs x6, x28, x8
adc x7, x21, x10
ldp x20, x13, [x0, #224]
ldp x15, x25, [x0, #240]
adds x9, x6, x1
adc x3, x7, x10
mul x11, x20, x15
mul x16, x20, x25
umulh x23, x20, x13
umulh x14, x20, x15
mul x12, x20, x13
extr x4, x3, x9, #63
umulh x28, x20, x25
and x8, x9, #0x7fffffffffffffff
mul x21, x13, x15
mul x6, x4, x26
mul x1, x13, x25
adds x7, x17, x6
adcs x3, x22, x24
adcs x9, x5, x2
adc x4, x8, x10
umulh x17, x13, x25
umulh x6, x13, x15
umulh x24, x15, x25
mul x22, x15, x25
stp x7, x3, [x0, #480]
adds x5, x11, x23
adcs x2, x16, x14
adc x8, x28, x10
stp x9, x4, [x0, #496]
mul x7, x13, x13
umulh x3, x20, x20
lsl x11, x12, #1
mul x23, x20, x20
adds x16, x2, x21
adcs x14, x8, x1
adc x28, x17, x10
umulh x9, x13, x13
mul x4, x15, x15
umulh x20, x15, x15
extr x2, x5, x12, #63
adds x21, x14, x6
adcs x8, x28, x22
adc x1, x24, x10
umulh x17, x25, x25
mul x13, x25, x25
extr x15, x16, x5, #63
lsr x12, x1, #63
extr x14, x8, x21, #63
extr x6, x21, x16, #63
extr x28, x1, x8, #63
adds x22, x11, x3
adcs x24, x2, x7
adcs x25, x15, x9
adcs x5, x6, x4
adcs x21, x14, x20
adcs x16, x28, x13
adc x8, x12, x17
umulh x1, x27, x8
mul x11, x27, x5
mul x3, x27, x21
mul x2, x27, x16
mul x7, x27, x8
umulh x15, x27, x16
umulh x9, x27, x5
umulh x6, x27, x21
adds x4, x23, x11
adcs x20, x22, x3
adcs x14, x24, x2
adcs x13, x25, x7
adc x28, x1, x10
ldp x17, x12, [x0, #272]
ldp x8, x16, [x0, #256]
adds x5, x13, x15
adc x21, x28, x10
umulh x11, x8, x17
umulh x23, x8, x16
mul x22, x8, x17
mul x3, x8, x12
mul x2, x8, x16
extr x24, x21, x5, #63
umulh x7, x8, x12
and x25, x5, #0x7fffffffffffffff
mul x1, x16, x17
mul x15, x24, x26
mul x13, x16, x12
adds x28, x4, x15
adcs x21, x20, x9
adcs x5, x14, x6
adc x24, x25, x10
umulh x4, x16, x12
mul x15, x17, x12
umulh x20, x16, x17
umulh x9, x17, x12
stp x28, x21, [x0, #352]
adds x6, x22, x23
adcs x14, x3, x11
adc x25, x7, x10
stp x5, x24, [x0, #368]
umulh x28, x8, x8
mul x21, x16, x16
lsl x23, x2, #1
mul x22, x8, x8
adds x11, x14, x1
adcs x3, x25, x13
adc x7, x4, x10
umulh x24, x16, x16
mul x5, x17, x17
extr x8, x6, x2, #63
umulh x14, x17, x17
adds x1, x3, x20
adcs x25, x7, x15
adc x13, x9, x10
extr x4, x11, x6, #63
mul x16, x12, x12
umulh x2, x12, x12
lsr x17, x13, #63
extr x20, x25, x1, #63
extr x3, x1, x11, #63
extr x7, x13, x25, #63
adds x15, x23, x28
adcs x9, x8, x21
adcs x6, x4, x24
adcs x12, x3, x5
adcs x11, x20, x14
adcs x1, x7, x16
adc x25, x17, x2
umulh x13, x27, x25
mul x23, x27, x11
mul x28, x27, x25
mul x21, x27, x1
umulh x8, x27, x1
mul x24, x27, x12
umulh x4, x27, x11
umulh x5, x27, x12
adds x3, x22, x24
adcs x20, x15, x23
adcs x14, x9, x21
adcs x7, x6, x28
adc x16, x13, x10
ldp x2, x17, [x0, #480]
ldp x25, x1, [x0, #464]
ldp x11, x12, [x0, #448]
ldp x24, x22, [x0, #496]
adds x15, x7, x8
adc x23, x16, x10
subs x9, x11, x2
sbcs x21, x12, x17
sbcs x28, x25, x24
sbcs x6, x1, x22
csel x13, x10, x27, hs
extr x7, x23, x15, #63
and x8, x15, #0x7fffffffffffffff
mul x16, x7, x26
adds x2, x3, x16
adcs x11, x20, x5
adcs x17, x14, x4
adc x12, x8, x10
subs x25, x9, x13
sbcs x24, x21, x10
sbcs x1, x28, x10
sbc x22, x6, x10
stp x2, x11, [x0, #384]
stp x17, x12, [x0, #400]
umulh x23, x25, x24
umulh x15, x25, x1
mul x7, x25, x1
umulh x3, x25, x22
umulh x16, x24, x22
umulh x20, x1, x22
mul x5, x25, x22
mul x14, x24, x22
mul x4, x24, x1
umulh x8, x24, x1
mul x13, x1, x22
mul x9, x25, x24
adds x21, x7, x23
adcs x28, x5, x15
adc x6, x3, x10
mul x2, x24, x24
umulh x11, x25, x25
lsl x17, x9, #1
mul x12, x25, x25
adds x7, x28, x4
adcs x23, x6, x14
adc x5, x16, x10
umulh x15, x24, x24
mul x3, x1, x1
umulh x25, x1, x1
extr x28, x21, x9, #63
adds x4, x23, x8
adcs x6, x5, x13
adc x14, x20, x10
umulh x16, x22, x22
mul x24, x22, x22
extr x1, x7, x21, #63
lsr x9, x14, #63
extr x8, x6, x4, #63
extr x23, x14, x6, #63
extr x5, x4, x7, #63
adds x13, x17, x11
adcs x20, x28, x2
adcs x22, x1, x15
adcs x21, x5, x3
adcs x6, x8, x25
adcs x14, x23, x24
adc x4, x9, x16
umulh x7, x27, x4
mul x17, x27, x4
mul x11, x27, x14
mul x28, x27, x6
umulh x2, x27, x14
mul x1, x27, x21
umulh x15, x27, x6
umulh x3, x27, x21
adds x5, x12, x1
adcs x25, x13, x28
adcs x8, x20, x11
adcs x24, x22, x17
adc x23, x7, x10
ldp x16, x9, [x0, #464]
ldp x4, x14, [x0, #448]
ldp x6, x21, [x0, #480]
ldp x1, x12, [x0, #496]
adds x13, x24, x2
adc x28, x23, x10
adds x11, x4, x6
adcs x20, x14, x21
adcs x17, x16, x1
adcs x22, x9, x12
csel x7, x27, x10, hs
extr x2, x28, x13, #63
and x24, x13, #0x7fffffffffffffff
mul x23, x2, x26
adds x4, x5, x23
adcs x6, x25, x3
adcs x14, x8, x15
adc x21, x24, x10
adds x16, x11, x7
adcs x1, x20, x10
adc x9, x17, x10
stp x4, x6, [x0, #192]
stp x14, x21, [x0, #208]
mul x12, x16, x9
umulh x28, x16, x22
umulh x13, x16, x9
umulh x2, x16, x1
mul x5, x16, x22
mul x23, x1, x9
umulh x25, x1, x22
umulh x3, x9, x22
mul x8, x1, x22
mul x15, x16, x1
umulh x24, x1, x9
mul x11, x9, x22
adds x7, x12, x2
adcs x20, x5, x13
adc x17, x28, x10
umulh x4, x16, x16
lsl x6, x15, #1
mul x14, x1, x1
mul x21, x16, x16
adds x12, x20, x23
adcs x2, x17, x8
adc x5, x25, x10
mul x13, x9, x9
umulh x28, x9, x9
umulh x16, x1, x1
extr x20, x7, x15, #63
adds x23, x2, x24
adcs x17, x5, x11
adc x8, x3, x10
mul x25, x22, x22
umulh x9, x22, x22
extr x1, x12, x7, #63
lsr x15, x8, #63
extr x2, x23, x12, #63
extr x24, x8, x17, #63
extr x5, x17, x23, #63
adds x11, x6, x4
adcs x3, x20, x14
adcs x22, x1, x16
adcs x7, x2, x13
adcs x12, x5, x28
adcs x8, x24, x25
adc x23, x15, x9
umulh x17, x27, x23
mul x6, x27, x7
mul x4, x27, x8
mul x20, x27, x12
mul x14, x27, x23
umulh x1, x27, x8
umulh x16, x27, x7
umulh x2, x27, x12
adds x13, x21, x6
adcs x28, x11, x20
adcs x5, x3, x4
adcs x25, x22, x14
adc x24, x17, x10
ldp x9, x15, [x0, #192]
ldp x23, x8, [x0, #208]
ldr x7, [x0, #64]
adds x12, x25, x1
adc x6, x24, x10
mul x21, x7, x15
mul x11, x7, x23
mul x20, x7, x8
mul x4, x7, x9
extr x3, x6, x12, #63
umulh x22, x7, x9
and x14, x12, #0x7fffffffffffffff
umulh x17, x7, x15
mul x1, x3, x26
umulh x25, x7, x23
adds x24, x13, x1
adcs x6, x28, x16
adcs x12, x5, x2
adc x3, x14, x10
umulh x13, x7, x8
adds x1, x21, x22
adcs x28, x11, x17
adcs x16, x20, x25
adc x2, x13, x10
stp x24, x6, [x0, #160]
stp x12, x3, [x0, #176]
ldr x5, [x0, #72]
mul x14, x5, x9
mul x7, x5, x15
mul x22, x5, x8
mul x21, x5, x23
umulh x11, x5, x9
ldr x17, [x0, #80]
umulh x20, x5, x8
umulh x25, x5, x15
umulh x13, x5, x23
adds x24, x1, x14
adcs x6, x28, x7
adcs x3, x16, x21
adcs x12, x2, x22
adc x5, x10, x10
mul x14, x17, x9
mul x1, x17, x15
mul x7, x17, x23
umulh x28, x17, x15
mul x16, x17, x8
umulh x21, x17, x9
adds x2, x6, x11
adcs x22, x3, x25
adcs x6, x12, x13
adc x11, x5, x20
umulh x3, x17, x8
umulh x25, x17, x23
ldr x12, [x0, #88]
adds x13, x2, x14
adcs x5, x22, x1
adcs x20, x6, x7
adcs x17, x11, x16
adc x2, x10, x10
mul x14, x12, x9
umulh x22, x12, x9
mul x1, x12, x15
umulh x6, x12, x15
mul x7, x12, x8
mul x16, x12, x23
adds x11, x5, x21
adcs x9, x20, x28
adcs x15, x17, x25
adc x5, x2, x3
umulh x21, x12, x8
umulh x20, x12, x23
adds x28, x11, x14
adcs x25, x9, x1
adcs x17, x15, x16
adcs x3, x5, x7
adc x2, x10, x10
adds x8, x25, x22
adcs x23, x17, x6
adcs x12, x3, x20
adc x11, x2, x21
umulh x14, x27, x11
mul x1, x27, x12
mul x9, x27, x23
mul x16, x27, x11
mul x15, x27, x8
umulh x7, x27, x12
umulh x5, x27, x23
umulh x22, x27, x8
adds x25, x4, x15
adcs x6, x24, x9
adcs x17, x13, x1
adcs x20, x28, x16
adc x3, x14, x10
ldp x21, x2, [x0, #352]
ldp x11, x12, [x0, #384]
ldp x23, x8, [x0, #400]
ldp x15, x4, [x0, #368]
adds x9, x20, x7
adc x24, x3, x10
subs x13, x21, x11
sbcs x1, x2, x12
sbcs x16, x15, x23
sbcs x28, x4, x8
csel x14, x10, x27, hs
extr x20, x24, x9, #63
and x7, x9, #0x7fffffffffffffff
mul x3, x20, x26
adds x11, x25, x3
adcs x21, x6, x22
adcs x12, x17, x5
adc x2, x7, x10
subs x15, x13, x14
sbcs x23, x1, x10
sbcs x4, x16, x10
sbc x8, x28, x10
stp x11, x21, [x0, #192]
stp x12, x2, [x0, #208]
ldp x24, x9, [x0, #384]
ldr x20, [x0, #352]
stp x4, x8, [x0, #432]
stp x15, x23, [x0, #416]
ldp x25, x3, [x0, #400]
ldr x6, [x0, #360]
umulh x22, x20, x24
umulh x17, x20, x9
mul x5, x20, x9
umulh x7, x20, x3
mul x14, x20, x3
umulh x13, x20, x25
mul x1, x6, x9
mul x16, x6, x24
mul x28, x6, x25
mul x11, x20, x25
mul x21, x20, x24
mul x12, x6, x3
umulh x2, x6, x9
umulh x4, x6, x24
adds x8, x5, x22
adcs x15, x11, x17
adcs x23, x14, x13
adc x20, x7, x10
umulh x22, x6, x3
umulh x5, x6, x25
ldr x17, [x0, #368]
adds x11, x8, x16
adcs x13, x15, x1
adcs x14, x23, x28
adcs x7, x20, x12
adc x6, x10, x10
mul x16, x17, x24
mul x8, x17, x3
mul x1, x17, x25
mul x15, x17, x9
umulh x28, x17, x24
umulh x23, x17, x9
adds x12, x13, x4
adcs x20, x14, x2
adcs x4, x7, x5
adc x13, x6, x22
ldr x2, [x0, #376]
umulh x14, x17, x3
umulh x7, x17, x25
adds x5, x12, x16
adcs x6, x20, x15
adcs x22, x4, x1
adcs x17, x13, x8
adc x16, x10, x10
mul x12, x2, x25
umulh x15, x2, x9
mul x20, x2, x9
umulh x4, x2, x24
mul x1, x2, x24
mul x13, x2, x3
adds x8, x6, x28
adcs x9, x22, x23
adcs x24, x17, x7
adc x6, x16, x14
umulh x28, x2, x3
umulh x22, x2, x25
adds x23, x8, x1
adcs x17, x9, x20
adcs x7, x24, x12
adcs x16, x6, x13
adc x14, x10, x10
adds x3, x17, x4
adcs x25, x7, x15
adcs x2, x16, x22
adc x8, x14, x28
umulh x1, x27, x8
mul x9, x27, x8
mul x20, x27, x25
umulh x24, x27, x2
mul x12, x27, x3
mul x13, x27, x2
umulh x6, x27, x25
umulh x17, x27, x3
adds x4, x21, x12
adcs x7, x11, x20
adcs x15, x5, x13
adcs x22, x23, x9
adc x16, x1, x10
ldp x28, x14, [x0, #432]
movz x8, #56129, lsl #0
ldp x2, x25, [x0, #416]
ldp x3, x21, [x0, #368]
ldp x12, x11, [x0, #352]
adds x20, x22, x24
adc x13, x16, x10
movk x8, #1, lsl #16
mul x5, x2, x8
extr x23, x13, x20, #63
mul x9, x25, x8
and x1, x20, #0x7fffffffffffffff
mul x22, x28, x8
mul x24, x23, x26
mul x16, x14, x8
adds x13, x4, x24
adcs x20, x7, x17
adcs x23, x15, x6
adc x4, x1, x10
umulh x24, x14, x8
adds x17, x12, x5
adcs x7, x11, x9
adcs x15, x3, x22
adcs x6, x21, x16
adc x1, x24, x10
stp x23, x4, [x0, #112]
stp x13, x20, [x0, #96]
umulh x14, x2, x8
umulh x12, x28, x8
umulh x5, x25, x8
ldr x11, [x0, #416]
adds x9, x6, x6
adc x22, x1, x1
mul x3, x22, x26
lsr x16, x9, #1
adds x21, x17, x3
adcs x24, x7, x14
adcs x23, x15, x5
adc x4, x16, x12
stp x21, x24, [x0, #128]
stp x23, x4, [x0, #144]
ldr x13, [x0, #424]
ldp x20, x2, [x0, #128]
ldp x28, x25, [x0, #144]
umulh x8, x11, x20
umulh x6, x11, x28
mul x1, x11, x25
umulh x22, x11, x2
mul x9, x11, x28
umulh x17, x11, x25
mul x3, x13, x2
mul x14, x11, x2
mul x7, x13, x20
mul x5, x13, x28
mul x15, x11, x20
mul x12, x13, x25
umulh x16, x13, x20
umulh x24, x13, x2
adds x21, x14, x8
adcs x23, x9, x22
adcs x4, x1, x6
adc x11, x17, x10
umulh x14, x13, x25
umulh x8, x13, x28
ldr x9, [x0, #432]
adds x22, x21, x7
adcs x1, x23, x3
adcs x6, x4, x5
adcs x17, x11, x12
adc x13, x10, x10
mul x21, x9, x20
mul x7, x9, x25
mul x23, x9, x28
mul x3, x9, x2
umulh x4, x9, x2
umulh x5, x9, x20
adds x12, x1, x16
adcs x11, x6, x24
adcs x1, x17, x8
adc x16, x13, x14
umulh x6, x9, x25
umulh x24, x9, x28
ldr x8, [x0, #440]
adds x17, x12, x21
adcs x14, x11, x3
adcs x13, x1, x23
adcs x9, x16, x7
adc x12, x10, x10
mul x21, x8, x20
umulh x3, x8, x20
mul x11, x8, x28
mul x23, x8, x25
mul x1, x8, x2
umulh x7, x8, x2
adds x16, x14, x5
adcs x20, x13, x4
adcs x2, x9, x24
adc x5, x12, x6
umulh x14, x8, x28
umulh x4, x8, x25
adds x13, x16, x21
adcs x24, x20, x1
adcs x9, x2, x11
adcs x6, x5, x23
adc x12, x10, x10
adds x28, x24, x3
adcs x8, x9, x7
adcs x25, x6, x14
adc x21, x12, x4
umulh x16, x27, x21
mul x1, x27, x8
mul x20, x27, x28
mul x11, x27, x25
mul x2, x27, x21
umulh x23, x27, x25
umulh x5, x27, x28
umulh x3, x27, x8
adds x24, x15, x20
adcs x7, x22, x1
adcs x9, x17, x11
adcs x6, x13, x2
adc x14, x16, x10
adds x12, x6, x23
adc x4, x14, x10
extr x21, x4, x12, #63
and x25, x12, #0x7fffffffffffffff
mul x28, x21, x26
adds x8, x24, x28
adcs x15, x7, x5
adcs x20, x9, x3
adc x22, x25, x10
stp x8, x15, [x0, #128]
stp x20, x22, [x0, #144]
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
.globl lab_sc_o3_19_50_0
lab_sc_o3_19_50_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
stp x6, x15, [x0, #256]
stp x9, x21, [x0, #224]
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x6, x16, x5
adcs x15, x1, x28
csel x9, x27, x10, hs
stp x17, x3, [x0, #240]
stp x8, x23, [x0, #272]
ldp x21, x11, [x0, #224]
subs x25, x12, x14
sbcs x24, x20, x10
sbcs x7, x13, x10
sbc x16, x4, x10
adds x5, x22, x9
adcs x28, x2, x10
adc x1, x6, x10
ldp x17, x3, [x0, #240]
umulh x8, x21, x11
stp x25, x24, [x0, #320]
stp x5, x28, [x0, #288]
stp x1, x15, [x0, #304]
stp x7, x16, [x0, #336]
mul x23, x21, x11
umulh x12, x21, x21
umulh x14, x11, x11
mul x20, x11, x11
mul x13, x21, x21
umulh x4, x21, x17
umulh x22, x21, x3
mul x9, x21, x17
mul x2, x21, x3
umulh x6, x11, x3
mul x25, x11, x17
mul x24, x11, x3
umulh x5, x11, x17
umulh x28, x17, x3
mul x1, x17, x3
umulh x15, x17, x17
mul x7, x17, x17
adds x16, x9, x8
adcs x21, x2, x4
adc x11, x22, x10
umulh x17, x3, x3
mul x8, x3, x3
lsl x9, x23, #1
adds x2, x21, x25
adcs x4, x11, x24
adc x22, x6, x10
extr x3, x16, x23, #63
ldp x21, x25, [x0, #256]
adds x11, x4, x5
adcs x24, x22, x1
adc x6, x28, x10
extr x23, x2, x16, #63
ldp x5, x4, [x0, #272]
extr x1, x11, x2, #63
extr x22, x24, x11, #63
extr x28, x6, x24, #63
lsr x16, x6, #63
adds x2, x9, x12
adcs x11, x3, x20
adcs x24, x23, x14
adcs x6, x1, x7
adcs x9, x22, x15
adcs x12, x28, x8
adc x3, x16, x17
umulh x20, x21, x25
umulh x14, x21, x5
umulh x23, x21, x4
mul x7, x21, x5
mul x1, x21, x4
umulh x22, x25, x4
mul x15, x25, x5
adds x8, x7, x20
adcs x28, x1, x14
adc x17, x23, x10
mul x16, x25, x4
umulh x7, x25, x5
adds x20, x28, x15
adcs x1, x17, x16
adc x14, x22, x10
umulh x23, x5, x4
mul x28, x5, x4
adds x15, x1, x7
adcs x17, x14, x28
adc x16, x23, x10
mul x22, x21, x25
umulh x1, x27, x3
mul x7, x27, x3
mul x14, x27, x6
umulh x28, x27, x6
mul x23, x27, x9
umulh x3, x27, x9
mul x6, x27, x12
umulh x9, x27, x12
adds x12, x13, x14
adcs x14, x2, x23
adcs x13, x11, x6
adcs x2, x24, x7
adc x23, x1, x10
umulh x6, x21, x21
mul x11, x21, x21
adds x7, x2, x9
adc x24, x23, x10
umulh x1, x25, x25
mul x21, x25, x25
extr x2, x24, x7, #63
and x9, x7, #0x7fffffffffffffff
mul x23, x2, x26
adds x25, x12, x23
adcs x24, x14, x28
adcs x7, x13, x3
adc x2, x9, x10
umulh x12, x5, x5
mul x23, x5, x5
umulh x14, x4, x4
mul x28, x4, x4
lsr x13, x16, #63
extr x3, x16, x17, #63
extr x9, x17, x15, #63
extr x5, x15, x20, #63
extr x4, x20, x8, #63
extr x16, x8, x22, #63
lsl x17, x22, #1
stp x25, x24, [x0, #352]
stp x7, x2, [x0, #368]
ldr x15, [x0, #320]
ldr x20, [x0, #328]
ldp x8, x22, [x0, #224]
adds x25, x17, x6
adcs x24, x16, x21
adcs x7, x4, x1
adcs x2, x5, x23
adcs x6, x9, x12
adcs x17, x3, x28
adc x21, x13, x14
ldp x16, x1, [x0, #240]
umulh x4, x15, x8
umulh x5, x15, x22
mul x23, x15, x22
mul x9, x20, x8
mul x12, x20, x22
mul x3, x27, x2
umulh x28, x27, x2
mul x13, x27, x6
umulh x14, x27, x6
mul x2, x27, x17
umulh x6, x27, x17
mul x17, x27, x21
umulh x21, x27, x21
adds x3, x11, x3
adcs x11, x25, x13
adcs x13, x24, x2
adcs x25, x7, x17
adc x24, x21, x10
adds x2, x25, x6
adc x7, x24, x10
umulh x17, x15, x16
extr x21, x7, x2, #63
and x25, x2, #0x7fffffffffffffff
mul x6, x21, x26
adds x24, x3, x6
adcs x7, x11, x28
adcs x2, x13, x14
adc x21, x25, x10
umulh x3, x15, x1
mul x6, x15, x16
mul x28, x15, x1
mul x11, x15, x8
adds x13, x23, x4
adcs x14, x6, x5
adcs x25, x28, x17
adc x15, x3, x10
mul x23, x20, x16
mul x4, x20, x1
umulh x6, x20, x8
stp x24, x7, [x0, #384]
umulh x5, x20, x22
umulh x28, x20, x16
umulh x17, x20, x1
stp x2, x21, [x0, #400]
ldr x3, [x0, #336]
ldr x24, [x0, #344]
adds x7, x13, x9
adcs x20, x14, x12
adcs x2, x25, x23
adcs x21, x15, x4
adc x13, x10, x10
mul x9, x3, x8
mul x14, x3, x22
mul x12, x3, x16
adds x23, x20, x6
adcs x25, x2, x5
adcs x4, x21, x28
adc x15, x13, x17
mul x20, x3, x1
umulh x6, x3, x8
umulh x5, x3, x22
umulh x2, x3, x16
umulh x28, x3, x1
adds x21, x23, x9
adcs x17, x25, x14
adcs x13, x4, x12
adcs x3, x15, x20
adc x9, x10, x10
ldr x23, [x0, #288]
ldp x14, x25, [x0, #256]
adds x12, x17, x6
adcs x4, x13, x5
adcs x20, x3, x2
adc x15, x9, x28
umulh x6, x23, x14
umulh x17, x23, x25
mul x5, x23, x25
mul x13, x24, x8
umulh x2, x24, x8
mul x3, x24, x22
umulh x9, x24, x22
mul x28, x24, x16
umulh x8, x24, x16
mul x22, x24, x1
adds x16, x12, x13
adcs x13, x4, x3
adcs x12, x20, x28
adcs x3, x15, x22
adc x4, x10, x10
umulh x28, x24, x1
ldr x20, [x0, #296]
adds x15, x13, x2
adcs x22, x12, x9
adcs x24, x3, x8
adc x1, x4, x28
mul x2, x20, x14
mul x13, x20, x25
ldp x12, x9, [x0, #272]
mul x3, x27, x15
umulh x8, x27, x15
mul x4, x27, x22
umulh x28, x27, x22
mul x15, x27, x24
umulh x22, x27, x24
mul x24, x27, x1
umulh x1, x27, x1
adds x11, x11, x3
adcs x3, x7, x4
adcs x7, x21, x15
adcs x4, x16, x24
adc x21, x1, x10
adds x15, x4, x22
adc x16, x21, x10
umulh x24, x23, x12
extr x1, x16, x15, #63
and x22, x15, #0x7fffffffffffffff
mul x4, x1, x26
adds x21, x11, x4
adcs x16, x3, x8
adcs x15, x7, x28
adc x1, x22, x10
umulh x11, x23, x9
mul x4, x23, x12
mul x3, x23, x9
mul x8, x23, x14
adds x28, x5, x6
adcs x7, x4, x17
adcs x22, x3, x24
adc x23, x11, x10
mul x6, x20, x12
mul x5, x20, x9
umulh x4, x20, x14
stp x21, x16, [x0, #448]
umulh x17, x20, x25
umulh x3, x20, x12
umulh x24, x20, x9
stp x15, x1, [x0, #464]
ldr x11, [x0, #304]
ldr x21, [x0, #312]
adds x16, x28, x2
adcs x20, x7, x13
adcs x1, x22, x6
adcs x15, x23, x5
adc x2, x10, x10
mul x28, x11, x14
mul x13, x11, x25
mul x7, x11, x12
adds x22, x20, x4
adcs x6, x1, x17
adcs x23, x15, x3
adc x5, x2, x24
mul x20, x11, x9
umulh x4, x11, x14
umulh x1, x11, x25
umulh x17, x11, x12
umulh x15, x11, x9
adds x3, x22, x28
adcs x2, x6, x13
adcs x24, x23, x7
adcs x11, x5, x20
adc x22, x10, x10
mul x28, x21, x14
umulh x6, x21, x14
mul x13, x21, x25
umulh x23, x21, x25
mul x7, x21, x12
umulh x20, x21, x12
adds x5, x2, x4
adcs x14, x24, x1
adcs x25, x11, x17
adc x12, x22, x15
mul x2, x21, x9
umulh x4, x21, x9
ldp x24, x1, [x0, #352]
ldp x17, x11, [x0, #368]
adds x15, x5, x28
adcs x22, x14, x13
adcs x9, x25, x7
adcs x21, x12, x2
adc x5, x10, x10
ldp x28, x13, [x0, #384]
ldr x14, [x0, #352]
adds x7, x22, x6
adcs x25, x9, x23
adcs x2, x21, x20
adc x12, x5, x4
ldp x6, x22, [x0, #400]
ldp x23, x9, [x0, #384]
subs x20, x24, x28
sbcs x21, x1, x13
sbcs x4, x17, x6
sbcs x5, x11, x22
csel x28, x10, x27, hs
umulh x24, x27, x12
mul x13, x27, x12
mul x1, x27, x7
umulh x17, x27, x7
mul x6, x27, x25
umulh x11, x27, x25
subs x22, x20, x28
sbcs x12, x21, x10
sbcs x7, x4, x10
sbc x25, x5, x10
mul x28, x27, x2
umulh x20, x27, x2
adds x21, x8, x1
adcs x4, x16, x6
adcs x5, x3, x28
adcs x2, x15, x13
adc x1, x24, x10
stp x7, x25, [x0, #432]
stp x22, x12, [x0, #416]
ldp x8, x6, [x0, #400]
umulh x16, x14, x23
umulh x3, x14, x9
mul x28, x14, x9
ldr x13, [x0, #360]
mul x15, x14, x23
adds x24, x2, x20
adc x7, x1, x10
umulh x25, x14, x8
umulh x22, x14, x6
extr x12, x7, x24, #63
and x2, x24, #0x7fffffffffffffff
mul x20, x12, x26
adds x1, x21, x20
adcs x7, x4, x17
adcs x24, x5, x11
adc x12, x2, x10
mul x21, x14, x8
mul x20, x14, x6
mul x4, x13, x23
mul x17, x13, x9
adds x5, x28, x16
adcs x11, x21, x3
adcs x2, x20, x25
adc x14, x22, x10
stp x1, x7, [x0, #480]
stp x24, x12, [x0, #496]
mul x16, x13, x8
mul x28, x13, x6
umulh x3, x13, x23
umulh x21, x13, x9
umulh x25, x13, x8
umulh x20, x13, x6
ldr x22, [x0, #368]
ldr x1, [x0, #376]
adds x7, x5, x4
adcs x24, x11, x17
adcs x12, x2, x16
adcs x13, x14, x28
adc x4, x10, x10
mul x5, x22, x23
mul x17, x22, x9
mul x11, x22, x8
adds x16, x24, x3
adcs x2, x12, x21
adcs x28, x13, x25
adc x14, x4, x20
mul x3, x22, x6
umulh x24, x22, x23
umulh x21, x22, x9
umulh x12, x22, x8
umulh x13, x22, x6
adds x25, x16, x5
adcs x4, x2, x17
adcs x20, x28, x11
adcs x22, x14, x3
adc x5, x10, x10
movz x16, #56129, lsl #0
ldp x17, x2, [x0, #432]
adds x28, x4, x24
adcs x11, x20, x21
adcs x14, x22, x12
adc x3, x5, x13
movk x16, #1, lsl #16
ldp x4, x24, [x0, #416]
ldp x20, x21, [x0, #352]
mul x22, x1, x23
umulh x12, x1, x23
mul x5, x1, x9
umulh x13, x1, x9
mul x23, x1, x8
umulh x9, x1, x8
mul x8, x1, x6
adds x28, x28, x22
adcs x22, x11, x5
adcs x11, x14, x23
adcs x5, x3, x8
adc x14, x10, x10
umulh x23, x1, x6
adds x8, x22, x12
adcs x3, x11, x13
adcs x6, x5, x9
adc x1, x14, x23
umulh x22, x2, x16
mul x12, x2, x16
mul x11, x4, x16
umulh x13, x4, x16
mul x9, x24, x16
umulh x5, x24, x16
mul x23, x17, x16
umulh x14, x17, x16
umulh x2, x27, x1
mul x4, x27, x1
mul x24, x27, x8
umulh x17, x27, x8
mul x16, x27, x3
umulh x1, x27, x3
mul x8, x27, x6
umulh x3, x27, x6
adds x6, x15, x24
adcs x15, x7, x16
adcs x24, x25, x8
adcs x7, x28, x4
adc x16, x2, x10
ldr x8, [x0, #416]
adds x25, x7, x3
adc x28, x16, x10
extr x4, x28, x25, #63
and x2, x25, #0x7fffffffffffffff
mul x7, x4, x26
ldr x3, [x0, #424]
adds x16, x6, x7
adcs x28, x15, x17
adcs x25, x24, x1
adc x4, x2, x10
ldp x6, x7, [x0, #368]
stp x16, x28, [x0, #96]
stp x25, x4, [x0, #112]
adds x17, x20, x11
adcs x15, x21, x9
adcs x24, x6, x23
adcs x1, x7, x12
adc x2, x22, x10
ldr x16, [x0, #432]
adds x28, x1, x1
adc x25, x2, x2
mul x4, x25, x26
lsr x20, x28, #1
adds x11, x17, x4
adcs x21, x15, x13
adcs x9, x24, x5
adc x23, x20, x14
stp x11, x21, [x0, #128]
stp x9, x23, [x0, #144]
ldp x6, x12, [x0, #128]
ldp x7, x22, [x0, #144]
ldr x1, [x0, #440]
umulh x2, x8, x6
umulh x25, x8, x12
umulh x28, x8, x7
umulh x17, x8, x22
mul x4, x8, x12
mul x13, x8, x7
mul x15, x8, x22
mul x5, x3, x6
mul x24, x3, x12
mul x14, x3, x7
mul x20, x3, x22
mul x21, x8, x6
adds x11, x4, x2
adcs x9, x13, x25
adcs x23, x15, x28
adc x8, x17, x10
umulh x4, x3, x6
umulh x2, x3, x12
umulh x13, x3, x7
umulh x25, x3, x22
adds x15, x11, x5
adcs x28, x9, x24
adcs x17, x23, x14
adcs x3, x8, x20
adc x11, x10, x10
mul x5, x16, x6
mul x9, x16, x12
mul x24, x16, x7
adds x23, x28, x4
adcs x14, x17, x2
adcs x20, x3, x13
adc x8, x11, x25
mul x28, x16, x22
umulh x4, x16, x6
umulh x17, x16, x12
umulh x2, x16, x7
umulh x13, x16, x22
adds x3, x23, x5
adcs x25, x14, x9
adcs x11, x20, x24
adcs x16, x8, x28
adc x23, x10, x10
ldp x5, x9, [x0, #448]
mul x14, x1, x6
umulh x24, x1, x6
adds x20, x25, x4
adcs x28, x11, x17
adcs x8, x16, x2
adc x6, x23, x13
ldp x4, x25, [x0, #464]
ldp x17, x11, [x0, #480]
mul x2, x1, x12
umulh x16, x1, x12
mul x13, x1, x7
umulh x23, x1, x7
mul x12, x1, x22
adds x7, x20, x14
adcs x14, x28, x2
adcs x20, x8, x13
adcs x2, x6, x12
adc x28, x10, x10
umulh x13, x1, x22
adds x8, x14, x24
adcs x12, x20, x16
adcs x6, x2, x23
adc x1, x28, x13
ldp x22, x24, [x0, #496]
umulh x14, x27, x1
mul x16, x27, x1
mul x20, x27, x8
umulh x2, x27, x8
subs x23, x5, x17
sbcs x28, x9, x11
sbcs x13, x4, x22
sbcs x1, x25, x24
csel x8, x10, x27, hs
mul x5, x27, x12
umulh x17, x27, x12
mul x9, x27, x6
umulh x11, x27, x6
adds x4, x21, x20
adcs x22, x15, x5
adcs x25, x3, x9
adcs x24, x7, x16
adc x12, x14, x10
subs x6, x23, x8
sbcs x21, x28, x10
sbcs x20, x13, x10
sbc x15, x1, x10
adds x5, x24, x11
adc x3, x12, x10
umulh x9, x6, x21
umulh x16, x6, x20
umulh x7, x6, x15
mul x14, x6, x20
mul x23, x6, x15
umulh x8, x21, x15
mul x28, x21, x20
mul x13, x21, x15
extr x1, x3, x5, #63
and x11, x5, #0x7fffffffffffffff
mul x24, x1, x26
adds x12, x14, x9
adcs x3, x23, x16
adc x5, x7, x10
umulh x1, x21, x20
umulh x14, x20, x15
adds x9, x4, x24
adcs x23, x22, x2
adcs x16, x25, x17
adc x7, x11, x10
mul x4, x20, x15
mul x24, x6, x21
adds x22, x3, x28
adcs x2, x5, x13
adc x25, x8, x10
umulh x17, x6, x6
umulh x11, x21, x21
mul x3, x21, x21
umulh x28, x20, x20
mul x13, x20, x20
mul x5, x6, x6
stp x9, x23, [x0, #128]
umulh x8, x15, x15
adds x21, x2, x1
adcs x20, x25, x4
adc x6, x14, x10
mul x9, x15, x15
extr x23, x22, x12, #63
extr x2, x12, x24, #63
lsl x1, x24, #1
stp x16, x7, [x0, #144]
ldp x25, x4, [x0, #448]
ldp x14, x15, [x0, #464]
extr x12, x21, x22, #63
extr x24, x20, x21, #63
extr x16, x6, x20, #63
lsr x7, x6, #63
adds x22, x1, x17
adcs x21, x2, x3
adcs x20, x23, x11
adcs x6, x12, x13
adcs x1, x24, x28
adcs x17, x16, x9
adc x2, x7, x8
ldp x3, x11, [x0, #480]
ldp x23, x12, [x0, #496]
adds x13, x25, x3
adcs x24, x4, x11
adcs x28, x14, x23
adcs x9, x15, x12
csel x16, x27, x10, hs
umulh x8, x27, x2
mul x7, x27, x2
mul x25, x27, x6
umulh x3, x27, x6
mul x4, x27, x1
umulh x11, x27, x1
mul x23, x27, x17
umulh x14, x27, x17
adds x12, x5, x25
adcs x15, x22, x4
adcs x2, x21, x23
adcs x6, x20, x7
adc x1, x8, x10
adds x17, x13, x16
adcs x25, x24, x10
adc x5, x28, x10
umulh x22, x17, x25
umulh x4, x17, x5
umulh x23, x17, x9
adds x21, x6, x14
adc x7, x1, x10
mul x20, x17, x5
mul x8, x17, x9
umulh x13, x25, x9
mul x16, x25, x5
mul x24, x25, x9
extr x28, x7, x21, #63
and x14, x21, #0x7fffffffffffffff
adds x6, x20, x22
adcs x1, x8, x4
adc x7, x23, x10
mul x21, x28, x26
umulh x20, x25, x5
umulh x22, x5, x9
adds x8, x12, x21
adcs x4, x15, x3
adcs x23, x2, x11
adc x28, x14, x10
adds x12, x1, x16
adcs x21, x7, x24
adc x3, x13, x10
mul x15, x5, x9
mul x11, x17, x25
umulh x2, x17, x17
umulh x14, x25, x25
mul x16, x25, x25
umulh x1, x5, x5
mul x7, x5, x5
mul x24, x17, x17
stp x8, x4, [x0, #192]
stp x23, x28, [x0, #208]
adds x13, x21, x20
adcs x25, x3, x15
adc x5, x22, x10
ldr x17, [x0, #64]
umulh x8, x9, x9
mul x4, x9, x9
extr x23, x12, x6, #63
extr x28, x6, x11, #63
lsl x21, x11, #1
lsr x20, x5, #63
extr x3, x5, x25, #63
extr x15, x25, x13, #63
extr x22, x13, x12, #63
ldr x9, [x0, #72]
ldp x6, x11, [x0, #192]
adds x5, x21, x2
adcs x25, x28, x16
adcs x12, x23, x14
adcs x13, x22, x7
adcs x21, x15, x1
adcs x2, x3, x4
adc x16, x20, x8
ldp x28, x14, [x0, #208]
umulh x23, x17, x6
umulh x22, x17, x11
mul x7, x17, x11
mul x15, x9, x6
mul x1, x9, x11
mul x3, x27, x13
umulh x4, x27, x13
mul x8, x27, x21
umulh x20, x27, x21
mul x13, x27, x2
umulh x21, x27, x2
mul x2, x27, x16
umulh x16, x27, x16
adds x3, x24, x3
adcs x24, x5, x8
adcs x5, x25, x13
adcs x8, x12, x2
adc x13, x16, x10
adds x25, x8, x21
adc x12, x13, x10
umulh x2, x17, x28
extr x16, x12, x25, #63
and x8, x25, #0x7fffffffffffffff
mul x21, x16, x26
adds x13, x3, x21
adcs x12, x24, x4
adcs x25, x5, x20
adc x16, x8, x10
umulh x3, x17, x14
mul x21, x17, x28
mul x4, x17, x14
mul x24, x17, x6
adds x20, x7, x23
adcs x5, x21, x22
adcs x8, x4, x2
adc x17, x3, x10
mul x7, x9, x28
mul x23, x9, x14
umulh x21, x9, x6
stp x13, x12, [x0, #160]
umulh x22, x9, x11
umulh x4, x9, x28
umulh x2, x9, x14
stp x25, x16, [x0, #176]
ldr x3, [x0, #80]
ldr x12, [x0, #88]
adds x13, x20, x15
adcs x9, x5, x1
adcs x25, x8, x7
adcs x16, x17, x23
adc x20, x10, x10
mul x15, x3, x6
mul x5, x3, x11
mul x1, x3, x28
adds x8, x9, x21
adcs x7, x25, x22
adcs x23, x16, x4
adc x17, x20, x2
mul x9, x3, x14
umulh x21, x3, x6
umulh x25, x3, x11
umulh x22, x3, x28
umulh x4, x3, x14
adds x16, x8, x15
adcs x2, x7, x5
adcs x20, x23, x1
adcs x3, x17, x9
adc x8, x10, x10
mul x15, x12, x6
umulh x5, x12, x6
mul x7, x12, x11
umulh x1, x12, x11
mul x23, x12, x28
umulh x9, x12, x28
adds x17, x2, x21
adcs x6, x20, x25
adcs x11, x3, x22
adc x28, x8, x4
mul x21, x12, x14
umulh x2, x12, x14
adds x25, x17, x15
adcs x20, x6, x7
adcs x22, x11, x23
adcs x3, x28, x21
adc x4, x10, x10
adds x8, x20, x5
adcs x12, x22, x1
adcs x14, x3, x9
adc x15, x4, x2
umulh x17, x27, x15
mul x7, x27, x8
mul x6, x27, x12
mul x23, x27, x14
mul x11, x27, x15
umulh x21, x27, x14
umulh x28, x27, x8
umulh x5, x27, x12
adds x20, x24, x7
adcs x1, x13, x6
adcs x22, x16, x23
adcs x3, x25, x11
adc x9, x17, x10
adds x4, x3, x21
adc x2, x9, x10
extr x15, x2, x4, #63
and x14, x4, #0x7fffffffffffffff
mul x8, x15, x26
adds x12, x20, x8
adcs x24, x1, x28
adcs x7, x22, x5
adc x13, x14, x10
stp x12, x24, [x0, #192]
stp x7, x13, [x0, #208]
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
.globl lab_sc_o3_19_50_1
lab_sc_o3_19_50_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
umulh x3, x12, x9
umulh x7, x12, x25
umulh x11, x12, x24
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
mul x4, x12, x24
mul x8, x12, x25
umulh x2, x9, x24
mul x13, x25, x24
umulh x17, x9, x25
mul x14, x9, x24
umulh x1, x25, x24
mul x6, x9, x25
mul x20, x12, x9
adds x22, x8, x3
adcs x16, x4, x7
adc x23, x11, x10
umulh x15, x25, x25
mul x21, x25, x25
umulh x5, x9, x9
mul x28, x9, x9
umulh x3, x24, x24
mul x8, x24, x24
umulh x4, x12, x12
mul x7, x12, x12
lsl x11, x20, #1
adds x25, x16, x6
adcs x9, x23, x14
adc x24, x2, x10
extr x12, x22, x20, #63
ldp x16, x6, [x0, #272]
adds x23, x9, x17
adcs x14, x24, x13
adc x2, x1, x10
extr x20, x25, x22, #63
ldp x17, x9, [x0, #256]
extr x13, x23, x25, #63
extr x24, x14, x23, #63
extr x1, x2, x14, #63
lsr x22, x2, #63
adds x25, x11, x4
adcs x23, x12, x28
adcs x14, x20, x5
adcs x2, x13, x21
adcs x11, x24, x15
adcs x4, x1, x8
adc x12, x22, x3
umulh x28, x17, x6
umulh x5, x17, x16
umulh x20, x9, x6
mul x21, x17, x16
mul x13, x17, x6
mul x24, x9, x6
umulh x15, x17, x9
adds x8, x21, x15
adcs x1, x13, x5
adc x3, x28, x10
umulh x22, x9, x16
umulh x21, x16, x6
mul x15, x27, x2
umulh x13, x27, x2
mul x5, x27, x11
umulh x28, x27, x11
mul x2, x27, x4
umulh x11, x27, x4
mul x4, x27, x12
umulh x12, x27, x12
adds x15, x7, x15
adcs x7, x25, x5
adcs x25, x23, x2
adcs x5, x14, x4
adc x2, x12, x10
adds x23, x5, x11
adc x4, x2, x10
mul x14, x16, x6
extr x12, x4, x23, #63
and x5, x23, #0x7fffffffffffffff
mul x11, x12, x26
adds x2, x15, x11
adcs x4, x7, x13
adcs x23, x25, x28
adc x12, x5, x10
mul x15, x17, x9
mul x11, x9, x16
umulh x7, x9, x9
mul x13, x9, x9
adds x25, x1, x11
adcs x28, x3, x24
adc x5, x20, x10
umulh x9, x17, x17
mul x1, x16, x16
umulh x11, x16, x16
mul x3, x17, x17
stp x23, x12, [x0, #368]
extr x24, x8, x15, #63
lsl x20, x15, #1
umulh x16, x6, x6
mul x17, x6, x6
adds x23, x28, x22
adcs x12, x5, x14
adc x15, x21, x10
extr x6, x25, x8, #63
stp x2, x4, [x0, #352]
ldr x28, [x0, #320]
ldp x22, x5, [x0, #240]
lsr x14, x15, #63
extr x21, x15, x12, #63
extr x8, x12, x23, #63
extr x2, x23, x25, #63
ldr x4, [x0, #328]
adds x15, x20, x9
adcs x12, x24, x13
adcs x25, x6, x7
adcs x23, x2, x1
adcs x9, x8, x11
adcs x20, x21, x17
adc x13, x14, x16
ldp x24, x7, [x0, #224]
umulh x6, x28, x5
umulh x2, x28, x22
mul x1, x28, x22
mul x8, x28, x5
mul x11, x4, x22
mul x21, x27, x23
umulh x17, x27, x23
mul x14, x27, x9
umulh x16, x27, x9
mul x23, x27, x20
umulh x9, x27, x20
mul x20, x27, x13
umulh x13, x27, x13
adds x21, x3, x21
adcs x3, x15, x14
adcs x14, x12, x23
adcs x15, x25, x20
adc x12, x13, x10
adds x23, x15, x9
adc x25, x12, x10
mul x20, x28, x7
extr x13, x25, x23, #63
and x15, x23, #0x7fffffffffffffff
mul x9, x13, x26
adds x12, x21, x9
adcs x25, x3, x17
adcs x23, x14, x16
adc x13, x15, x10
umulh x21, x28, x24
mul x9, x4, x24
umulh x17, x28, x7
mul x3, x28, x24
stp x12, x25, [x0, #384]
mul x14, x4, x5
adds x16, x20, x21
adcs x15, x1, x17
adcs x28, x8, x2
adc x12, x6, x10
mul x25, x4, x7
umulh x20, x4, x5
ldr x21, [x0, #336]
umulh x1, x4, x22
stp x23, x13, [x0, #400]
umulh x17, x4, x24
umulh x8, x4, x7
ldr x2, [x0, #344]
adds x6, x16, x9
adcs x23, x15, x25
adcs x13, x28, x11
adcs x4, x12, x14
adc x16, x10, x10
mul x9, x21, x24
mul x15, x21, x5
mul x25, x21, x7
adds x11, x23, x17
adcs x28, x13, x8
adcs x14, x4, x1
adc x12, x16, x20
mul x23, x21, x22
umulh x17, x21, x22
umulh x8, x21, x24
umulh x13, x21, x5
umulh x1, x21, x7
adds x4, x11, x9
adcs x20, x28, x25
adcs x16, x14, x23
adcs x21, x12, x15
adc x9, x10, x10
ldr x11, [x0, #288]
ldp x25, x28, [x0, #256]
adds x23, x20, x8
adcs x14, x16, x1
adcs x15, x21, x17
adc x12, x9, x13
umulh x8, x11, x28
mul x20, x11, x28
umulh x1, x11, x25
mul x16, x2, x5
umulh x17, x2, x5
mul x21, x2, x24
umulh x9, x2, x24
mul x13, x2, x7
umulh x5, x2, x7
mul x24, x2, x22
adds x7, x23, x21
adcs x21, x14, x13
adcs x23, x15, x24
adcs x13, x12, x16
adc x14, x10, x10
umulh x24, x2, x22
ldr x15, [x0, #296]
adds x12, x21, x9
adcs x16, x23, x5
adcs x2, x13, x24
adc x22, x14, x17
mul x9, x15, x25
mul x21, x15, x28
umulh x23, x15, x28
umulh x5, x15, x25
mul x13, x27, x12
umulh x24, x27, x12
mul x14, x27, x16
umulh x17, x27, x16
mul x12, x27, x2
umulh x16, x27, x2
mul x2, x27, x22
umulh x22, x27, x22
adds x3, x3, x13
adcs x13, x6, x14
adcs x6, x4, x12
adcs x14, x7, x2
adc x4, x22, x10
adds x12, x14, x16
adc x7, x4, x10
ldr x2, [x0, #304]
extr x22, x7, x12, #63
and x16, x12, #0x7fffffffffffffff
mul x14, x22, x26
adds x4, x3, x14
adcs x7, x13, x24
adcs x12, x6, x17
adc x22, x16, x10
ldp x3, x14, [x0, #272]
mul x13, x2, x25
stp x4, x7, [x0, #448]
umulh x24, x2, x25
mul x17, x2, x28
stp x12, x22, [x0, #464]
umulh x6, x11, x3
mul x16, x11, x14
mul x4, x11, x25
mul x7, x11, x3
umulh x22, x11, x14
adds x12, x20, x1
adcs x11, x7, x8
adcs x1, x16, x6
adc x20, x22, x10
umulh x7, x15, x14
mul x8, x15, x3
mul x16, x15, x14
adds x6, x12, x9
adcs x22, x11, x21
adcs x9, x1, x8
adcs x12, x20, x16
adc x21, x10, x10
umulh x11, x15, x3
mul x1, x2, x3
adds x8, x22, x5
adcs x20, x9, x23
adcs x16, x12, x11
adc x15, x21, x7
umulh x22, x2, x3
mul x5, x2, x14
umulh x9, x2, x14
umulh x23, x2, x28
ldr x12, [x0, #312]
adds x11, x8, x13
adcs x21, x20, x17
adcs x7, x16, x1
adcs x2, x15, x5
adc x8, x10, x10
ldp x13, x20, [x0, #384]
mul x17, x12, x25
umulh x16, x12, x25
adds x1, x21, x24
adcs x5, x7, x23
adcs x15, x2, x22
adc x25, x8, x9
mul x21, x12, x3
umulh x24, x12, x3
mul x7, x12, x14
umulh x23, x12, x14
mul x22, x12, x28
umulh x2, x12, x28
ldp x9, x8, [x0, #368]
adds x3, x1, x17
adcs x14, x5, x22
adcs x28, x15, x21
adcs x12, x25, x7
adc x1, x10, x10
ldp x17, x22, [x0, #352]
ldr x5, [x0, #352]
adds x21, x14, x16
adcs x15, x28, x2
adcs x7, x12, x24
adc x25, x1, x23
ldp x16, x14, [x0, #400]
ldp x2, x28, [x0, #400]
subs x24, x17, x13
sbcs x12, x22, x20
sbcs x23, x9, x16
sbcs x1, x8, x14
csel x13, x10, x27, hs
mul x17, x27, x15
mul x20, x27, x25
umulh x22, x27, x25
mul x9, x27, x7
umulh x16, x27, x7
umulh x8, x27, x15
subs x14, x24, x13
sbcs x25, x12, x10
sbcs x7, x23, x10
sbc x15, x1, x10
mul x13, x27, x21
umulh x24, x27, x21
adds x12, x4, x13
adcs x23, x6, x17
adcs x1, x11, x9
adcs x21, x3, x20
adc x13, x22, x10
stp x7, x15, [x0, #432]
stp x14, x25, [x0, #416]
umulh x4, x5, x2
ldr x17, [x0, #360]
ldp x6, x11, [x0, #384]
umulh x9, x5, x28
mul x20, x5, x28
mul x3, x5, x2
adds x22, x21, x16
adc x7, x13, x10
mul x15, x17, x2
umulh x14, x5, x6
extr x25, x7, x22, #63
and x21, x22, #0x7fffffffffffffff
mul x16, x25, x26
adds x13, x12, x16
adcs x7, x23, x24
adcs x22, x1, x8
adc x25, x21, x10
umulh x12, x5, x11
mul x16, x5, x11
umulh x23, x17, x2
mul x24, x5, x6
stp x13, x7, [x0, #480]
stp x22, x25, [x0, #496]
adds x1, x16, x14
adcs x8, x3, x12
adcs x21, x20, x4
adc x5, x9, x10
mul x13, x17, x6
mul x7, x17, x11
mul x22, x17, x28
ldr x25, [x0, #368]
umulh x14, x17, x28
umulh x16, x17, x6
umulh x12, x17, x11
ldr x3, [x0, #376]
adds x4, x1, x13
adcs x20, x8, x7
adcs x9, x21, x15
adcs x17, x5, x22
adc x13, x10, x10
mul x1, x25, x6
mul x7, x25, x28
mul x8, x25, x2
adds x15, x20, x16
adcs x21, x9, x12
adcs x22, x17, x23
adc x5, x13, x14
umulh x16, x25, x28
umulh x20, x25, x2
mul x12, x25, x11
umulh x9, x25, x11
umulh x17, x25, x6
adds x23, x15, x1
adcs x13, x21, x12
adcs x14, x22, x8
adcs x25, x5, x7
adc x1, x10, x10
movz x15, #56129, lsl #0
ldp x12, x21, [x0, #368]
adds x22, x13, x17
adcs x8, x14, x9
adcs x5, x25, x20
adc x7, x1, x16
movk x15, #1, lsl #16
ldp x13, x17, [x0, #432]
ldp x14, x9, [x0, #416]
mul x25, x3, x6
umulh x20, x3, x6
mul x1, x3, x11
umulh x16, x3, x11
mul x6, x3, x2
umulh x11, x3, x2
mul x2, x3, x28
adds x22, x22, x25
adcs x25, x8, x1
adcs x8, x5, x6
adcs x1, x7, x2
adc x5, x10, x10
umulh x6, x3, x28
adds x2, x25, x20
adcs x7, x8, x16
adcs x28, x1, x11
adc x3, x5, x6
mul x25, x13, x15
mul x20, x14, x15
umulh x8, x17, x15
mul x16, x17, x15
mul x11, x9, x15
umulh x1, x9, x15
umulh x6, x13, x15
umulh x5, x14, x15
umulh x17, x27, x3
mul x9, x27, x3
mul x13, x27, x2
umulh x14, x27, x2
mul x15, x27, x7
umulh x3, x27, x7
mul x2, x27, x28
umulh x7, x27, x28
adds x28, x24, x13
adcs x24, x4, x15
adcs x13, x23, x2
adcs x4, x22, x9
adc x15, x17, x10
ldr x2, [x0, #416]
adds x23, x4, x7
adc x22, x15, x10
extr x9, x22, x23, #63
and x17, x23, #0x7fffffffffffffff
mul x4, x9, x26
ldr x7, [x0, #424]
adds x15, x28, x4
adcs x22, x24, x14
adcs x23, x13, x3
adc x9, x17, x10
ldp x28, x4, [x0, #352]
stp x15, x22, [x0, #96]
stp x23, x9, [x0, #112]
adds x14, x28, x20
adcs x24, x4, x11
adcs x13, x12, x25
adcs x3, x21, x16
adc x17, x8, x10
ldr x15, [x0, #432]
adds x22, x3, x3
adc x23, x17, x17
mul x9, x23, x26
lsr x28, x22, #1
adds x20, x14, x9
adcs x4, x24, x5
adcs x11, x13, x1
adc x25, x28, x6
stp x20, x4, [x0, #128]
stp x11, x25, [x0, #144]
ldp x12, x16, [x0, #128]
ldp x21, x8, [x0, #144]
ldr x3, [x0, #440]
umulh x17, x2, x12
umulh x23, x2, x21
umulh x22, x2, x8
umulh x14, x2, x16
mul x9, x2, x16
mul x5, x2, x8
mul x24, x7, x8
mul x1, x2, x21
umulh x13, x7, x21
mul x6, x7, x16
umulh x28, x7, x8
mul x4, x2, x12
adds x20, x9, x17
adcs x11, x1, x14
adcs x25, x5, x23
adc x2, x22, x10
mul x9, x7, x12
mul x17, x7, x21
umulh x1, x7, x12
umulh x14, x7, x16
adds x5, x20, x9
adcs x23, x11, x6
adcs x22, x25, x17
adcs x7, x2, x24
adc x20, x10, x10
mul x9, x15, x12
mul x11, x15, x16
mul x6, x15, x21
adds x25, x23, x1
adcs x17, x22, x14
adcs x24, x7, x13
adc x2, x20, x28
mul x23, x15, x8
umulh x1, x15, x16
umulh x22, x15, x8
umulh x14, x15, x21
umulh x13, x15, x12
adds x7, x25, x9
adcs x28, x17, x11
adcs x20, x24, x6
adcs x15, x2, x23
adc x25, x10, x10
ldp x9, x11, [x0, #480]
mul x17, x3, x8
umulh x6, x3, x8
adds x24, x28, x13
adcs x23, x20, x1
adcs x2, x15, x14
adc x8, x25, x22
ldp x13, x28, [x0, #464]
ldp x1, x20, [x0, #496]
mul x14, x3, x12
umulh x15, x3, x12
mul x22, x3, x16
umulh x25, x3, x16
mul x12, x3, x21
adds x16, x24, x14
adcs x14, x23, x22
adcs x24, x2, x12
adcs x22, x8, x17
adc x23, x10, x10
umulh x12, x3, x21
adds x2, x14, x15
adcs x17, x24, x25
adcs x8, x22, x12
adc x3, x23, x6
ldp x21, x15, [x0, #448]
umulh x14, x27, x3
mul x25, x27, x3
mul x24, x27, x17
mul x22, x27, x2
subs x12, x21, x9
sbcs x23, x15, x11
sbcs x6, x13, x1
sbcs x3, x28, x20
csel x21, x10, x27, hs
umulh x9, x27, x2
mul x15, x27, x8
umulh x11, x27, x8
umulh x13, x27, x17
adds x1, x4, x22
adcs x28, x5, x24
adcs x20, x7, x15
adcs x2, x16, x25
adc x8, x14, x10
subs x17, x12, x21
sbcs x4, x23, x10
sbcs x22, x6, x10
sbc x5, x3, x10
adds x24, x2, x11
adc x7, x8, x10
umulh x15, x17, x5
mul x25, x17, x5
umulh x16, x17, x22
mul x14, x17, x22
umulh x12, x4, x5
umulh x21, x17, x4
mul x23, x4, x5
umulh x6, x4, x22
extr x3, x7, x24, #63
and x11, x24, #0x7fffffffffffffff
mul x2, x3, x26
adds x8, x14, x21
adcs x7, x25, x16
adc x24, x15, x10
mul x3, x4, x22
mul x14, x22, x5
adds x21, x1, x2
adcs x25, x28, x9
adcs x16, x20, x13
adc x15, x11, x10
umulh x1, x5, x5
mul x2, x4, x4
umulh x28, x4, x4
adds x9, x7, x3
adcs x20, x24, x23
adc x13, x12, x10
mul x11, x17, x4
mul x7, x5, x5
umulh x3, x22, x5
mul x23, x22, x22
umulh x24, x22, x22
stp x21, x25, [x0, #128]
umulh x12, x17, x17
mul x4, x17, x17
extr x5, x8, x11, #63
extr x22, x9, x8, #63
lsl x21, x11, #1
stp x16, x15, [x0, #144]
ldp x25, x17, [x0, #448]
adds x8, x20, x6
adcs x11, x13, x14
adc x16, x3, x10
ldp x15, x20, [x0, #464]
extr x6, x8, x9, #63
extr x13, x11, x8, #63
extr x14, x16, x11, #63
lsr x3, x16, #63
adds x9, x21, x12
adcs x8, x5, x2
adcs x11, x22, x28
adcs x16, x6, x23
adcs x21, x13, x24
adcs x12, x14, x7
adc x5, x3, x1
ldp x2, x28, [x0, #496]
ldp x22, x6, [x0, #480]
adds x23, x25, x22
adcs x13, x17, x6
adcs x24, x15, x2
adcs x7, x20, x28
csel x14, x27, x10, hs
mul x1, x27, x21
umulh x3, x27, x21
mul x25, x27, x16
mul x22, x27, x5
umulh x17, x27, x5
mul x6, x27, x12
umulh x2, x27, x12
umulh x15, x27, x16
adds x28, x23, x14
adcs x20, x13, x10
adc x21, x24, x10
adds x5, x4, x25
adcs x12, x9, x1
adcs x16, x8, x6
adcs x23, x11, x22
adc x14, x17, x10
umulh x13, x28, x20
umulh x24, x28, x21
umulh x25, x28, x7
mul x4, x20, x21
mul x9, x28, x7
umulh x1, x20, x7
mul x6, x28, x21
adds x8, x23, x2
adc x22, x14, x10
umulh x11, x21, x7
adds x17, x6, x13
adcs x2, x9, x24
adc x23, x25, x10
mul x14, x20, x7
umulh x6, x20, x21
extr x13, x22, x8, #63
and x9, x8, #0x7fffffffffffffff
mul x24, x13, x26
adds x25, x2, x4
adcs x22, x23, x14
adc x8, x1, x10
umulh x13, x20, x20
mul x4, x21, x7
adds x2, x5, x24
adcs x23, x12, x15
adcs x14, x16, x3
adc x1, x9, x10
umulh x5, x7, x7
mul x24, x7, x7
umulh x15, x21, x21
adds x12, x22, x6
adcs x3, x8, x4
adc x16, x11, x10
mul x9, x21, x21
extr x7, x25, x17, #63
umulh x22, x28, x28
mul x6, x28, x20
mul x8, x20, x20
mul x4, x28, x28
stp x2, x23, [x0, #192]
stp x14, x1, [x0, #208]
ldr x11, [x0, #64]
extr x21, x12, x25, #63
extr x20, x3, x12, #63
extr x28, x16, x3, #63
lsr x2, x16, #63
extr x23, x17, x6, #63
lsl x14, x6, #1
ldr x1, [x0, #72]
adds x25, x14, x22
adcs x12, x23, x8
adcs x3, x7, x13
adcs x16, x21, x9
adcs x17, x20, x15
adcs x6, x28, x24
adc x14, x2, x5
ldp x22, x8, [x0, #192]
ldp x23, x13, [x0, #208]
umulh x7, x11, x22
umulh x21, x11, x23
mul x9, x11, x13
umulh x20, x11, x8
mul x15, x11, x23
mul x28, x27, x16
umulh x24, x27, x16
mul x5, x27, x17
umulh x2, x27, x17
mul x16, x27, x6
umulh x17, x27, x6
mul x6, x27, x14
umulh x14, x27, x14
adds x28, x4, x28
adcs x4, x25, x5
adcs x25, x12, x16
adcs x5, x3, x6
adc x16, x14, x10
adds x12, x5, x17
adc x3, x16, x10
umulh x6, x11, x13
extr x14, x3, x12, #63
and x5, x12, #0x7fffffffffffffff
mul x17, x14, x26
adds x16, x28, x17
adcs x3, x4, x24
adcs x12, x25, x2
adc x14, x5, x10
mul x28, x1, x8
mul x17, x11, x8
mul x24, x1, x22
mul x4, x11, x22
adds x2, x17, x7
adcs x25, x15, x20
adcs x5, x9, x21
adc x11, x6, x10
mul x17, x1, x23
mul x7, x1, x13
umulh x15, x1, x22
stp x16, x3, [x0, #160]
umulh x20, x1, x13
umulh x9, x1, x8
umulh x21, x1, x23
stp x12, x14, [x0, #176]
ldr x6, [x0, #80]
ldr x3, [x0, #88]
adds x16, x2, x24
adcs x1, x25, x28
adcs x12, x5, x17
adcs x14, x11, x7
adc x2, x10, x10
mul x24, x6, x22
mul x25, x6, x13
mul x28, x6, x23
adds x5, x1, x15
adcs x17, x12, x9
adcs x7, x14, x21
adc x11, x2, x20
mul x1, x6, x8
umulh x15, x6, x8
umulh x12, x6, x13
umulh x9, x6, x23
umulh x21, x6, x22
adds x14, x5, x24
adcs x20, x17, x1
adcs x2, x7, x28
adcs x6, x11, x25
adc x5, x10, x10
mul x24, x3, x23
umulh x1, x3, x23
mul x17, x3, x13
umulh x28, x3, x13
mul x7, x3, x8
umulh x25, x3, x8
adds x11, x20, x21
adcs x23, x2, x15
adcs x13, x6, x9
adc x8, x5, x12
mul x21, x3, x22
umulh x20, x3, x22
adds x15, x11, x21
adcs x2, x23, x7
adcs x9, x13, x24
adcs x6, x8, x17
adc x12, x10, x10
adds x5, x2, x20
adcs x3, x9, x25
adcs x22, x6, x1
adc x21, x12, x28
umulh x11, x27, x21
mul x7, x27, x3
mul x23, x27, x5
mul x24, x27, x22
mul x13, x27, x21
umulh x17, x27, x22
umulh x8, x27, x5
umulh x20, x27, x3
adds x2, x4, x23
adcs x25, x16, x7
adcs x9, x14, x24
adcs x6, x15, x13
adc x1, x11, x10
adds x12, x6, x17
adc x28, x1, x10
extr x21, x28, x12, #63
and x22, x12, #0x7fffffffffffffff
mul x5, x21, x26
adds x3, x2, x5
adcs x4, x25, x8
adcs x23, x9, x20
adc x16, x22, x10
stp x3, x4, [x0, #192]
stp x23, x16, [x0, #208]
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
.globl lab_sc_o3_19_30_0
lab_sc_o3_19_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
stp x6, x15, [x0, #256]
stp x9, x21, [x0, #224]
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x6, x16, x5
adcs x15, x1, x28
csel x9, x27, x10, hs
stp x17, x3, [x0, #240]
stp x8, x23, [x0, #272]
ldp x21, x11, [x0, #224]
subs x25, x12, x14
sbcs x24, x20, x10
sbcs x7, x13, x10
sbc x16, x4, x10
adds x5, x22, x9
adcs x28, x2, x10
adc x1, x6, x10
ldp x17, x3, [x0, #240]
umulh x8, x21, x11
stp x25, x24, [x0, #320]
stp x5, x28, [x0, #288]
stp x1, x15, [x0, #304]
stp x7, x16, [x0, #336]
mul x23, x21, x11
umulh x12, x21, x21
umulh x14, x11, x11
mul x20, x11, x11
mul x13, x21, x21
umulh x4, x21, x17
umulh x22, x21, x3
mul x9, x21, x17
mul x2, x21, x3
umulh x6, x11, x3
mul x25, x11, x17
mul x24, x11, x3
umulh x5, x11, x17
umulh x28, x17, x3
mul x1, x17, x3
umulh x15, x17, x17
mul x7, x17, x17
adds x16, x9, x8
adcs x21, x2, x4
adc x11, x22, x10
umulh x17, x3, x3
mul x8, x3, x3
lsl x9, x23, #1
adds x2, x21, x25
adcs x4, x11, x24
adc x22, x6, x10
extr x3, x16, x23, #63
adds x21, x4, x5
adcs x25, x22, x1
adc x11, x28, x10
extr x24, x2, x16, #63
lsr x6, x11, #63
extr x23, x11, x25, #63
extr x5, x25, x21, #63
extr x4, x21, x2, #63
adds x1, x9, x12
adcs x22, x3, x20
adcs x28, x24, x14
adcs x16, x4, x7
adcs x11, x5, x15
adcs x25, x23, x8
adc x21, x6, x17
ldp x2, x9, [x0, #256]
ldp x12, x3, [x0, #272]
umulh x20, x2, x9
umulh x14, x2, x12
mul x24, x2, x12
mul x7, x2, x3
mul x4, x2, x9
umulh x5, x27, x21
mul x15, x27, x21
mul x8, x27, x16
umulh x23, x27, x16
mul x17, x27, x11
umulh x6, x27, x11
mul x21, x27, x25
umulh x16, x27, x25
adds x11, x13, x8
adcs x25, x1, x17
adcs x8, x22, x21
adcs x13, x28, x15
adc x1, x5, x10
umulh x17, x2, x3
umulh x21, x9, x3
adds x22, x24, x20
adcs x15, x7, x14
adc x28, x17, x10
mul x5, x9, x12
mul x24, x9, x3
adds x20, x13, x16
adc x7, x1, x10
umulh x14, x9, x12
adds x17, x15, x5
adcs x13, x28, x24
adc x16, x21, x10
umulh x1, x12, x3
mul x15, x12, x3
extr x5, x7, x20, #63
and x28, x20, #0x7fffffffffffffff
mul x24, x5, x26
adds x21, x13, x14
adcs x7, x16, x15
adc x20, x1, x10
adds x5, x11, x24
adcs x13, x25, x23
adcs x14, x8, x6
adc x16, x28, x10
extr x15, x17, x22, #63
extr x1, x22, x4, #63
lsr x11, x20, #63
extr x24, x20, x7, #63
extr x25, x7, x21, #63
extr x23, x21, x17, #63
stp x5, x13, [x0, #352]
lsl x8, x4, #1
stp x14, x16, [x0, #368]
umulh x6, x2, x2
umulh x28, x9, x9
umulh x22, x12, x12
mul x20, x9, x9
mul x7, x12, x12
umulh x17, x3, x3
mul x21, x3, x3
mul x5, x2, x2
adds x13, x8, x6
adcs x4, x1, x20
adcs x14, x15, x28
adcs x16, x23, x7
adcs x9, x25, x22
adcs x12, x24, x21
adc x3, x11, x17
ldp x2, x6, [x0, #224]
ldp x8, x20, [x0, #240]
ldr x1, [x0, #320]
mul x28, x1, x6
mul x15, x1, x8
mul x23, x1, x20
mul x7, x1, x2
umulh x25, x27, x3
mul x22, x27, x3
mul x24, x27, x16
umulh x21, x27, x16
mul x11, x27, x9
umulh x17, x27, x9
mul x3, x27, x12
umulh x16, x27, x12
adds x9, x5, x24
adcs x12, x13, x11
adcs x24, x4, x3
adcs x5, x14, x22
adc x11, x25, x10
umulh x13, x1, x2
umulh x4, x1, x6
adds x3, x5, x16
adc x14, x11, x10
umulh x22, x1, x8
umulh x25, x1, x20
extr x5, x14, x3, #63
and x16, x3, #0x7fffffffffffffff
mul x11, x5, x26
adds x1, x28, x13
adcs x14, x15, x4
adcs x3, x23, x22
adc x5, x25, x10
ldr x28, [x0, #328]
adds x13, x9, x11
adcs x15, x12, x21
adcs x4, x24, x17
adc x23, x16, x10
mul x22, x28, x2
mul x25, x28, x6
mul x9, x28, x8
mul x11, x28, x20
umulh x21, x28, x2
stp x13, x15, [x0, #384]
umulh x12, x28, x6
umulh x24, x28, x8
umulh x17, x28, x20
stp x4, x23, [x0, #400]
ldr x16, [x0, #336]
adds x13, x1, x22
adcs x15, x14, x25
adcs x28, x3, x9
adcs x4, x5, x11
adc x23, x10, x10
ldr x1, [x0, #344]
mul x22, x16, x2
mul x14, x16, x6
mul x25, x16, x8
adds x9, x15, x21
adcs x3, x28, x12
adcs x11, x4, x24
adc x5, x23, x17
mul x15, x16, x20
umulh x21, x16, x2
umulh x12, x16, x6
umulh x28, x16, x8
umulh x24, x16, x20
adds x4, x9, x22
adcs x17, x3, x14
adcs x23, x11, x25
adcs x16, x5, x15
adc x22, x10, x10
mul x9, x1, x2
umulh x14, x1, x2
mul x3, x1, x6
umulh x25, x1, x6
mul x11, x1, x8
umulh x15, x1, x8
adds x5, x17, x21
adcs x2, x23, x12
adcs x6, x16, x28
adc x8, x22, x24
mul x21, x1, x20
umulh x17, x1, x20
adds x12, x5, x9
adcs x23, x2, x3
adcs x28, x6, x11
adcs x16, x8, x21
adc x22, x10, x10
ldp x24, x1, [x0, #256]
ldr x20, [x0, #288]
ldp x9, x5, [x0, #272]
adds x3, x23, x14
adcs x2, x28, x25
adcs x11, x16, x15
adc x6, x22, x17
mul x8, x20, x1
mul x21, x20, x9
mul x14, x20, x5
mul x23, x20, x24
umulh x28, x27, x6
mul x25, x27, x6
mul x16, x27, x3
umulh x15, x27, x3
mul x22, x27, x2
umulh x17, x27, x2
mul x6, x27, x11
umulh x3, x27, x11
adds x2, x7, x16
adcs x11, x13, x22
adcs x7, x4, x6
adcs x16, x12, x25
adc x13, x28, x10
umulh x22, x20, x24
umulh x4, x20, x1
adds x6, x16, x3
adc x12, x13, x10
umulh x25, x20, x9
umulh x28, x20, x5
extr x3, x12, x6, #63
and x16, x6, #0x7fffffffffffffff
mul x13, x3, x26
adds x20, x8, x22
adcs x12, x21, x4
adcs x6, x14, x25
adc x3, x28, x10
ldr x22, [x0, #296]
adds x8, x2, x13
adcs x21, x11, x15
adcs x4, x7, x17
adc x14, x16, x10
mul x25, x22, x24
mul x28, x22, x1
mul x2, x22, x9
mul x13, x22, x5
umulh x11, x22, x24
stp x8, x21, [x0, #448]
umulh x15, x22, x1
umulh x17, x22, x9
umulh x7, x22, x5
stp x4, x14, [x0, #464]
ldr x16, [x0, #304]
adds x8, x20, x25
adcs x21, x12, x28
adcs x22, x6, x2
adcs x14, x3, x13
adc x4, x10, x10
ldr x25, [x0, #312]
mul x20, x16, x24
mul x28, x16, x1
mul x12, x16, x9
adds x6, x21, x11
adcs x2, x22, x15
adcs x3, x14, x17
adc x13, x4, x7
mul x21, x16, x5
umulh x11, x16, x24
umulh x22, x16, x1
umulh x15, x16, x9
umulh x14, x16, x5
adds x17, x6, x20
adcs x4, x2, x28
adcs x7, x3, x12
adcs x16, x13, x21
adc x6, x10, x10
mul x20, x25, x24
umulh x2, x25, x24
mul x28, x25, x1
umulh x3, x25, x1
mul x12, x25, x9
umulh x21, x25, x9
adds x13, x4, x11
adcs x24, x7, x22
adcs x1, x16, x15
adc x9, x6, x14
mul x4, x25, x5
umulh x11, x25, x5
adds x7, x13, x20
adcs x22, x24, x28
adcs x15, x1, x12
adcs x16, x9, x4
adc x14, x10, x10
ldp x6, x5, [x0, #352]
ldp x25, x13, [x0, #368]
ldp x20, x28, [x0, #384]
adds x24, x22, x2
adcs x12, x15, x3
adcs x1, x16, x21
adc x4, x14, x11
ldp x9, x2, [x0, #400]
umulh x22, x27, x4
mul x3, x27, x4
mul x15, x27, x24
umulh x21, x27, x24
mul x16, x27, x12
umulh x11, x27, x12
subs x14, x6, x20
sbcs x4, x5, x28
sbcs x24, x25, x9
sbcs x12, x13, x2
csel x20, x10, x27, hs
mul x6, x27, x1
umulh x28, x27, x1
adds x5, x23, x15
adcs x25, x8, x16
adcs x9, x17, x6
adcs x13, x7, x3
adc x2, x22, x10
ldp x1, x15, [x0, #384]
ldr x23, [x0, #352]
subs x16, x14, x20
sbcs x8, x4, x10
sbcs x17, x24, x10
sbc x6, x12, x10
ldp x3, x7, [x0, #400]
adds x22, x13, x28
adc x20, x2, x10
mul x14, x23, x15
stp x17, x6, [x0, #432]
stp x16, x8, [x0, #416]
mul x4, x23, x1
mul x24, x23, x3
extr x12, x20, x22, #63
and x13, x22, #0x7fffffffffffffff
umulh x28, x23, x1
umulh x2, x23, x15
mul x17, x12, x26
umulh x6, x23, x3
mul x16, x23, x7
adds x8, x5, x17
adcs x20, x25, x21
adcs x22, x9, x11
adc x12, x13, x10
umulh x5, x23, x7
stp x8, x20, [x0, #480]
stp x22, x12, [x0, #496]
ldr x17, [x0, #360]
adds x25, x14, x28
adcs x21, x24, x2
adcs x9, x16, x6
adc x11, x5, x10
ldr x13, [x0, #368]
mul x23, x17, x1
mul x8, x17, x15
mul x20, x17, x3
mul x22, x17, x7
umulh x12, x17, x1
umulh x28, x17, x15
umulh x14, x17, x3
umulh x2, x17, x7
mul x24, x13, x1
adds x6, x25, x23
adcs x16, x21, x8
adcs x5, x9, x20
adcs x17, x11, x22
adc x23, x10, x10
mul x25, x13, x15
mul x8, x13, x3
mul x21, x13, x7
adds x20, x16, x12
adcs x9, x5, x28
adcs x22, x17, x14
adc x11, x23, x2
umulh x12, x13, x1
umulh x16, x13, x15
umulh x28, x13, x3
umulh x5, x13, x7
ldr x17, [x0, #376]
adds x14, x20, x24
adcs x23, x9, x25
adcs x2, x22, x8
adcs x13, x11, x21
adc x24, x10, x10
mul x20, x17, x1
umulh x25, x17, x1
mul x9, x17, x15
umulh x22, x17, x15
mul x8, x17, x3
umulh x11, x17, x3
adds x21, x23, x12
adcs x1, x2, x16
adcs x15, x13, x28
adc x3, x24, x5
mul x23, x17, x7
umulh x12, x17, x7
adds x2, x21, x20
adcs x16, x1, x9
adcs x13, x15, x8
adcs x28, x3, x23
adc x24, x10, x10
ldp x5, x7, [x0, #416]
ldp x17, x21, [x0, #352]
ldp x20, x1, [x0, #368]
adds x9, x16, x25
adcs x15, x13, x22
adcs x8, x28, x11
adc x23, x24, x12
movz x3, #56129, lsl #0
ldp x16, x25, [x0, #432]
movk x3, #1, lsl #16
mul x13, x5, x3
umulh x22, x27, x23
mul x11, x27, x23
mul x28, x27, x9
umulh x12, x27, x9
mul x24, x27, x15
umulh x23, x27, x15
mul x9, x27, x8
umulh x15, x27, x8
adds x8, x4, x28
adcs x4, x6, x24
adcs x28, x14, x9
adcs x6, x2, x11
adc x24, x22, x10
umulh x9, x5, x3
umulh x14, x25, x3
mul x2, x25, x3
adds x11, x6, x15
adc x22, x24, x10
mul x5, x7, x3
umulh x25, x7, x3
extr x6, x22, x11, #63
and x15, x11, #0x7fffffffffffffff
mul x24, x6, x26
adds x7, x8, x24
adcs x22, x4, x12
adcs x11, x28, x23
adc x6, x15, x10
mul x8, x16, x3
umulh x24, x16, x3
adds x12, x17, x13
adcs x4, x21, x5
adcs x28, x20, x8
adcs x23, x1, x2
adc x15, x14, x10
stp x7, x22, [x0, #96]
stp x11, x6, [x0, #112]
ldr x16, [x0, #416]
ldr x3, [x0, #424]
adds x17, x23, x23
adc x13, x15, x15
mul x21, x13, x26
lsr x5, x17, #1
adds x8, x12, x21
adcs x20, x4, x9
adcs x2, x28, x25
adc x1, x5, x24
stp x8, x20, [x0, #128]
stp x2, x1, [x0, #144]
ldp x14, x7, [x0, #128]
ldp x22, x11, [x0, #144]
ldr x6, [x0, #432]
umulh x23, x16, x14
umulh x15, x16, x7
umulh x13, x16, x22
umulh x17, x16, x11
mul x12, x16, x7
mul x21, x16, x22
mul x9, x16, x11
mul x4, x3, x14
mul x25, x3, x7
mul x28, x3, x22
mul x24, x3, x11
umulh x5, x3, x14
mul x20, x16, x14
adds x8, x12, x23
adcs x2, x21, x15
adcs x1, x9, x13
adc x16, x17, x10
umulh x12, x3, x7
umulh x23, x3, x22
umulh x21, x3, x11
mul x15, x6, x14
adds x9, x8, x4
adcs x13, x2, x25
adcs x17, x1, x28
adcs x3, x16, x24
adc x8, x10, x10
mul x4, x6, x7
mul x2, x6, x22
mul x25, x6, x11
adds x1, x13, x5
adcs x28, x17, x12
adcs x24, x3, x23
adc x16, x8, x21
umulh x13, x6, x14
umulh x5, x6, x7
umulh x17, x6, x22
umulh x12, x6, x11
ldr x23, [x0, #440]
adds x3, x1, x15
adcs x21, x28, x4
adcs x8, x24, x2
adcs x6, x16, x25
adc x1, x10, x10
mul x15, x23, x14
umulh x4, x23, x14
mul x28, x23, x7
umulh x2, x23, x7
mul x24, x23, x22
umulh x25, x23, x22
adds x16, x21, x13
adcs x14, x8, x5
adcs x7, x6, x17
adc x22, x1, x12
mul x13, x23, x11
umulh x21, x23, x11
adds x5, x16, x15
adcs x8, x14, x28
adcs x17, x7, x24
adcs x6, x22, x13
adc x12, x10, x10
ldp x1, x23, [x0, #448]
ldp x11, x15, [x0, #464]
ldp x16, x28, [x0, #480]
adds x14, x8, x4
adcs x24, x17, x2
adcs x7, x6, x25
adc x13, x12, x21
ldp x22, x4, [x0, #496]
umulh x8, x27, x13
mul x2, x27, x13
mul x17, x27, x14
umulh x6, x27, x14
subs x25, x1, x16
sbcs x12, x23, x28
sbcs x21, x11, x22
sbcs x13, x15, x4
csel x14, x10, x27, hs
mul x1, x27, x24
umulh x16, x27, x24
mul x23, x27, x7
umulh x28, x27, x7
adds x11, x20, x17
adcs x22, x9, x1
adcs x15, x3, x23
adcs x4, x5, x2
adc x24, x8, x10
subs x7, x25, x14
sbcs x20, x12, x10
sbcs x17, x21, x10
sbc x9, x13, x10
adds x1, x4, x28
adc x3, x24, x10
umulh x23, x7, x20
umulh x2, x7, x17
umulh x5, x7, x9
mul x8, x7, x17
mul x25, x7, x9
mul x14, x20, x17
mul x12, x20, x9
umulh x21, x20, x17
extr x13, x3, x1, #63
and x28, x1, #0x7fffffffffffffff
mul x4, x13, x26
adds x24, x11, x4
adcs x3, x22, x6
adcs x1, x15, x16
adc x13, x28, x10
adds x11, x8, x23
adcs x4, x25, x2
adc x22, x5, x10
umulh x6, x20, x9
umulh x15, x17, x9
mul x16, x17, x9
mul x28, x7, x20
stp x24, x3, [x0, #128]
stp x1, x13, [x0, #144]
umulh x8, x7, x7
adds x23, x4, x14
adcs x25, x22, x12
adc x2, x6, x10
umulh x5, x20, x20
mul x24, x20, x20
umulh x3, x17, x17
mul x1, x17, x17
umulh x13, x9, x9
mul x4, x9, x9
mul x14, x7, x7
extr x12, x11, x28, #63
lsl x22, x28, #1
adds x6, x25, x21
adcs x20, x2, x16
adc x17, x15, x10
extr x9, x23, x11, #63
lsr x7, x17, #63
extr x28, x17, x20, #63
extr x25, x20, x6, #63
extr x21, x6, x23, #63
adds x2, x22, x8
adcs x16, x12, x24
adcs x15, x9, x5
adcs x11, x21, x1
adcs x17, x25, x3
adcs x20, x28, x4
adc x23, x7, x13
ldp x6, x22, [x0, #448]
ldp x8, x12, [x0, #464]
ldp x24, x5, [x0, #480]
ldp x9, x21, [x0, #496]
adds x1, x6, x24
adcs x25, x22, x5
adcs x3, x8, x9
adcs x4, x12, x21
csel x28, x27, x10, hs
umulh x13, x27, x23
mul x7, x27, x23
mul x6, x27, x11
umulh x24, x27, x11
mul x22, x27, x17
umulh x5, x27, x17
mul x9, x27, x20
umulh x8, x27, x20
adds x21, x14, x6
adcs x12, x2, x22
adcs x23, x16, x9
adcs x11, x15, x7
adc x17, x13, x10
adds x20, x1, x28
adcs x6, x25, x10
adc x14, x3, x10
umulh x2, x20, x6
umulh x22, x20, x14
umulh x9, x20, x4
adds x16, x11, x8
adc x7, x17, x10
mul x15, x20, x14
mul x13, x20, x4
umulh x1, x6, x4
mul x28, x6, x14
mul x25, x6, x4
extr x3, x7, x16, #63
and x8, x16, #0x7fffffffffffffff
mul x11, x3, x26
adds x17, x15, x2
adcs x7, x13, x22
adc x16, x9, x10
umulh x3, x6, x14
umulh x15, x14, x4
adds x2, x21, x11
adcs x13, x12, x24
adcs x22, x23, x5
adc x9, x8, x10
mul x21, x14, x4
adds x11, x7, x28
adcs x24, x16, x25
adc x12, x1, x10
mul x5, x20, x6
stp x2, x13, [x0, #192]
stp x22, x9, [x0, #208]
adds x23, x24, x3
adcs x8, x12, x21
adc x28, x15, x10
umulh x7, x20, x20
umulh x16, x6, x6
umulh x25, x14, x14
umulh x1, x4, x4
mul x2, x6, x6
mul x13, x14, x14
mul x22, x4, x4
mul x9, x20, x20
extr x24, x11, x17, #63
extr x3, x23, x11, #63
extr x12, x8, x23, #63
extr x21, x28, x8, #63
lsr x15, x28, #63
extr x6, x17, x5, #63
lsl x14, x5, #1
adds x4, x14, x7
adcs x20, x6, x2
adcs x11, x24, x16
adcs x23, x3, x13
adcs x8, x12, x25
adcs x28, x21, x22
adc x17, x15, x1
ldp x5, x14, [x0, #192]
ldp x7, x2, [x0, #208]
ldr x6, [x0, #64]
mul x16, x6, x14
mul x24, x6, x7
mul x3, x6, x2
umulh x13, x27, x17
mul x12, x27, x17
mul x25, x27, x23
umulh x21, x6, x5
umulh x22, x27, x23
mul x1, x27, x8
umulh x15, x27, x8
mul x17, x27, x28
umulh x23, x27, x28
adds x8, x9, x25
adcs x28, x4, x1
adcs x25, x20, x17
adcs x9, x11, x12
adc x4, x13, x10
umulh x1, x6, x14
umulh x17, x6, x7
adds x20, x9, x23
adc x11, x4, x10
umulh x12, x6, x2
mul x13, x6, x5
extr x9, x11, x20, #63
and x23, x20, #0x7fffffffffffffff
mul x4, x9, x26
adds x6, x16, x21
adcs x11, x24, x1
adcs x20, x3, x17
adc x9, x12, x10
ldr x16, [x0, #72]
adds x21, x8, x4
adcs x24, x28, x22
adcs x1, x25, x15
adc x3, x23, x10
mul x17, x16, x5
mul x12, x16, x14
mul x8, x16, x7
mul x4, x16, x2
umulh x22, x16, x5
stp x21, x24, [x0, #160]
umulh x28, x16, x14
umulh x15, x16, x7
umulh x25, x16, x2
stp x1, x3, [x0, #176]
ldr x23, [x0, #80]
adds x24, x6, x17
adcs x21, x11, x12
adcs x16, x20, x8
adcs x1, x9, x4
adc x3, x10, x10
ldr x6, [x0, #88]
mul x17, x23, x5
mul x11, x23, x14
mul x12, x23, x7
adds x20, x21, x22
adcs x8, x16, x28
adcs x4, x1, x15
adc x9, x3, x25
mul x21, x23, x2
umulh x22, x23, x5
umulh x16, x23, x14
umulh x28, x23, x7
umulh x15, x23, x2
adds x1, x20, x17
adcs x25, x8, x11
adcs x3, x4, x12
adcs x23, x9, x21
adc x20, x10, x10
mul x17, x6, x5
umulh x11, x6, x5
mul x8, x6, x14
umulh x12, x6, x14
mul x4, x6, x7
umulh x21, x6, x7
adds x9, x25, x22
adcs x5, x3, x16
adcs x14, x23, x28
adc x7, x20, x15
mul x22, x6, x2
umulh x25, x6, x2
adds x16, x9, x17
adcs x3, x5, x8
adcs x28, x14, x4
adcs x23, x7, x22
adc x15, x10, x10
adds x20, x3, x11
adcs x6, x28, x12
adcs x2, x23, x21
adc x17, x15, x25
umulh x9, x27, x17
mul x8, x27, x20
mul x5, x27, x6
mul x4, x27, x2
mul x14, x27, x17
umulh x22, x27, x2
umulh x7, x27, x20
umulh x11, x27, x6
adds x3, x13, x8
adcs x12, x24, x5
adcs x28, x1, x4
adcs x23, x16, x14
adc x21, x9, x10
adds x15, x23, x22
adc x25, x21, x10
extr x17, x25, x15, #63
and x2, x15, #0x7fffffffffffffff
mul x20, x17, x26
adds x6, x3, x20
adcs x13, x12, x7
adcs x8, x28, x11
adc x24, x2, x10
stp x6, x13, [x0, #192]
stp x8, x24, [x0, #208]
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
.globl lab_sc_o3_19_30_1
lab_sc_o3_19_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
umulh x3, x12, x9
umulh x7, x12, x25
umulh x11, x12, x24
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
mul x4, x12, x24
mul x8, x12, x25
umulh x2, x9, x24
mul x13, x25, x24
umulh x17, x9, x25
mul x14, x9, x24
umulh x1, x25, x24
mul x6, x9, x25
mul x20, x12, x9
adds x22, x8, x3
adcs x16, x4, x7
adc x23, x11, x10
umulh x15, x25, x25
mul x21, x25, x25
umulh x5, x9, x9
mul x28, x9, x9
umulh x3, x24, x24
mul x8, x24, x24
umulh x4, x12, x12
mul x7, x12, x12
lsl x11, x20, #1
adds x25, x16, x6
adcs x9, x23, x14
adc x24, x2, x10
extr x12, x22, x20, #63
adds x16, x9, x17
adcs x6, x24, x13
adc x23, x1, x10
extr x14, x25, x22, #63
lsr x2, x23, #63
extr x20, x23, x6, #63
extr x17, x6, x16, #63
extr x9, x16, x25, #63
adds x13, x11, x4
adcs x24, x12, x28
adcs x1, x14, x5
adcs x22, x9, x21
adcs x23, x17, x15
adcs x6, x20, x8
adc x16, x2, x3
ldp x25, x11, [x0, #272]
ldp x4, x12, [x0, #256]
umulh x28, x4, x12
umulh x5, x4, x25
mul x14, x4, x25
mul x21, x4, x11
mul x9, x4, x12
umulh x17, x27, x16
mul x15, x27, x16
mul x8, x27, x22
umulh x20, x27, x22
mul x3, x27, x23
umulh x2, x27, x23
mul x16, x27, x6
umulh x22, x27, x6
adds x23, x7, x8
adcs x6, x13, x3
adcs x8, x24, x16
adcs x7, x1, x15
adc x13, x17, x10
umulh x3, x4, x11
umulh x16, x12, x11
adds x24, x14, x28
adcs x15, x21, x5
adc x1, x3, x10
mul x17, x12, x11
umulh x14, x12, x25
adds x28, x7, x22
adc x21, x13, x10
umulh x5, x25, x11
extr x3, x21, x28, #63
and x7, x28, #0x7fffffffffffffff
mul x22, x3, x26
adds x13, x23, x22
adcs x21, x6, x20
adcs x28, x8, x2
adc x3, x7, x10
mul x23, x25, x11
mul x22, x12, x25
extr x6, x24, x9, #63
adds x20, x15, x22
adcs x8, x1, x17
adc x2, x16, x10
stp x28, x3, [x0, #368]
stp x13, x21, [x0, #352]
umulh x7, x12, x12
mul x15, x12, x12
lsl x22, x9, #1
umulh x1, x4, x4
mul x17, x25, x25
umulh x16, x25, x25
mul x28, x4, x4
adds x3, x8, x14
adcs x13, x2, x23
adc x21, x5, x10
extr x12, x20, x24, #63
umulh x9, x11, x11
mul x25, x11, x11
lsr x4, x21, #63
extr x8, x21, x13, #63
extr x14, x13, x3, #63
extr x2, x3, x20, #63
adds x23, x22, x1
adcs x5, x6, x15
adcs x24, x12, x7
adcs x11, x2, x17
adcs x21, x14, x16
adcs x13, x8, x25
adc x20, x4, x9
ldp x3, x1, [x0, #240]
ldr x22, [x0, #320]
ldp x15, x6, [x0, #224]
mul x7, x22, x3
mul x12, x22, x6
mul x2, x22, x1
mul x17, x22, x15
mul x14, x27, x11
umulh x16, x22, x15
umulh x8, x27, x11
mul x25, x27, x21
umulh x4, x27, x21
mul x9, x27, x13
umulh x11, x27, x13
mul x21, x27, x20
umulh x13, x27, x20
adds x20, x28, x14
adcs x14, x23, x25
adcs x28, x5, x9
adcs x25, x24, x21
adc x23, x13, x10
umulh x5, x22, x1
adds x9, x25, x11
adc x24, x23, x10
umulh x21, x22, x3
umulh x13, x22, x6
extr x25, x24, x9, #63
and x11, x9, #0x7fffffffffffffff
mul x23, x25, x26
adds x22, x12, x16
adcs x24, x7, x13
adcs x9, x2, x21
adc x25, x5, x10
ldr x12, [x0, #328]
adds x16, x20, x23
adcs x7, x14, x8
adcs x13, x28, x4
adc x2, x11, x10
mul x21, x12, x15
mul x5, x12, x1
mul x20, x12, x6
mul x23, x12, x3
umulh x8, x12, x1
stp x16, x7, [x0, #384]
umulh x14, x12, x3
umulh x28, x12, x15
umulh x4, x12, x6
stp x13, x2, [x0, #400]
ldr x11, [x0, #336]
adds x16, x22, x21
adcs x7, x24, x20
adcs x12, x9, x23
adcs x13, x25, x5
adc x2, x10, x10
ldr x22, [x0, #344]
mul x21, x11, x15
mul x24, x11, x1
mul x20, x11, x6
adds x23, x7, x28
adcs x9, x12, x4
adcs x5, x13, x14
adc x25, x2, x8
mul x7, x11, x3
umulh x28, x11, x3
umulh x4, x11, x15
umulh x12, x11, x1
umulh x14, x11, x6
adds x13, x23, x21
adcs x8, x9, x20
adcs x2, x5, x7
adcs x11, x25, x24
adc x21, x10, x10
mul x23, x22, x1
umulh x20, x22, x1
mul x9, x22, x15
umulh x7, x22, x15
umulh x5, x22, x6
mul x24, x22, x6
adds x25, x8, x4
adcs x1, x2, x14
adcs x15, x11, x28
adc x6, x21, x12
mul x4, x22, x3
umulh x8, x22, x3
adds x14, x25, x9
adcs x2, x1, x24
adcs x28, x15, x4
adcs x11, x6, x23
adc x21, x10, x10
ldp x12, x22, [x0, #256]
ldr x3, [x0, #288]
ldp x9, x25, [x0, #272]
adds x24, x2, x7
adcs x1, x28, x5
adcs x4, x11, x8
adc x15, x21, x20
mul x6, x3, x22
mul x23, x3, x25
mul x7, x3, x9
mul x2, x3, x12
umulh x28, x27, x15
mul x5, x27, x15
umulh x11, x27, x4
mul x8, x27, x4
mul x21, x27, x24
umulh x20, x27, x24
mul x15, x27, x1
umulh x4, x27, x1
adds x24, x17, x21
adcs x1, x16, x15
adcs x17, x13, x8
adcs x21, x14, x5
adc x16, x28, x10
umulh x15, x3, x9
umulh x13, x3, x22
adds x8, x21, x11
adc x14, x16, x10
umulh x5, x3, x12
umulh x28, x3, x25
extr x11, x14, x8, #63
and x21, x8, #0x7fffffffffffffff
mul x16, x11, x26
adds x3, x6, x5
adcs x14, x7, x13
adcs x8, x23, x15
adc x11, x28, x10
ldr x5, [x0, #296]
adds x6, x24, x16
adcs x7, x1, x20
adcs x13, x17, x4
adc x23, x21, x10
mul x15, x5, x12
mul x28, x5, x22
umulh x24, x5, x22
umulh x16, x5, x25
mul x1, x5, x9
stp x6, x7, [x0, #448]
umulh x20, x5, x12
mul x4, x5, x25
umulh x17, x5, x9
stp x13, x23, [x0, #464]
ldr x21, [x0, #304]
adds x6, x3, x15
adcs x7, x14, x28
adcs x5, x8, x1
adcs x23, x11, x4
adc x13, x10, x10
ldr x15, [x0, #312]
mul x3, x21, x12
mul x28, x21, x9
umulh x14, x21, x12
adds x8, x7, x20
adcs x1, x5, x24
adcs x11, x23, x17
adc x4, x13, x16
mul x7, x21, x22
umulh x20, x21, x9
mul x5, x21, x25
umulh x24, x21, x25
umulh x23, x21, x22
adds x17, x8, x3
adcs x13, x1, x7
adcs x16, x11, x28
adcs x21, x4, x5
adc x8, x10, x10
mul x3, x15, x9
umulh x1, x15, x9
mul x7, x15, x25
umulh x11, x15, x25
umulh x28, x15, x12
mul x5, x15, x12
adds x4, x13, x14
adcs x9, x16, x23
adcs x25, x21, x20
adc x12, x8, x24
mul x13, x15, x22
umulh x14, x15, x22
adds x16, x4, x5
adcs x23, x9, x13
adcs x20, x25, x3
adcs x21, x12, x7
adc x24, x10, x10
ldp x8, x22, [x0, #384]
ldp x15, x4, [x0, #368]
ldp x5, x13, [x0, #352]
adds x9, x23, x28
adcs x3, x20, x14
adcs x25, x21, x1
adc x7, x24, x11
ldp x12, x28, [x0, #400]
umulh x23, x27, x7
mul x14, x27, x7
mul x20, x27, x3
mul x1, x27, x25
umulh x21, x27, x25
umulh x11, x27, x3
subs x24, x5, x8
sbcs x7, x13, x22
sbcs x25, x15, x12
sbcs x3, x4, x28
csel x8, x10, x27, hs
mul x5, x27, x9
umulh x22, x27, x9
adds x13, x2, x5
adcs x15, x6, x20
adcs x12, x17, x1
adcs x4, x16, x14
adc x28, x23, x10
ldr x9, [x0, #352]
ldp x5, x2, [x0, #400]
subs x20, x24, x8
sbcs x6, x7, x10
sbcs x17, x25, x10
sbc x1, x3, x10
ldp x14, x16, [x0, #384]
adds x23, x4, x21
adc x8, x28, x10
mul x24, x9, x2
stp x17, x1, [x0, #432]
stp x20, x6, [x0, #416]
mul x7, x9, x5
mul x25, x9, x16
extr x3, x8, x23, #63
and x4, x23, #0x7fffffffffffffff
umulh x21, x9, x14
umulh x28, x9, x16
mul x17, x3, x26
umulh x1, x9, x5
mul x20, x9, x14
adds x6, x13, x17
adcs x8, x15, x22
adcs x23, x12, x11
adc x3, x4, x10
umulh x13, x9, x2
stp x6, x8, [x0, #480]
stp x23, x3, [x0, #496]
ldr x17, [x0, #360]
adds x15, x25, x21
adcs x22, x7, x28
adcs x12, x24, x1
adc x11, x13, x10
ldr x4, [x0, #368]
mul x9, x17, x14
mul x6, x17, x5
umulh x8, x17, x5
mul x23, x17, x16
mul x3, x17, x2
mul x21, x4, x2
umulh x25, x17, x2
mul x28, x4, x5
adds x7, x15, x9
adcs x1, x22, x23
adcs x24, x12, x6
adcs x13, x11, x3
adc x9, x10, x10
umulh x15, x17, x14
umulh x23, x17, x16
umulh x22, x4, x2
mul x6, x4, x14
adds x12, x1, x15
adcs x3, x24, x23
adcs x11, x13, x8
adc x17, x9, x25
umulh x15, x4, x5
mul x1, x4, x16
ldr x23, [x0, #376]
umulh x24, x4, x16
umulh x13, x4, x14
adds x8, x12, x6
adcs x9, x3, x1
adcs x25, x11, x28
adcs x4, x17, x21
adc x6, x10, x10
mul x12, x23, x14
umulh x1, x23, x14
mul x3, x23, x5
umulh x11, x23, x5
mul x28, x23, x2
umulh x17, x23, x2
adds x21, x9, x13
adcs x14, x25, x24
adcs x5, x4, x15
adc x2, x6, x22
mul x9, x23, x16
umulh x13, x23, x16
adds x25, x21, x12
adcs x24, x14, x9
adcs x4, x5, x3
adcs x15, x2, x28
adc x6, x10, x10
ldp x22, x16, [x0, #368]
ldp x23, x21, [x0, #416]
ldp x12, x14, [x0, #352]
adds x9, x24, x1
adcs x5, x4, x13
adcs x3, x15, x11
adc x28, x6, x17
movz x2, #56129, lsl #0
ldp x24, x1, [x0, #432]
movk x2, #1, lsl #16
mul x4, x23, x2
umulh x13, x27, x28
mul x11, x27, x28
mul x15, x27, x9
umulh x17, x27, x9
mul x6, x27, x5
umulh x28, x27, x5
mul x9, x27, x3
umulh x5, x27, x3
adds x3, x20, x15
adcs x20, x7, x6
adcs x15, x8, x9
adcs x7, x25, x11
adc x6, x13, x10
mul x9, x24, x2
umulh x8, x24, x2
umulh x25, x23, x2
adds x11, x7, x5
adc x13, x6, x10
umulh x24, x1, x2
mul x23, x1, x2
extr x7, x13, x11, #63
and x5, x11, #0x7fffffffffffffff
mul x6, x7, x26
adds x1, x3, x6
adcs x13, x20, x17
adcs x11, x15, x28
adc x7, x5, x10
mul x3, x21, x2
umulh x6, x21, x2
adds x17, x12, x4
adcs x20, x14, x3
adcs x15, x22, x9
adcs x28, x16, x23
adc x5, x24, x10
stp x11, x7, [x0, #112]
stp x1, x13, [x0, #96]
ldr x21, [x0, #416]
ldr x2, [x0, #424]
adds x12, x28, x28
adc x4, x5, x5
mul x14, x4, x26
lsr x3, x12, #1
adds x9, x17, x14
adcs x22, x20, x25
adcs x23, x15, x6
adc x16, x3, x8
stp x9, x22, [x0, #128]
stp x23, x16, [x0, #144]
ldp x24, x11, [x0, #128]
ldp x7, x1, [x0, #144]
ldr x13, [x0, #432]
umulh x28, x21, x24
umulh x5, x21, x7
umulh x4, x21, x1
umulh x12, x21, x11
mul x17, x21, x11
mul x14, x21, x1
mul x25, x2, x1
mul x20, x21, x7
umulh x6, x2, x7
mul x15, x2, x11
umulh x8, x2, x1
mul x3, x2, x24
mul x22, x21, x24
adds x9, x17, x28
adcs x23, x20, x12
adcs x16, x14, x5
adc x21, x4, x10
mul x17, x2, x7
umulh x28, x2, x24
umulh x20, x2, x11
mul x12, x13, x24
adds x14, x9, x3
adcs x5, x23, x15
adcs x4, x16, x17
adcs x2, x21, x25
adc x9, x10, x10
mul x3, x13, x11
mul x23, x13, x7
mul x15, x13, x1
adds x16, x5, x28
adcs x17, x4, x20
adcs x25, x2, x6
adc x21, x9, x8
umulh x5, x13, x11
umulh x28, x13, x1
umulh x4, x13, x7
umulh x20, x13, x24
ldr x6, [x0, #440]
adds x2, x16, x12
adcs x8, x17, x3
adcs x9, x25, x23
adcs x13, x21, x15
adc x16, x10, x10
mul x12, x6, x24
umulh x3, x6, x24
mul x17, x6, x1
umulh x23, x6, x1
mul x25, x6, x7
umulh x15, x6, x7
adds x21, x8, x20
adcs x24, x9, x5
adcs x1, x13, x4
adc x7, x16, x28
mul x20, x6, x11
umulh x8, x6, x11
adds x5, x21, x12
adcs x9, x24, x20
adcs x4, x1, x25
adcs x13, x7, x17
adc x28, x10, x10
ldp x16, x6, [x0, #480]
ldp x11, x12, [x0, #464]
ldp x21, x20, [x0, #448]
adds x24, x9, x3
adcs x25, x4, x8
adcs x1, x13, x15
adc x17, x28, x23
ldp x7, x3, [x0, #496]
umulh x9, x27, x17
mul x8, x27, x17
mul x4, x27, x25
mul x13, x27, x24
subs x15, x21, x16
sbcs x28, x20, x6
sbcs x23, x11, x7
sbcs x17, x12, x3
csel x21, x10, x27, hs
umulh x16, x27, x24
mul x20, x27, x1
umulh x6, x27, x1
umulh x11, x27, x25
adds x7, x22, x13
adcs x12, x14, x4
adcs x3, x2, x20
adcs x24, x5, x8
adc x1, x9, x10
subs x25, x15, x21
sbcs x22, x28, x10
sbcs x13, x23, x10
sbc x14, x17, x10
adds x4, x24, x6
adc x2, x1, x10
umulh x20, x25, x14
mul x8, x25, x14
umulh x5, x25, x13
mul x9, x25, x13
umulh x15, x25, x22
mul x21, x22, x14
umulh x28, x22, x13
mul x23, x22, x13
extr x17, x2, x4, #63
and x6, x4, #0x7fffffffffffffff
mul x24, x17, x26
adds x1, x7, x24
adcs x2, x12, x16
adcs x4, x3, x11
adc x17, x6, x10
adds x7, x9, x15
adcs x24, x8, x5
adc x12, x20, x10
umulh x16, x22, x14
mul x3, x13, x14
umulh x11, x13, x14
mul x6, x25, x22
stp x1, x2, [x0, #128]
stp x4, x17, [x0, #144]
umulh x9, x14, x14
mul x15, x14, x14
adds x8, x24, x23
adcs x5, x12, x21
adc x20, x16, x10
mul x1, x22, x22
umulh x2, x22, x22
mul x4, x13, x13
umulh x17, x13, x13
extr x14, x7, x6, #63
lsl x24, x6, #1
umulh x23, x25, x25
mul x21, x25, x25
adds x12, x5, x28
adcs x16, x20, x3
adc x22, x11, x10
extr x13, x8, x7, #63
lsr x6, x22, #63
extr x25, x12, x8, #63
extr x5, x16, x12, #63
extr x28, x22, x16, #63
adds x20, x24, x23
adcs x3, x14, x1
adcs x11, x13, x2
adcs x7, x25, x4
adcs x8, x5, x17
adcs x12, x28, x15
adc x16, x6, x9
ldp x22, x24, [x0, #448]
ldp x23, x14, [x0, #464]
ldp x1, x2, [x0, #496]
ldp x13, x25, [x0, #480]
adds x4, x22, x13
adcs x5, x24, x25
adcs x17, x23, x1
adcs x15, x14, x2
csel x28, x27, x10, hs
mul x9, x27, x8
umulh x6, x27, x8
mul x22, x27, x7
mul x13, x27, x16
umulh x24, x27, x16
mul x25, x27, x12
umulh x1, x27, x12
umulh x23, x27, x7
adds x2, x4, x28
adcs x14, x5, x10
adc x8, x17, x10
adds x16, x21, x22
adcs x12, x20, x9
adcs x7, x3, x25
adcs x4, x11, x13
adc x28, x24, x10
umulh x5, x2, x14
umulh x17, x2, x8
umulh x22, x2, x15
mul x21, x14, x8
mul x20, x2, x15
mul x9, x2, x8
mul x25, x14, x15
adds x3, x4, x1
adc x13, x28, x10
umulh x11, x14, x15
extr x24, x13, x3, #63
and x1, x3, #0x7fffffffffffffff
mul x4, x24, x26
adds x28, x9, x5
adcs x13, x20, x17
adc x3, x22, x10
umulh x24, x8, x15
umulh x9, x14, x8
adds x5, x16, x4
adcs x20, x12, x23
adcs x17, x7, x6
adc x22, x1, x10
mul x16, x8, x15
adds x4, x13, x21
adcs x23, x3, x25
adc x12, x11, x10
mul x6, x2, x14
stp x5, x20, [x0, #192]
stp x17, x22, [x0, #208]
umulh x7, x15, x15
adds x1, x23, x9
adcs x21, x12, x16
adc x13, x24, x10
umulh x3, x14, x14
umulh x25, x8, x8
extr x11, x4, x28, #63
extr x5, x28, x6, #63
mul x20, x15, x15
lsl x17, x6, #1
mul x22, x8, x8
mul x23, x14, x14
umulh x9, x2, x2
extr x12, x1, x4, #63
extr x16, x21, x1, #63
extr x24, x13, x21, #63
lsr x28, x13, #63
mul x15, x2, x2
adds x6, x17, x9
adcs x8, x5, x23
adcs x14, x11, x3
adcs x4, x12, x22
adcs x1, x16, x25
adcs x21, x24, x20
adc x13, x28, x7
ldp x2, x17, [x0, #192]
ldp x9, x23, [x0, #208]
ldr x5, [x0, #64]
mul x3, x5, x17
mul x11, x5, x23
mul x12, x5, x9
mul x22, x27, x4
umulh x16, x5, x2
umulh x25, x27, x13
mul x24, x27, x13
umulh x20, x27, x4
mul x7, x27, x1
umulh x28, x27, x1
mul x13, x27, x21
umulh x4, x27, x21
adds x1, x15, x22
adcs x21, x6, x7
adcs x22, x8, x13
adcs x15, x14, x24
adc x6, x25, x10
umulh x7, x5, x9
umulh x13, x5, x17
adds x8, x15, x4
adc x14, x6, x10
umulh x24, x5, x23
mul x25, x5, x2
extr x15, x14, x8, #63
and x4, x8, #0x7fffffffffffffff
mul x6, x15, x26
adds x5, x3, x16
adcs x14, x12, x13
adcs x8, x11, x7
adc x15, x24, x10
ldr x3, [x0, #72]
adds x16, x1, x6
adcs x12, x21, x20
adcs x13, x22, x28
adc x11, x4, x10
mul x7, x3, x2
mul x24, x3, x17
mul x1, x3, x9
mul x6, x3, x23
umulh x20, x3, x2
stp x16, x12, [x0, #160]
umulh x21, x3, x23
umulh x28, x3, x17
umulh x22, x3, x9
stp x13, x11, [x0, #176]
ldr x4, [x0, #80]
adds x12, x5, x7
adcs x16, x14, x24
adcs x3, x8, x1
adcs x13, x15, x6
adc x11, x10, x10
ldr x5, [x0, #88]
mul x7, x4, x2
mul x14, x4, x23
mul x24, x4, x9
adds x8, x16, x20
adcs x1, x3, x28
adcs x6, x13, x22
adc x15, x11, x21
mul x16, x4, x17
umulh x20, x4, x17
umulh x3, x4, x23
umulh x28, x4, x9
umulh x22, x4, x2
adds x13, x8, x7
adcs x21, x1, x16
adcs x11, x6, x24
adcs x4, x15, x14
adc x8, x10, x10
mul x7, x5, x9
umulh x16, x5, x9
mul x1, x5, x23
umulh x24, x5, x23
mul x6, x5, x17
umulh x14, x5, x17
adds x15, x21, x22
adcs x9, x11, x20
adcs x23, x4, x28
adc x17, x8, x3
mul x22, x5, x2
umulh x21, x5, x2
adds x20, x15, x22
adcs x11, x9, x6
adcs x28, x23, x7
adcs x4, x17, x1
adc x3, x10, x10
adds x8, x11, x21
adcs x5, x28, x14
adcs x2, x4, x16
adc x22, x3, x24
umulh x15, x27, x22
mul x6, x27, x5
mul x9, x27, x8
mul x7, x27, x2
mul x23, x27, x22
umulh x1, x27, x2
umulh x17, x27, x8
umulh x21, x27, x5
adds x11, x25, x9
adcs x14, x12, x6
adcs x28, x13, x7
adcs x4, x20, x23
adc x16, x15, x10
adds x3, x4, x1
adc x24, x16, x10
extr x22, x24, x3, #63
and x2, x3, #0x7fffffffffffffff
mul x8, x22, x26
adds x5, x11, x8
adcs x25, x14, x17
adcs x9, x28, x21
adc x12, x2, x10
stp x5, x25, [x0, #192]
stp x9, x12, [x0, #208]
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
.globl lab_sc_o3_19_15_0
lab_sc_o3_19_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
umulh x17, x9, x7
umulh x1, x9, x16
umulh x12, x9, x21
mul x14, x9, x16
mul x20, x9, x21
umulh x13, x7, x21
mul x4, x7, x16
mul x22, x7, x21
umulh x6, x7, x16
umulh x2, x16, x21
mul x11, x16, x21
mul x15, x9, x7
adds x8, x14, x17
adcs x28, x20, x1
adc x23, x12, x10
umulh x25, x9, x9
mul x24, x9, x9
mul x3, x7, x7
lsl x5, x15, #1
adds x17, x28, x4
adcs x14, x23, x22
adc x20, x13, x10
umulh x1, x7, x7
extr x12, x8, x15, #63
umulh x9, x16, x16
mul x28, x16, x16
adds x4, x14, x6
adcs x23, x20, x11
adc x22, x2, x10
extr x13, x17, x8, #63
umulh x7, x21, x21
mul x15, x21, x21
lsr x16, x22, #63
extr x6, x22, x23, #63
extr x14, x23, x4, #63
extr x11, x4, x17, #63
adds x20, x5, x25
adcs x2, x12, x3
adcs x8, x13, x1
adcs x21, x11, x28
adcs x22, x14, x9
adcs x23, x6, x15
adc x4, x16, x7
umulh x17, x27, x4
mul x5, x27, x21
mul x25, x27, x22
mul x12, x27, x23
mul x3, x27, x4
umulh x1, x27, x23
umulh x13, x27, x21
umulh x28, x27, x22
adds x11, x24, x5
adcs x14, x20, x25
adcs x9, x2, x12
adcs x15, x8, x3
adc x6, x17, x10
ldp x7, x16, [x0, #256]
ldp x4, x23, [x0, #272]
adds x21, x15, x1
adc x22, x6, x10
umulh x5, x7, x16
umulh x24, x7, x4
mul x20, x7, x4
mul x25, x7, x23
mul x12, x7, x16
extr x2, x22, x21, #63
umulh x3, x7, x23
and x8, x21, #0x7fffffffffffffff
mul x17, x16, x4
mul x15, x2, x26
mul x1, x16, x23
adds x6, x11, x15
adcs x22, x14, x13
adcs x21, x9, x28
adc x2, x8, x10
umulh x11, x16, x23
umulh x15, x16, x4
umulh x14, x4, x23
stp x6, x22, [x0, #352]
adds x13, x20, x5
adcs x9, x25, x24
adc x28, x3, x10
mul x8, x4, x23
stp x21, x2, [x0, #368]
umulh x6, x7, x7
mul x22, x7, x7
mul x20, x16, x16
lsl x5, x12, #1
adds x25, x9, x17
adcs x24, x28, x1
adc x3, x11, x10
umulh x21, x16, x16
extr x2, x13, x12, #63
umulh x7, x4, x4
mul x9, x4, x4
adds x17, x24, x15
adcs x28, x3, x8
adc x1, x14, x10
extr x11, x25, x13, #63
umulh x16, x23, x23
mul x12, x23, x23
lsr x4, x1, #63
extr x24, x1, x28, #63
extr x15, x28, x17, #63
extr x3, x17, x25, #63
adds x8, x5, x6
adcs x14, x2, x20
adcs x13, x11, x21
adcs x23, x3, x9
adcs x1, x15, x7
adcs x28, x24, x12
adc x25, x4, x16
umulh x17, x27, x25
mul x6, x27, x23
mul x5, x27, x1
mul x20, x27, x28
mul x2, x27, x25
umulh x21, x27, x28
umulh x11, x27, x23
umulh x3, x27, x1
adds x9, x22, x6
adcs x15, x8, x5
adcs x7, x14, x20
adcs x24, x13, x2
adc x12, x17, x10
ldp x4, x16, [x0, #224]
ldp x25, x28, [x0, #240]
ldr x23, [x0, #320]
adds x1, x24, x21
adc x6, x12, x10
mul x22, x23, x16
mul x5, x23, x25
mul x8, x23, x28
mul x14, x23, x4
extr x20, x6, x1, #63
umulh x13, x23, x4
and x2, x1, #0x7fffffffffffffff
umulh x17, x23, x16
mul x24, x20, x26
umulh x21, x23, x25
adds x12, x9, x24
adcs x6, x15, x11
adcs x1, x7, x3
adc x20, x2, x10
umulh x9, x23, x28
adds x24, x22, x13
adcs x11, x5, x17
adcs x15, x8, x21
adc x7, x9, x10
stp x12, x6, [x0, #384]
stp x1, x20, [x0, #400]
ldr x3, [x0, #328]
mul x2, x3, x4
mul x23, x3, x16
mul x22, x3, x25
mul x13, x3, x28
umulh x5, x3, x4
umulh x17, x3, x16
umulh x8, x3, x25
umulh x21, x3, x28
ldr x9, [x0, #336]
adds x12, x24, x2
adcs x6, x11, x23
adcs x1, x15, x22
adcs x20, x7, x13
adc x3, x10, x10
mul x24, x9, x4
mul x2, x9, x16
mul x11, x9, x25
mul x23, x9, x28
adds x22, x6, x5
adcs x15, x1, x17
adcs x13, x20, x8
adc x7, x3, x21
umulh x6, x9, x4
umulh x5, x9, x16
umulh x17, x9, x25
umulh x1, x9, x28
ldr x8, [x0, #344]
adds x20, x22, x24
adcs x21, x15, x2
adcs x3, x13, x11
adcs x9, x7, x23
adc x24, x10, x10
mul x22, x8, x4
umulh x2, x8, x4
mul x15, x8, x16
umulh x11, x8, x16
mul x13, x8, x25
adds x23, x21, x6
adcs x7, x3, x5
adcs x4, x9, x17
adc x16, x24, x1
umulh x6, x8, x25
mul x21, x8, x28
umulh x5, x8, x28
adds x3, x23, x22
adcs x17, x7, x15
adcs x9, x4, x13
adcs x24, x16, x21
adc x1, x10, x10
adds x25, x17, x2
adcs x8, x9, x11
adcs x28, x24, x6
adc x22, x1, x5
umulh x23, x27, x22
mul x15, x27, x25
mul x7, x27, x8
mul x13, x27, x28
mul x4, x27, x22
umulh x16, x27, x28
umulh x21, x27, x25
umulh x2, x27, x8
adds x17, x14, x15
adcs x9, x12, x7
adcs x11, x20, x13
adcs x24, x3, x4
adc x6, x23, x10
ldp x1, x5, [x0, #256]
ldp x22, x28, [x0, #272]
ldr x25, [x0, #288]
adds x8, x24, x16
adc x14, x6, x10
mul x15, x25, x5
mul x12, x25, x22
mul x7, x25, x28
mul x20, x25, x1
extr x13, x14, x8, #63
umulh x3, x25, x1
and x4, x8, #0x7fffffffffffffff
umulh x23, x25, x5
mul x16, x13, x26
umulh x24, x25, x22
adds x6, x17, x16
adcs x14, x9, x21
adcs x8, x11, x2
adc x13, x4, x10
umulh x17, x25, x28
adds x16, x15, x3
adcs x9, x12, x23
adcs x21, x7, x24
adc x2, x17, x10
stp x6, x14, [x0, #448]
stp x8, x13, [x0, #464]
ldr x11, [x0, #296]
mul x4, x11, x1
mul x25, x11, x5
mul x3, x11, x22
mul x15, x11, x28
umulh x12, x11, x1
umulh x23, x11, x5
umulh x7, x11, x22
umulh x24, x11, x28
ldr x17, [x0, #304]
adds x6, x16, x4
adcs x14, x9, x25
adcs x13, x21, x3
adcs x8, x2, x15
adc x11, x10, x10
mul x4, x17, x1
mul x16, x17, x5
mul x25, x17, x22
mul x9, x17, x28
adds x21, x14, x12
adcs x3, x13, x23
adcs x2, x8, x7
adc x15, x11, x24
umulh x14, x17, x1
umulh x12, x17, x5
umulh x13, x17, x22
umulh x23, x17, x28
ldr x8, [x0, #312]
adds x7, x21, x4
adcs x11, x3, x16
adcs x24, x2, x25
adcs x17, x15, x9
adc x21, x10, x10
mul x4, x8, x1
umulh x3, x8, x1
mul x16, x8, x5
umulh x2, x8, x5
mul x25, x8, x22
adds x9, x11, x14
adcs x15, x24, x12
adcs x1, x17, x13
adc x5, x21, x23
umulh x11, x8, x22
mul x14, x8, x28
umulh x24, x8, x28
adds x12, x9, x4
adcs x13, x15, x16
adcs x17, x1, x25
adcs x23, x5, x14
adc x21, x10, x10
adds x22, x13, x3
adcs x28, x17, x2
adcs x8, x23, x11
adc x9, x21, x24
umulh x4, x27, x9
mul x16, x27, x22
mul x15, x27, x28
mul x25, x27, x8
mul x1, x27, x9
umulh x14, x27, x8
umulh x5, x27, x22
umulh x3, x27, x28
adds x13, x20, x16
adcs x2, x6, x15
adcs x17, x7, x25
adcs x11, x12, x1
adc x23, x4, x10
ldp x24, x21, [x0, #352]
ldp x9, x8, [x0, #368]
ldp x22, x28, [x0, #384]
ldp x16, x20, [x0, #400]
adds x15, x11, x14
adc x6, x23, x10
subs x7, x24, x22
sbcs x25, x21, x28
sbcs x1, x9, x16
sbcs x12, x8, x20
csel x4, x10, x27, hs
extr x11, x6, x15, #63
and x14, x15, #0x7fffffffffffffff
mul x23, x11, x26
adds x22, x13, x23
adcs x24, x2, x5
adcs x28, x17, x3
adc x21, x14, x10
subs x9, x7, x4
sbcs x16, x25, x10
sbcs x8, x1, x10
sbc x20, x12, x10
stp x22, x24, [x0, #480]
stp x28, x21, [x0, #496]
ldp x6, x15, [x0, #384]
ldp x11, x13, [x0, #400]
stp x8, x20, [x0, #432]
stp x9, x16, [x0, #416]
ldr x23, [x0, #352]
ldr x2, [x0, #360]
umulh x5, x23, x6
umulh x17, x23, x15
umulh x3, x23, x11
umulh x14, x23, x13
mul x4, x23, x15
mul x7, x23, x11
mul x25, x23, x13
mul x1, x2, x6
mul x12, x2, x15
mul x22, x2, x11
mul x24, x23, x6
mul x28, x2, x13
umulh x21, x2, x6
umulh x8, x2, x15
adds x20, x4, x5
adcs x9, x7, x17
adcs x16, x25, x3
adc x23, x14, x10
umulh x5, x2, x11
umulh x4, x2, x13
ldr x17, [x0, #368]
adds x7, x20, x1
adcs x3, x9, x12
adcs x25, x16, x22
adcs x14, x23, x28
adc x2, x10, x10
mul x1, x17, x6
mul x20, x17, x15
mul x12, x17, x11
mul x9, x17, x13
adds x22, x3, x21
adcs x16, x25, x8
adcs x28, x14, x5
adc x23, x2, x4
umulh x21, x17, x6
umulh x3, x17, x15
umulh x8, x17, x11
umulh x25, x17, x13
ldr x14, [x0, #376]
adds x5, x22, x1
adcs x2, x16, x20
adcs x4, x28, x12
adcs x17, x23, x9
adc x1, x10, x10
mul x22, x14, x6
umulh x20, x14, x6
mul x16, x14, x15
umulh x28, x14, x15
mul x12, x14, x11
adds x23, x2, x21
adcs x9, x4, x3
adcs x6, x17, x8
adc x15, x1, x25
umulh x2, x14, x11
mul x21, x14, x13
umulh x4, x14, x13
adds x3, x23, x22
adcs x17, x9, x16
adcs x8, x6, x12
adcs x1, x15, x21
adc x25, x10, x10
adds x11, x17, x20
adcs x13, x8, x28
adcs x14, x1, x2
adc x23, x25, x4
umulh x22, x27, x23
mul x9, x27, x11
mul x16, x27, x13
mul x6, x27, x14
mul x12, x27, x23
umulh x21, x27, x14
umulh x15, x27, x11
umulh x17, x27, x13
adds x20, x24, x9
adcs x8, x7, x16
adcs x28, x5, x6
adcs x2, x3, x12
adc x1, x22, x10
ldp x4, x25, [x0, #432]
ldp x23, x14, [x0, #416]
movz x11, #56129, lsl #0
ldp x13, x24, [x0, #352]
ldp x9, x7, [x0, #368]
adds x16, x2, x21
adc x6, x1, x10
movk x11, #1, lsl #16
mul x5, x23, x11
extr x3, x6, x16, #63
mul x12, x14, x11
and x22, x16, #0x7fffffffffffffff
mul x2, x4, x11
mul x21, x3, x26
adds x1, x20, x21
adcs x6, x8, x15
adcs x16, x28, x17
adc x3, x22, x10
umulh x20, x25, x11
mul x21, x25, x11
adds x15, x13, x5
adcs x8, x24, x12
adcs x28, x9, x2
adcs x17, x7, x21
adc x22, x20, x10
stp x1, x6, [x0, #96]
stp x16, x3, [x0, #112]
umulh x25, x23, x11
umulh x13, x14, x11
umulh x5, x4, x11
ldr x24, [x0, #416]
adds x12, x17, x17
adc x2, x22, x22
mul x9, x2, x26
lsr x21, x12, #1
adds x7, x15, x9
adcs x20, x8, x25
adcs x1, x28, x13
adc x6, x21, x5
stp x7, x20, [x0, #128]
stp x1, x6, [x0, #144]
ldr x16, [x0, #424]
ldp x3, x23, [x0, #128]
ldp x14, x4, [x0, #144]
umulh x11, x24, x3
umulh x17, x24, x23
umulh x22, x24, x14
umulh x2, x24, x4
mul x12, x24, x23
mul x15, x24, x14
mul x9, x24, x4
mul x25, x16, x3
mul x8, x16, x23
mul x13, x16, x14
mul x28, x24, x3
mul x5, x16, x4
umulh x21, x16, x3
umulh x20, x16, x23
adds x7, x12, x11
adcs x1, x15, x17
adcs x6, x9, x22
adc x24, x2, x10
umulh x12, x16, x14
umulh x11, x16, x4
ldr x15, [x0, #432]
adds x17, x7, x25
adcs x9, x1, x8
adcs x22, x6, x13
adcs x2, x24, x5
adc x16, x10, x10
mul x7, x15, x3
mul x25, x15, x23
mul x1, x15, x14
mul x8, x15, x4
adds x6, x9, x21
adcs x13, x22, x20
adcs x5, x2, x12
adc x24, x16, x11
umulh x9, x15, x3
umulh x21, x15, x23
umulh x22, x15, x14
umulh x20, x15, x4
ldr x12, [x0, #440]
adds x2, x6, x7
adcs x11, x13, x25
adcs x16, x5, x1
adcs x15, x24, x8
adc x6, x10, x10
mul x7, x12, x3
umulh x25, x12, x3
mul x13, x12, x23
umulh x1, x12, x23
mul x5, x12, x14
adds x8, x11, x9
adcs x24, x16, x21
adcs x3, x15, x22
adc x23, x6, x20
umulh x9, x12, x14
mul x11, x12, x4
umulh x21, x12, x4
adds x16, x8, x7
adcs x22, x24, x13
adcs x15, x3, x5
adcs x20, x23, x11
adc x6, x10, x10
adds x14, x22, x25
adcs x12, x15, x1
adcs x4, x20, x9
adc x7, x6, x21
umulh x8, x27, x7
mul x13, x27, x14
mul x24, x27, x12
mul x5, x27, x4
mul x3, x27, x7
umulh x11, x27, x4
umulh x23, x27, x14
umulh x25, x27, x12
adds x22, x28, x13
adcs x1, x17, x24
adcs x15, x2, x5
adcs x20, x16, x3
adc x9, x8, x10
ldp x6, x21, [x0, #448]
ldp x7, x4, [x0, #464]
ldp x14, x12, [x0, #480]
ldp x28, x13, [x0, #496]
adds x17, x20, x11
adc x24, x9, x10
subs x2, x6, x14
sbcs x5, x21, x12
sbcs x3, x7, x28
sbcs x16, x4, x13
csel x8, x10, x27, hs
extr x11, x24, x17, #63
and x20, x17, #0x7fffffffffffffff
mul x9, x11, x26
adds x6, x22, x9
adcs x14, x1, x23
adcs x21, x15, x25
adc x12, x20, x10
subs x7, x2, x8
sbcs x28, x5, x10
sbcs x4, x3, x10
sbc x13, x16, x10
stp x6, x14, [x0, #128]
stp x21, x12, [x0, #144]
umulh x24, x7, x28
umulh x17, x7, x4
umulh x11, x7, x13
mul x22, x7, x4
mul x9, x7, x13
umulh x1, x28, x13
mul x23, x28, x4
mul x15, x28, x13
umulh x25, x28, x4
umulh x20, x4, x13
mul x2, x4, x13
mul x8, x7, x28
adds x5, x22, x24
adcs x3, x9, x17
adc x16, x11, x10
umulh x6, x7, x7
mul x14, x7, x7
mul x21, x28, x28
lsl x12, x8, #1
adds x22, x3, x23
adcs x24, x16, x15
adc x9, x1, x10
umulh x17, x28, x28
extr x11, x5, x8, #63
umulh x7, x4, x4
mul x3, x4, x4
adds x23, x24, x25
adcs x15, x9, x2
adc x16, x20, x10
extr x1, x22, x5, #63
umulh x28, x13, x13
mul x8, x13, x13
lsr x4, x16, #63
extr x24, x16, x15, #63
extr x25, x15, x23, #63
extr x9, x23, x22, #63
adds x2, x12, x6
adcs x20, x11, x21
adcs x5, x1, x17
adcs x13, x9, x3
adcs x16, x25, x7
adcs x15, x24, x8
adc x22, x4, x28
umulh x23, x27, x22
mul x12, x27, x13
mul x6, x27, x16
mul x11, x27, x15
mul x21, x27, x22
umulh x17, x27, x15
umulh x1, x27, x13
umulh x9, x27, x16
adds x3, x14, x12
adcs x25, x2, x6
adcs x7, x20, x11
adcs x8, x5, x21
adc x24, x23, x10
ldp x28, x4, [x0, #448]
ldp x22, x15, [x0, #464]
ldp x13, x16, [x0, #480]
ldp x12, x14, [x0, #496]
adds x2, x8, x17
adc x6, x24, x10
adds x11, x28, x13
adcs x20, x4, x16
adcs x21, x22, x12
adcs x5, x15, x14
csel x23, x27, x10, hs
extr x17, x6, x2, #63
and x8, x2, #0x7fffffffffffffff
mul x24, x17, x26
adds x28, x3, x24
adcs x13, x25, x1
adcs x4, x7, x9
adc x16, x8, x10
adds x12, x11, x23
adcs x22, x20, x10
adc x14, x21, x10
stp x28, x13, [x0, #192]
stp x4, x16, [x0, #208]
umulh x15, x12, x22
umulh x6, x12, x14
umulh x2, x12, x5
mul x17, x12, x14
mul x3, x12, x5
umulh x24, x22, x5
mul x1, x22, x14
mul x25, x22, x5
umulh x9, x22, x14
umulh x7, x14, x5
mul x8, x14, x5
mul x11, x12, x22
adds x23, x17, x15
adcs x20, x3, x6
adc x21, x2, x10
umulh x28, x12, x12
mul x13, x12, x12
mul x4, x22, x22
lsl x16, x11, #1
adds x17, x20, x1
adcs x15, x21, x25
adc x3, x24, x10
umulh x6, x22, x22
extr x2, x23, x11, #63
umulh x12, x14, x14
mul x1, x14, x14
adds x20, x15, x9
adcs x21, x3, x8
adc x25, x7, x10
extr x24, x17, x23, #63
umulh x22, x5, x5
mul x11, x5, x5
lsr x14, x25, #63
extr x15, x25, x21, #63
extr x9, x21, x20, #63
extr x3, x20, x17, #63
adds x8, x16, x28
adcs x7, x2, x4
adcs x23, x24, x6
adcs x5, x3, x1
adcs x25, x9, x12
adcs x21, x15, x11
adc x17, x14, x22
umulh x20, x27, x17
mul x16, x27, x5
mul x28, x27, x25
mul x4, x27, x21
mul x2, x27, x17
umulh x6, x27, x21
umulh x24, x27, x5
umulh x3, x27, x25
adds x1, x13, x16
adcs x9, x8, x28
adcs x12, x7, x4
adcs x15, x23, x2
adc x11, x20, x10
ldp x22, x14, [x0, #192]
ldp x17, x21, [x0, #208]
ldr x5, [x0, #64]
adds x25, x15, x6
adc x16, x11, x10
mul x13, x5, x14
mul x8, x5, x17
mul x28, x5, x21
mul x4, x5, x22
extr x7, x16, x25, #63
umulh x23, x5, x22
and x2, x25, #0x7fffffffffffffff
umulh x20, x5, x14
mul x15, x7, x26
umulh x6, x5, x17
adds x11, x1, x15
adcs x16, x9, x24
adcs x25, x12, x3
adc x7, x2, x10
umulh x1, x5, x21
adds x15, x13, x23
adcs x24, x8, x20
adcs x9, x28, x6
adc x3, x1, x10
stp x11, x16, [x0, #160]
stp x25, x7, [x0, #176]
ldr x12, [x0, #72]
mul x2, x12, x22
mul x5, x12, x14
mul x13, x12, x17
mul x23, x12, x21
umulh x8, x12, x22
umulh x20, x12, x14
umulh x28, x12, x17
umulh x6, x12, x21
ldr x1, [x0, #80]
adds x16, x15, x2
adcs x11, x24, x5
adcs x25, x9, x13
adcs x7, x3, x23
adc x12, x10, x10
mul x15, x1, x22
mul x2, x1, x14
mul x24, x1, x17
mul x5, x1, x21
adds x9, x11, x8
adcs x13, x25, x20
adcs x23, x7, x28
adc x3, x12, x6
umulh x11, x1, x22
umulh x8, x1, x14
umulh x25, x1, x17
umulh x20, x1, x21
ldr x28, [x0, #88]
adds x7, x9, x15
adcs x6, x13, x2
adcs x12, x23, x24
adcs x1, x3, x5
adc x9, x10, x10
mul x15, x28, x22
umulh x2, x28, x22
mul x13, x28, x14
umulh x24, x28, x14
mul x23, x28, x17
adds x5, x6, x11
adcs x3, x12, x8
adcs x22, x1, x25
adc x14, x9, x20
umulh x11, x28, x17
mul x6, x28, x21
umulh x8, x28, x21
adds x12, x5, x15
adcs x25, x3, x13
adcs x1, x22, x23
adcs x20, x14, x6
adc x9, x10, x10
adds x17, x25, x2
adcs x28, x1, x24
adcs x21, x20, x11
adc x15, x9, x8
umulh x5, x27, x15
mul x13, x27, x17
mul x3, x27, x28
mul x23, x27, x21
mul x22, x27, x15
umulh x6, x27, x21
umulh x14, x27, x17
umulh x2, x27, x28
adds x25, x4, x13
adcs x24, x16, x3
adcs x1, x7, x23
adcs x20, x12, x22
adc x11, x5, x10
adds x9, x20, x6
adc x8, x11, x10
extr x15, x8, x9, #63
and x21, x9, #0x7fffffffffffffff
mul x17, x15, x26
adds x28, x25, x17
adcs x4, x24, x14
adcs x13, x1, x2
adc x16, x21, x10
stp x28, x4, [x0, #192]
stp x13, x16, [x0, #208]
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
.globl lab_sc_o3_19_15_1
lab_sc_o3_19_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
umulh x3, x6, x16
umulh x7, x6, x23
umulh x11, x6, x15
mul x4, x6, x15
mul x8, x6, x23
umulh x2, x16, x15
mul x13, x23, x15
umulh x17, x16, x23
mul x5, x16, x15
umulh x1, x23, x15
mul x9, x16, x23
mul x12, x6, x16
adds x21, x8, x3
adcs x20, x4, x7
adc x22, x11, x10
umulh x28, x6, x6
mul x24, x6, x6
mul x25, x16, x16
lsl x14, x12, #1
adds x3, x20, x9
adcs x8, x22, x5
adc x4, x2, x10
umulh x7, x16, x16
extr x11, x21, x12, #63
umulh x6, x23, x23
mul x20, x23, x23
adds x9, x8, x17
adcs x22, x4, x13
adc x5, x1, x10
extr x2, x3, x21, #63
umulh x16, x15, x15
mul x12, x15, x15
lsr x23, x5, #63
extr x17, x5, x22, #63
extr x8, x22, x9, #63
extr x13, x9, x3, #63
adds x4, x14, x28
adcs x1, x11, x25
adcs x21, x2, x7
adcs x15, x13, x20
adcs x5, x8, x6
adcs x22, x17, x12
adc x9, x23, x16
umulh x3, x27, x9
mul x14, x27, x15
mul x28, x27, x5
mul x11, x27, x9
mul x25, x27, x22
umulh x7, x27, x22
umulh x2, x27, x5
umulh x20, x27, x15
adds x13, x24, x14
adcs x8, x4, x28
adcs x6, x1, x25
adcs x12, x21, x11
adc x17, x3, x10
ldp x16, x23, [x0, #272]
ldp x9, x22, [x0, #256]
adds x5, x12, x7
adc x15, x17, x10
umulh x14, x9, x16
mul x24, x9, x16
mul x4, x9, x23
umulh x28, x9, x22
mul x25, x9, x22
extr x1, x15, x5, #63
umulh x11, x9, x23
and x21, x5, #0x7fffffffffffffff
mul x3, x22, x16
mul x12, x1, x26
mul x7, x22, x23
adds x17, x13, x12
adcs x15, x8, x20
adcs x5, x6, x2
adc x1, x21, x10
umulh x13, x22, x23
umulh x12, x22, x16
umulh x8, x16, x23
stp x17, x15, [x0, #352]
adds x20, x24, x28
adcs x6, x4, x14
adc x2, x11, x10
mul x21, x16, x23
stp x5, x1, [x0, #368]
umulh x17, x9, x9
mul x15, x22, x22
mul x24, x9, x9
lsl x28, x25, #1
adds x4, x6, x3
adcs x14, x2, x7
adc x11, x13, x10
umulh x5, x22, x22
extr x1, x20, x25, #63
mul x9, x16, x16
umulh x6, x16, x16
adds x3, x14, x12
adcs x2, x11, x21
adc x7, x8, x10
extr x13, x4, x20, #63
umulh x22, x23, x23
mul x25, x23, x23
lsr x16, x7, #63
extr x14, x7, x2, #63
extr x12, x2, x3, #63
extr x11, x3, x4, #63
adds x21, x28, x17
adcs x8, x1, x15
adcs x20, x13, x5
adcs x23, x11, x9
adcs x7, x12, x6
adcs x2, x14, x25
adc x4, x16, x22
umulh x3, x27, x4
mul x17, x27, x23
mul x28, x27, x4
mul x15, x27, x7
mul x1, x27, x2
umulh x5, x27, x2
umulh x13, x27, x7
umulh x11, x27, x23
adds x9, x24, x17
adcs x12, x21, x15
adcs x6, x8, x1
adcs x14, x20, x28
adc x25, x3, x10
ldp x16, x22, [x0, #240]
ldr x4, [x0, #320]
ldp x2, x7, [x0, #224]
adds x23, x14, x5
adc x17, x25, x10
mul x24, x4, x16
mul x15, x4, x7
mul x21, x4, x22
mul x8, x4, x2
extr x1, x17, x23, #63
umulh x20, x4, x2
and x28, x23, #0x7fffffffffffffff
umulh x3, x4, x7
mul x14, x1, x26
umulh x5, x4, x16
adds x25, x9, x14
adcs x17, x12, x11
adcs x23, x6, x13
adc x1, x28, x10
umulh x9, x4, x22
adds x14, x15, x20
adcs x11, x24, x3
adcs x12, x21, x5
adc x6, x9, x10
stp x25, x17, [x0, #384]
stp x23, x1, [x0, #400]
ldr x13, [x0, #328]
mul x28, x13, x2
mul x4, x13, x22
mul x15, x13, x7
mul x20, x13, x16
umulh x24, x13, x22
ldr x3, [x0, #336]
umulh x21, x13, x16
umulh x5, x13, x2
umulh x9, x13, x7
adds x25, x14, x28
adcs x17, x11, x15
adcs x23, x12, x20
adcs x1, x6, x4
adc x13, x10, x10
mul x14, x3, x2
mul x28, x3, x22
mul x11, x3, x7
mul x15, x3, x16
adds x20, x17, x5
adcs x12, x23, x9
adcs x4, x1, x21
adc x6, x13, x24
umulh x17, x3, x16
umulh x5, x3, x2
umulh x9, x3, x22
umulh x23, x3, x7
ldr x21, [x0, #344]
adds x1, x20, x14
adcs x24, x12, x11
adcs x13, x4, x15
adcs x3, x6, x28
adc x14, x10, x10
mul x20, x21, x2
umulh x11, x21, x2
mul x12, x21, x22
umulh x15, x21, x7
mul x4, x21, x7
adds x28, x24, x5
adcs x6, x13, x23
adcs x2, x3, x17
adc x7, x14, x9
umulh x5, x21, x22
mul x24, x21, x16
umulh x23, x21, x16
adds x13, x28, x20
adcs x17, x6, x4
adcs x3, x2, x24
adcs x14, x7, x12
adc x9, x10, x10
adds x22, x17, x11
adcs x21, x3, x15
adcs x16, x14, x23
adc x20, x9, x5
umulh x28, x27, x20
mul x4, x27, x20
umulh x6, x27, x16
mul x24, x27, x22
mul x2, x27, x21
mul x7, x27, x16
umulh x12, x27, x21
umulh x11, x27, x22
adds x17, x8, x24
adcs x3, x25, x2
adcs x15, x1, x7
adcs x14, x13, x4
adc x23, x28, x10
ldp x9, x5, [x0, #256]
ldp x20, x16, [x0, #272]
ldr x21, [x0, #288]
adds x22, x14, x6
adc x8, x23, x10
mul x24, x21, x5
mul x25, x21, x16
mul x2, x21, x20
mul x1, x21, x9
extr x7, x8, x22, #63
umulh x13, x21, x9
and x4, x22, #0x7fffffffffffffff
umulh x28, x21, x5
mul x6, x7, x26
umulh x14, x21, x20
adds x23, x17, x6
adcs x8, x3, x11
adcs x22, x15, x12
adc x7, x4, x10
umulh x17, x21, x16
adds x6, x24, x13
adcs x3, x2, x28
adcs x11, x25, x14
adc x12, x17, x10
stp x23, x8, [x0, #448]
stp x22, x7, [x0, #464]
ldr x15, [x0, #296]
mul x4, x15, x9
mul x21, x15, x5
umulh x13, x15, x5
umulh x24, x15, x16
mul x2, x15, x20
umulh x28, x15, x9
mul x25, x15, x16
umulh x14, x15, x20
ldr x17, [x0, #304]
adds x23, x6, x4
adcs x8, x3, x21
adcs x7, x11, x2
adcs x22, x12, x25
adc x15, x10, x10
mul x4, x17, x9
mul x6, x17, x20
umulh x21, x17, x9
mul x3, x17, x5
adds x11, x8, x28
adcs x2, x7, x13
adcs x12, x22, x14
adc x25, x15, x24
umulh x8, x17, x20
mul x28, x17, x16
umulh x7, x17, x16
umulh x13, x17, x5
ldr x22, [x0, #312]
adds x14, x11, x4
adcs x15, x2, x3
adcs x24, x12, x6
adcs x17, x25, x28
adc x11, x10, x10
mul x4, x22, x9
umulh x2, x22, x9
mul x3, x22, x20
mul x12, x22, x16
adds x6, x15, x21
adcs x28, x24, x13
adcs x25, x17, x8
adc x9, x11, x7
umulh x15, x22, x20
umulh x21, x22, x16
mul x24, x22, x5
umulh x13, x22, x5
adds x8, x6, x4
adcs x17, x28, x24
adcs x7, x25, x3
adcs x11, x9, x12
adc x20, x10, x10
adds x16, x17, x2
adcs x5, x7, x13
adcs x22, x11, x15
adc x6, x20, x21
umulh x4, x27, x6
mul x24, x27, x5
mul x28, x27, x6
mul x3, x27, x22
umulh x25, x27, x22
mul x12, x27, x16
umulh x9, x27, x5
umulh x2, x27, x16
adds x17, x1, x12
adcs x13, x23, x24
adcs x7, x14, x3
adcs x15, x8, x28
adc x11, x4, x10
ldp x21, x20, [x0, #384]
ldp x6, x22, [x0, #368]
ldp x5, x16, [x0, #352]
ldp x12, x1, [x0, #400]
adds x24, x15, x25
adc x23, x11, x10
subs x14, x5, x21
sbcs x3, x16, x20
sbcs x28, x6, x12
sbcs x8, x22, x1
csel x4, x10, x27, hs
extr x15, x23, x24, #63
and x25, x24, #0x7fffffffffffffff
mul x11, x15, x26
adds x21, x17, x11
adcs x5, x13, x2
adcs x20, x7, x9
adc x16, x25, x10
subs x6, x14, x4
sbcs x12, x3, x10
sbcs x22, x28, x10
sbc x1, x8, x10
stp x21, x5, [x0, #480]
stp x20, x16, [x0, #496]
ldr x23, [x0, #352]
ldp x24, x15, [x0, #400]
stp x22, x1, [x0, #432]
stp x6, x12, [x0, #416]
ldr x17, [x0, #360]
ldp x11, x13, [x0, #384]
umulh x2, x23, x24
umulh x7, x23, x15
mul x9, x23, x15
mul x25, x23, x24
umulh x4, x23, x11
umulh x14, x23, x13
mul x3, x23, x13
mul x28, x17, x24
mul x8, x17, x11
mul x21, x17, x13
mul x5, x23, x11
mul x20, x17, x15
umulh x16, x17, x11
umulh x22, x17, x13
adds x1, x3, x4
adcs x6, x25, x14
adcs x12, x9, x2
adc x23, x7, x10
umulh x4, x17, x24
umulh x3, x17, x15
ldr x14, [x0, #368]
adds x25, x1, x8
adcs x2, x6, x21
adcs x9, x12, x28
adcs x7, x23, x20
adc x17, x10, x10
mul x8, x14, x11
mul x1, x14, x15
mul x21, x14, x24
mul x6, x14, x13
adds x28, x2, x16
adcs x12, x9, x22
adcs x20, x7, x4
adc x23, x17, x3
umulh x16, x14, x15
umulh x2, x14, x24
ldr x22, [x0, #376]
umulh x9, x14, x13
umulh x7, x14, x11
adds x4, x28, x8
adcs x17, x12, x6
adcs x3, x20, x21
adcs x14, x23, x1
adc x8, x10, x10
mul x28, x22, x11
umulh x6, x22, x11
mul x12, x22, x24
mul x20, x22, x15
adds x21, x17, x7
adcs x23, x3, x9
adcs x1, x14, x2
adc x11, x8, x16
umulh x17, x22, x24
umulh x7, x22, x15
mul x3, x22, x13
umulh x9, x22, x13
adds x14, x21, x28
adcs x2, x23, x3
adcs x8, x1, x12
adcs x16, x11, x20
adc x24, x10, x10
adds x15, x2, x6
adcs x13, x8, x9
adcs x22, x16, x17
adc x21, x24, x7
umulh x28, x27, x21
mul x23, x27, x13
mul x3, x27, x15
mul x1, x27, x22
umulh x12, x27, x22
mul x20, x27, x21
umulh x11, x27, x15
umulh x2, x27, x13
adds x6, x5, x3
adcs x8, x25, x23
adcs x9, x4, x1
adcs x17, x14, x20
adc x16, x28, x10
movz x7, #56129, lsl #0
ldp x24, x22, [x0, #368]
ldp x21, x15, [x0, #432]
ldp x13, x5, [x0, #416]
ldp x3, x25, [x0, #352]
adds x23, x17, x12
adc x1, x16, x10
movk x7, #1, lsl #16
mul x4, x13, x7
extr x14, x1, x23, #63
mul x20, x5, x7
and x28, x23, #0x7fffffffffffffff
mul x17, x21, x7
mul x12, x14, x26
adds x16, x6, x12
adcs x1, x8, x11
adcs x23, x9, x2
adc x14, x28, x10
umulh x6, x15, x7
mul x12, x15, x7
adds x11, x3, x4
adcs x8, x25, x20
adcs x9, x24, x17
adcs x2, x22, x12
adc x28, x6, x10
stp x23, x14, [x0, #112]
stp x16, x1, [x0, #96]
umulh x15, x5, x7
umulh x3, x21, x7
umulh x4, x13, x7
ldr x25, [x0, #416]
adds x20, x2, x2
adc x17, x28, x28
mul x24, x17, x26
lsr x12, x20, #1
adds x22, x11, x24
adcs x6, x8, x4
adcs x23, x9, x15
adc x14, x12, x3
stp x22, x6, [x0, #128]
stp x23, x14, [x0, #144]
ldr x16, [x0, #424]
ldp x1, x5, [x0, #128]
ldp x21, x13, [x0, #144]
umulh x7, x25, x1
umulh x2, x25, x21
umulh x28, x25, x13
umulh x17, x25, x5
mul x20, x25, x5
mul x11, x25, x13
mul x24, x25, x21
mul x4, x16, x5
mul x8, x16, x1
mul x15, x16, x21
mul x9, x25, x1
mul x3, x16, x13
umulh x12, x16, x1
umulh x6, x16, x5
adds x22, x20, x7
adcs x23, x24, x17
adcs x14, x11, x2
adc x25, x28, x10
umulh x20, x16, x21
umulh x7, x16, x13
ldr x24, [x0, #432]
adds x17, x22, x8
adcs x11, x23, x4
adcs x2, x14, x15
adcs x28, x25, x3
adc x16, x10, x10
mul x22, x24, x1
mul x8, x24, x5
mul x23, x24, x21
mul x4, x24, x13
adds x14, x11, x12
adcs x15, x2, x6
adcs x3, x28, x20
adc x25, x16, x7
umulh x11, x24, x5
umulh x12, x24, x13
umulh x2, x24, x21
umulh x6, x24, x1
ldr x20, [x0, #440]
adds x28, x14, x22
adcs x7, x15, x8
adcs x16, x3, x23
adcs x24, x25, x4
adc x14, x10, x10
mul x22, x20, x1
umulh x8, x20, x1
mul x15, x20, x13
mul x23, x20, x21
adds x3, x7, x6
adcs x4, x16, x11
adcs x25, x24, x2
adc x1, x14, x12
umulh x6, x20, x21
umulh x7, x20, x13
mul x11, x20, x5
umulh x16, x20, x5
adds x2, x3, x22
adcs x24, x4, x11
adcs x12, x25, x23
adcs x14, x1, x15
adc x21, x10, x10
adds x13, x24, x8
adcs x20, x12, x16
adcs x5, x14, x6
adc x22, x21, x7
umulh x3, x27, x22
mul x11, x27, x22
mul x4, x27, x20
mul x23, x27, x13
mul x25, x27, x5
umulh x15, x27, x5
umulh x1, x27, x13
umulh x8, x27, x20
adds x24, x9, x23
adcs x16, x17, x4
adcs x12, x28, x25
adcs x14, x2, x11
adc x6, x3, x10
ldp x21, x7, [x0, #480]
ldp x22, x5, [x0, #464]
ldp x13, x20, [x0, #496]
ldp x9, x23, [x0, #448]
adds x17, x14, x15
adc x4, x6, x10
subs x28, x9, x21
sbcs x25, x23, x7
sbcs x11, x22, x13
sbcs x2, x5, x20
csel x3, x10, x27, hs
and x15, x17, #0x7fffffffffffffff
extr x14, x4, x17, #63
mul x6, x14, x26
adds x9, x24, x6
adcs x21, x16, x1
adcs x23, x12, x8
adc x7, x15, x10
subs x22, x28, x3
sbcs x13, x25, x10
sbcs x5, x11, x10
sbc x20, x2, x10
stp x9, x21, [x0, #128]
stp x23, x7, [x0, #144]
umulh x4, x22, x13
umulh x17, x22, x20
mul x14, x22, x20
umulh x24, x22, x5
mul x6, x22, x5
umulh x16, x13, x20
mul x1, x13, x20
umulh x12, x13, x5
mul x8, x13, x5
mul x15, x5, x20
umulh x28, x5, x20
mul x3, x22, x13
adds x25, x6, x4
adcs x11, x14, x24
adc x2, x17, x10
mul x9, x13, x13
umulh x21, x22, x22
mul x23, x22, x22
lsl x7, x3, #1
adds x6, x11, x8
adcs x4, x2, x1
adc x14, x16, x10
umulh x24, x13, x13
extr x17, x25, x3, #63
mul x22, x5, x5
umulh x11, x5, x5
adds x8, x4, x12
adcs x1, x14, x15
adc x2, x28, x10
extr x16, x6, x25, #63
umulh x13, x20, x20
mul x3, x20, x20
lsr x5, x2, #63
extr x4, x8, x6, #63
extr x12, x1, x8, #63
extr x14, x2, x1, #63
adds x15, x7, x21
adcs x28, x17, x9
adcs x25, x16, x24
adcs x20, x4, x22
adcs x6, x12, x11
adcs x8, x14, x3
adc x1, x5, x13
umulh x2, x27, x1
mul x7, x27, x6
mul x21, x27, x20
mul x17, x27, x1
mul x9, x27, x8
umulh x24, x27, x8
umulh x16, x27, x6
umulh x4, x27, x20
adds x22, x23, x21
adcs x12, x15, x7
adcs x11, x28, x9
adcs x3, x25, x17
adc x14, x2, x10
ldp x13, x5, [x0, #448]
ldp x1, x8, [x0, #464]
ldp x6, x20, [x0, #496]
ldp x21, x23, [x0, #480]
adds x15, x3, x24
adc x7, x14, x10
adds x9, x13, x21
adcs x28, x5, x23
adcs x17, x1, x6
adcs x25, x8, x20
csel x2, x27, x10, hs
extr x24, x7, x15, #63
and x3, x15, #0x7fffffffffffffff
mul x14, x24, x26
adds x13, x22, x14
adcs x21, x12, x4
adcs x5, x11, x16
adc x23, x3, x10
adds x6, x9, x2
adcs x1, x28, x10
adc x20, x17, x10
stp x13, x21, [x0, #192]
stp x5, x23, [x0, #208]
umulh x8, x6, x20
umulh x7, x6, x25
mul x15, x1, x20
mul x24, x6, x25
umulh x22, x1, x25
mul x14, x6, x20
umulh x4, x6, x1
umulh x12, x20, x25
mul x16, x1, x25
umulh x11, x1, x20
mul x3, x20, x25
mul x9, x6, x1
adds x2, x14, x4
adcs x28, x24, x8
adc x17, x7, x10
lsl x13, x9, #1
umulh x21, x6, x6
mul x5, x6, x6
mul x23, x1, x1
adds x14, x28, x15
adcs x4, x17, x16
adc x24, x22, x10
umulh x8, x1, x1
extr x7, x2, x9, #63
umulh x6, x20, x20
mul x15, x20, x20
adds x28, x4, x11
adcs x17, x24, x3
adc x16, x12, x10
extr x22, x14, x2, #63
umulh x1, x25, x25
mul x9, x25, x25
lsr x20, x16, #63
extr x4, x16, x17, #63
extr x11, x17, x28, #63
extr x24, x28, x14, #63
adds x3, x13, x21
adcs x12, x7, x23
adcs x2, x22, x8
adcs x25, x24, x15
adcs x16, x11, x6
adcs x17, x4, x9
adc x14, x20, x1
umulh x28, x27, x14
mul x13, x27, x25
mul x21, x27, x14
mul x23, x27, x17
mul x7, x27, x16
umulh x8, x27, x17
umulh x22, x27, x16
umulh x24, x27, x25
adds x15, x5, x13
adcs x11, x3, x7
adcs x6, x12, x23
adcs x4, x2, x21
adc x9, x28, x10
ldp x1, x20, [x0, #192]
ldp x14, x17, [x0, #208]
ldr x16, [x0, #64]
adds x25, x4, x8
adc x13, x9, x10
mul x5, x16, x20
mul x3, x16, x17
mul x7, x16, x14
mul x23, x16, x1
extr x12, x13, x25, #63
umulh x2, x16, x1
and x21, x25, #0x7fffffffffffffff
umulh x28, x16, x20
mul x4, x12, x26
umulh x8, x16, x14
adds x9, x15, x4
adcs x13, x11, x24
adcs x25, x6, x22
adc x12, x21, x10
umulh x15, x16, x17
adds x4, x5, x2
adcs x24, x7, x28
adcs x11, x3, x8
adc x22, x15, x10
stp x9, x13, [x0, #160]
stp x25, x12, [x0, #176]
ldr x6, [x0, #72]
mul x21, x6, x1
mul x16, x6, x20
mul x5, x6, x14
mul x2, x6, x17
umulh x7, x6, x1
umulh x28, x6, x17
umulh x3, x6, x20
umulh x8, x6, x14
ldr x15, [x0, #80]
adds x13, x4, x21
adcs x9, x24, x16
adcs x25, x11, x5
adcs x12, x22, x2
adc x6, x10, x10
mul x4, x15, x1
mul x21, x15, x17
mul x24, x15, x14
mul x16, x15, x20
adds x11, x9, x7
adcs x5, x25, x3
adcs x2, x12, x8
adc x22, x6, x28
umulh x9, x15, x20
umulh x7, x15, x17
umulh x25, x15, x14
umulh x3, x15, x1
ldr x8, [x0, #88]
adds x12, x11, x4
adcs x28, x5, x16
adcs x6, x2, x24
adcs x15, x22, x21
adc x11, x10, x10
mul x4, x8, x1
umulh x16, x8, x1
mul x5, x8, x14
mul x24, x8, x17
adds x2, x28, x3
adcs x21, x6, x9
adcs x22, x15, x25
adc x1, x11, x7
umulh x3, x8, x14
umulh x28, x8, x17
mul x9, x8, x20
umulh x6, x8, x20
adds x25, x2, x4
adcs x15, x21, x9
adcs x7, x22, x5
adcs x11, x1, x24
adc x14, x10, x10
adds x17, x15, x16
adcs x8, x7, x6
adcs x20, x11, x3
adc x4, x14, x28
umulh x2, x27, x4
mul x9, x27, x8
mul x21, x27, x17
mul x5, x27, x20
mul x22, x27, x4
umulh x24, x27, x20
umulh x1, x27, x17
umulh x16, x27, x8
adds x15, x23, x21
adcs x6, x13, x9
adcs x7, x12, x5
adcs x11, x25, x22
adc x3, x2, x10
adds x14, x11, x24
adc x28, x3, x10
extr x4, x28, x14, #63
and x20, x14, #0x7fffffffffffffff
mul x17, x4, x26
adds x8, x15, x17
adcs x23, x6, x1
adcs x21, x7, x16
adc x13, x20, x10
stp x8, x23, [x0, #192]
stp x21, x13, [x0, #208]
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
.globl lab_sc_o3_21_30_0
lab_sc_o3_21_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x11, x16, x5
adcs x25, x1, x28
csel x24, x27, x10, hs
stp x9, x21, [x0, #224]
stp x17, x3, [x0, #240]
stp x6, x15, [x0, #256]
stp x8, x23, [x0, #272]
subs x7, x12, x14
sbcs x16, x20, x10
sbcs x5, x13, x10
sbc x28, x4, x10
adds x1, x22, x24
adcs x9, x2, x10
adc x21, x11, x10
ldp x17, x3, [x0, #224]
ldp x6, x15, [x0, #240]
stp x7, x16, [x0, #320]
stp x1, x9, [x0, #288]
stp x21, x25, [x0, #304]
stp x5, x28, [x0, #336]
umulh x8, x17, x3
umulh x23, x17, x6
umulh x12, x17, x15
mul x14, x17, x6
mul x20, x17, x15
umulh x13, x3, x15
mul x4, x3, x6
mul x22, x3, x15
umulh x24, x3, x6
umulh x2, x6, x15
mul x11, x6, x15
mul x7, x17, x3
umulh x16, x17, x17
umulh x1, x3, x3
adds x9, x14, x8
adcs x21, x20, x23
adc x25, x12, x10
mul x5, x3, x3
umulh x28, x6, x6
mul x8, x6, x6
umulh x14, x15, x15
mul x20, x15, x15
mul x23, x17, x17
lsl x12, x7, #1
adds x3, x21, x4
adcs x6, x25, x22
adc x15, x13, x10
extr x17, x9, x7, #63
adds x21, x6, x24
adcs x4, x15, x11
adc x25, x2, x10
extr x22, x3, x9, #63
lsr x13, x25, #63
extr x7, x25, x4, #63
extr x24, x4, x21, #63
extr x6, x21, x3, #63
adds x11, x12, x16
adcs x15, x17, x5
adcs x2, x22, x1
adcs x9, x6, x8
adcs x25, x24, x28
adcs x4, x7, x20
adc x21, x13, x14
ldp x3, x12, [x0, #256]
ldp x16, x17, [x0, #272]
umulh x5, x3, x12
umulh x1, x3, x16
mul x22, x3, x16
mul x8, x3, x17
mul x6, x3, x12
umulh x24, x27, x21
mul x28, x27, x21
mul x20, x27, x9
umulh x7, x3, x17
umulh x14, x27, x9
mul x13, x27, x25
umulh x21, x27, x25
mul x9, x27, x4
umulh x25, x27, x4
adds x4, x23, x20
adcs x20, x11, x13
adcs x23, x15, x9
adcs x11, x2, x28
adc x13, x24, x10
umulh x9, x12, x17
adds x15, x22, x5
adcs x28, x8, x1
adc x2, x7, x10
mul x24, x12, x16
mul x22, x12, x17
umulh x5, x12, x16
umulh x8, x16, x17
adds x1, x28, x24
adcs x7, x2, x22
adc x28, x9, x10
mul x24, x16, x17
adds x2, x11, x25
adc x22, x13, x10
adds x9, x7, x5
adcs x11, x28, x24
adc x25, x8, x10
extr x13, x22, x2, #63
and x7, x2, #0x7fffffffffffffff
mul x5, x13, x26
lsr x28, x25, #63
extr x24, x25, x11, #63
adds x8, x4, x5
adcs x22, x20, x14
adcs x2, x23, x21
adc x13, x7, x10
extr x25, x11, x9, #63
extr x4, x9, x1, #63
extr x5, x1, x15, #63
extr x20, x15, x6, #63
stp x8, x22, [x0, #352]
lsl x14, x6, #1
stp x2, x13, [x0, #368]
umulh x23, x3, x3
umulh x21, x12, x12
umulh x7, x16, x16
umulh x11, x17, x17
mul x9, x12, x12
mul x1, x16, x16
mul x15, x17, x17
mul x8, x3, x3
adds x22, x14, x23
adcs x6, x20, x9
adcs x2, x5, x21
adcs x13, x4, x1
adcs x12, x25, x7
adcs x16, x24, x15
adc x17, x28, x11
ldp x3, x23, [x0, #224]
ldp x14, x9, [x0, #240]
ldr x20, [x0, #320]
mul x21, x20, x23
mul x5, x20, x14
mul x4, x20, x9
mul x1, x20, x3
umulh x25, x27, x17
mul x7, x27, x17
mul x24, x27, x13
umulh x15, x20, x3
umulh x28, x27, x13
mul x11, x27, x12
umulh x17, x27, x12
mul x13, x27, x16
umulh x12, x27, x16
adds x16, x8, x24
adcs x24, x22, x11
adcs x8, x6, x13
adcs x11, x2, x7
adc x22, x25, x10
umulh x6, x20, x23
umulh x13, x20, x14
umulh x2, x20, x9
ldr x7, [x0, #328]
adds x25, x21, x15
adcs x20, x5, x6
adcs x21, x4, x13
adc x15, x2, x10
adds x5, x11, x12
adc x6, x22, x10
mul x4, x7, x3
mul x13, x7, x23
mul x2, x7, x14
mul x11, x7, x9
extr x12, x6, x5, #63
and x22, x5, #0x7fffffffffffffff
mul x6, x12, x26
adds x5, x25, x4
adcs x12, x20, x13
adcs x25, x21, x2
adcs x4, x15, x11
adc x20, x10, x10
adds x13, x16, x6
adcs x2, x24, x28
adcs x21, x8, x17
adc x11, x22, x10
umulh x15, x7, x3
umulh x16, x7, x23
umulh x6, x7, x14
umulh x28, x7, x9
stp x13, x2, [x0, #384]
stp x21, x11, [x0, #400]
ldr x24, [x0, #336]
adds x8, x12, x15
adcs x17, x25, x16
adcs x22, x4, x6
adc x7, x20, x28
ldr x13, [x0, #344]
mul x2, x24, x3
mul x21, x24, x23
mul x11, x24, x14
mul x12, x24, x9
umulh x15, x24, x3
umulh x16, x24, x23
umulh x25, x24, x14
umulh x6, x24, x9
mul x4, x13, x3
umulh x28, x13, x3
mul x20, x13, x23
adds x24, x8, x2
adcs x3, x17, x21
adcs x2, x22, x11
adcs x8, x7, x12
adc x21, x10, x10
umulh x17, x13, x23
mul x11, x13, x14
umulh x22, x13, x14
mul x12, x13, x9
umulh x7, x13, x9
adds x23, x3, x15
adcs x14, x2, x16
adcs x13, x8, x25
adc x9, x21, x6
adds x15, x23, x4
adcs x3, x14, x20
adcs x16, x13, x11
adcs x2, x9, x12
adc x25, x10, x10
ldp x8, x21, [x0, #256]
ldp x6, x4, [x0, #272]
ldr x23, [x0, #288]
adds x20, x3, x28
adcs x14, x16, x17
adcs x11, x2, x22
adc x13, x25, x7
mul x9, x23, x21
mul x12, x23, x6
mul x28, x23, x4
mul x3, x23, x8
umulh x16, x27, x13
mul x17, x27, x13
mul x2, x27, x20
umulh x22, x23, x8
umulh x25, x27, x20
mul x7, x27, x14
umulh x13, x27, x14
mul x20, x27, x11
umulh x14, x27, x11
adds x11, x1, x2
adcs x1, x5, x7
adcs x2, x24, x20
adcs x5, x15, x17
adc x7, x16, x10
umulh x24, x23, x21
umulh x20, x23, x6
umulh x15, x23, x4
ldr x17, [x0, #296]
adds x16, x9, x22
adcs x23, x12, x24
adcs x22, x28, x20
adc x9, x15, x10
adds x12, x5, x14
adc x24, x7, x10
mul x28, x17, x8
mul x20, x17, x21
mul x15, x17, x6
mul x14, x17, x4
extr x5, x24, x12, #63
and x7, x12, #0x7fffffffffffffff
mul x24, x5, x26
adds x12, x16, x28
adcs x5, x23, x20
adcs x28, x22, x15
adcs x16, x9, x14
adc x20, x10, x10
adds x23, x11, x24
adcs x22, x1, x25
adcs x15, x2, x13
adc x9, x7, x10
umulh x14, x17, x8
umulh x11, x17, x21
umulh x24, x17, x6
umulh x1, x17, x4
stp x23, x22, [x0, #448]
stp x15, x9, [x0, #464]
ldr x25, [x0, #304]
adds x13, x5, x14
adcs x2, x28, x11
adcs x7, x16, x24
adc x17, x20, x1
ldr x23, [x0, #312]
mul x22, x25, x8
mul x9, x25, x21
mul x15, x25, x6
mul x5, x25, x4
umulh x14, x25, x8
umulh x28, x25, x21
umulh x11, x25, x6
umulh x16, x25, x4
mul x24, x23, x8
umulh x20, x23, x8
mul x1, x23, x21
adds x25, x13, x22
adcs x8, x2, x9
adcs x13, x7, x15
adcs x22, x17, x5
adc x2, x10, x10
umulh x9, x23, x21
mul x7, x23, x6
umulh x15, x23, x6
mul x5, x23, x4
umulh x17, x23, x4
adds x21, x8, x14
adcs x6, x13, x28
adcs x4, x22, x11
adc x23, x2, x16
adds x8, x21, x24
adcs x14, x6, x1
adcs x13, x4, x7
adcs x28, x23, x5
adc x11, x10, x10
ldp x22, x16, [x0, #352]
ldp x2, x21, [x0, #368]
ldp x24, x1, [x0, #384]
adds x6, x14, x20
adcs x7, x13, x9
adcs x4, x28, x15
adc x5, x11, x17
ldp x23, x20, [x0, #400]
umulh x14, x27, x5
mul x9, x27, x5
mul x13, x27, x6
umulh x15, x27, x6
mul x28, x27, x7
umulh x17, x27, x7
mul x11, x27, x4
umulh x5, x27, x4
subs x6, x22, x24
sbcs x7, x16, x1
sbcs x4, x2, x23
sbcs x24, x21, x20
csel x22, x10, x27, hs
adds x1, x3, x13
adcs x16, x12, x28
adcs x2, x25, x11
adcs x23, x8, x9
adc x21, x14, x10
ldp x20, x13, [x0, #384]
ldp x3, x28, [x0, #400]
ldr x12, [x0, #352]
subs x25, x6, x22
sbcs x11, x7, x10
sbcs x9, x4, x10
sbc x8, x24, x10
adds x14, x23, x5
adc x22, x21, x10
mul x6, x12, x13
mul x7, x12, x3
mul x4, x12, x28
mul x24, x12, x20
extr x23, x22, x14, #63
and x5, x14, #0x7fffffffffffffff
stp x9, x8, [x0, #432]
stp x25, x11, [x0, #416]
mul x21, x23, x26
umulh x22, x12, x20
umulh x14, x12, x13
umulh x9, x12, x3
adds x8, x1, x21
adcs x25, x16, x15
adcs x11, x2, x17
adc x23, x5, x10
umulh x1, x12, x28
stp x8, x25, [x0, #480]
stp x11, x23, [x0, #496]
ldr x21, [x0, #360]
adds x16, x6, x22
adcs x15, x7, x14
adcs x2, x4, x9
adc x17, x1, x10
ldr x5, [x0, #368]
mul x12, x21, x20
mul x8, x21, x13
mul x25, x21, x3
mul x11, x21, x28
umulh x23, x21, x20
umulh x22, x21, x13
umulh x6, x21, x3
umulh x14, x21, x28
mul x7, x5, x20
mul x9, x5, x13
mul x4, x5, x3
adds x1, x16, x12
adcs x21, x15, x8
adcs x12, x2, x25
adcs x16, x17, x11
adc x8, x10, x10
mul x15, x5, x28
umulh x25, x5, x20
umulh x2, x5, x13
adds x11, x21, x23
adcs x17, x12, x22
adcs x23, x16, x6
adc x21, x8, x14
umulh x22, x5, x3
umulh x12, x5, x28
ldr x16, [x0, #376]
adds x6, x11, x7
adcs x8, x17, x9
adcs x14, x23, x4
adcs x5, x21, x15
adc x7, x10, x10
mul x11, x16, x20
umulh x9, x16, x20
mul x17, x16, x13
umulh x23, x16, x13
mul x4, x16, x3
umulh x21, x16, x3
mul x15, x16, x28
umulh x20, x16, x28
adds x13, x8, x25
adcs x3, x14, x2
adcs x28, x5, x22
adc x16, x7, x12
adds x8, x13, x11
adcs x25, x3, x17
adcs x14, x28, x4
adcs x2, x16, x15
adc x5, x10, x10
ldp x22, x7, [x0, #416]
ldp x12, x13, [x0, #352]
ldp x11, x3, [x0, #368]
adds x17, x25, x9
adcs x28, x14, x23
adcs x4, x2, x21
adc x15, x5, x20
ldp x16, x25, [x0, #432]
movz x9, #56129, lsl #0
movk x9, #1, lsl #16
mul x14, x22, x9
umulh x23, x27, x15
mul x21, x27, x15
mul x2, x27, x17
mul x20, x7, x9
umulh x5, x27, x17
mul x15, x27, x28
umulh x17, x27, x28
mul x28, x27, x4
umulh x4, x27, x4
adds x24, x24, x2
adcs x2, x1, x15
adcs x1, x6, x28
adcs x15, x8, x21
adc x28, x23, x10
umulh x6, x22, x9
umulh x8, x7, x9
umulh x21, x25, x9
mul x23, x25, x9
mul x22, x16, x9
umulh x7, x16, x9
adds x25, x12, x14
adcs x16, x13, x20
adcs x9, x11, x22
adcs x12, x3, x23
adc x14, x21, x10
adds x13, x15, x4
adc x20, x28, x10
extr x22, x20, x13, #63
and x11, x13, #0x7fffffffffffffff
mul x23, x22, x26
adds x3, x12, x12
adc x21, x14, x14
adds x15, x24, x23
adcs x4, x2, x5
adcs x28, x1, x17
adc x20, x11, x10
mul x13, x21, x26
lsr x22, x3, #1
adds x12, x25, x13
adcs x14, x16, x6
adcs x24, x9, x8
adc x23, x22, x7
stp x15, x4, [x0, #96]
stp x28, x20, [x0, #112]
ldr x5, [x0, #416]
ldr x2, [x0, #424]
stp x12, x14, [x0, #128]
stp x24, x23, [x0, #144]
ldp x1, x17, [x0, #128]
ldp x11, x21, [x0, #144]
ldr x3, [x0, #432]
umulh x25, x5, x1
umulh x13, x5, x17
umulh x6, x5, x11
umulh x16, x5, x21
mul x8, x5, x17
mul x9, x5, x11
mul x7, x5, x21
mul x22, x2, x1
mul x15, x2, x17
mul x4, x2, x11
mul x28, x2, x21
umulh x20, x2, x1
umulh x14, x2, x17
umulh x12, x2, x11
umulh x24, x2, x21
adds x23, x8, x25
adcs x2, x9, x13
adcs x8, x7, x6
adc x25, x16, x10
mul x9, x5, x1
mul x13, x3, x1
mul x7, x3, x17
mul x6, x3, x11
adds x16, x23, x22
adcs x5, x2, x15
adcs x23, x8, x4
adcs x22, x25, x28
adc x2, x10, x10
mul x15, x3, x21
umulh x8, x3, x1
umulh x4, x3, x17
adds x28, x5, x20
adcs x25, x23, x14
adcs x5, x22, x12
adc x20, x2, x24
umulh x23, x3, x11
umulh x14, x3, x21
ldr x12, [x0, #440]
adds x22, x28, x13
adcs x24, x25, x7
adcs x2, x5, x6
adcs x3, x20, x15
adc x28, x10, x10
mul x13, x12, x1
umulh x7, x12, x1
mul x25, x12, x17
umulh x6, x12, x17
mul x5, x12, x11
umulh x15, x12, x11
mul x20, x12, x21
umulh x1, x12, x21
adds x17, x24, x8
adcs x11, x2, x4
adcs x12, x3, x23
adc x21, x28, x14
adds x8, x17, x13
adcs x24, x11, x25
adcs x4, x12, x5
adcs x2, x21, x20
adc x23, x10, x10
ldp x3, x14, [x0, #448]
ldp x28, x13, [x0, #464]
ldp x17, x25, [x0, #480]
adds x11, x24, x7
adcs x5, x4, x6
adcs x12, x2, x15
adc x20, x23, x1
ldp x21, x7, [x0, #496]
umulh x24, x27, x20
mul x6, x27, x20
mul x4, x27, x11
umulh x2, x27, x11
subs x15, x3, x17
sbcs x23, x14, x25
sbcs x1, x28, x21
sbcs x20, x13, x7
csel x11, x10, x27, hs
mul x3, x27, x5
umulh x17, x27, x5
mul x14, x27, x12
umulh x25, x27, x12
adds x28, x9, x4
adcs x21, x16, x3
adcs x13, x22, x14
adcs x7, x8, x6
adc x5, x24, x10
subs x12, x15, x11
sbcs x9, x23, x10
sbcs x4, x1, x10
sbc x16, x20, x10
adds x3, x7, x25
adc x22, x5, x10
umulh x14, x12, x9
umulh x6, x12, x4
umulh x8, x12, x16
mul x24, x12, x4
mul x15, x12, x16
mul x11, x9, x4
mul x23, x9, x16
umulh x1, x9, x4
mul x20, x12, x9
extr x25, x22, x3, #63
umulh x7, x9, x16
and x5, x3, #0x7fffffffffffffff
mul x22, x25, x26
adds x3, x28, x22
adcs x25, x21, x2
adcs x28, x13, x17
adc x22, x5, x10
adds x21, x24, x14
adcs x2, x15, x6
adc x13, x8, x10
umulh x17, x4, x16
mul x5, x4, x16
adds x24, x2, x11
adcs x14, x13, x23
adc x15, x7, x10
stp x3, x25, [x0, #128]
stp x28, x22, [x0, #144]
umulh x6, x12, x12
umulh x8, x9, x9
umulh x2, x4, x4
umulh x11, x16, x16
mul x23, x9, x9
mul x13, x4, x4
mul x7, x16, x16
adds x3, x14, x1
adcs x25, x15, x5
adc x28, x17, x10
extr x22, x24, x21, #63
extr x9, x21, x20, #63
lsl x4, x20, #1
mul x16, x12, x12
lsr x14, x28, #63
extr x1, x28, x25, #63
extr x15, x25, x3, #63
extr x5, x3, x24, #63
adds x17, x4, x6
adcs x21, x9, x23
adcs x20, x22, x8
adcs x12, x5, x13
adcs x28, x15, x2
adcs x25, x1, x7
adc x24, x14, x11
ldp x3, x4, [x0, #448]
ldp x6, x9, [x0, #464]
ldp x23, x8, [x0, #480]
ldp x22, x5, [x0, #496]
adds x13, x3, x23
adcs x15, x4, x8
adcs x2, x6, x22
adcs x7, x9, x5
csel x1, x27, x10, hs
umulh x11, x27, x24
mul x14, x27, x12
mul x3, x27, x28
mul x23, x27, x24
umulh x4, x27, x12
umulh x8, x27, x28
mul x22, x27, x25
umulh x6, x27, x25
adds x5, x16, x14
adcs x9, x17, x3
adcs x24, x21, x22
adcs x12, x20, x23
adc x28, x11, x10
adds x25, x13, x1
adcs x14, x15, x10
adc x16, x2, x10
umulh x17, x25, x14
umulh x3, x25, x16
umulh x22, x25, x7
adds x21, x12, x6
adc x23, x28, x10
mul x20, x25, x16
mul x11, x25, x7
umulh x13, x14, x7
mul x1, x14, x16
mul x15, x14, x7
umulh x2, x14, x16
extr x6, x23, x21, #63
and x12, x21, #0x7fffffffffffffff
umulh x28, x16, x7
mul x23, x6, x26
adds x21, x20, x17
adcs x6, x11, x3
adc x20, x22, x10
mul x17, x16, x7
mul x11, x25, x14
adds x3, x5, x23
adcs x22, x9, x4
adcs x5, x24, x8
adc x23, x12, x10
adds x4, x6, x1
adcs x9, x20, x15
adc x8, x13, x10
stp x3, x22, [x0, #192]
stp x5, x23, [x0, #208]
adds x24, x9, x2
adcs x12, x8, x17
adc x1, x28, x10
umulh x6, x25, x25
umulh x20, x14, x14
umulh x15, x16, x16
umulh x13, x7, x7
mul x3, x14, x14
mul x22, x16, x16
mul x5, x7, x7
extr x23, x4, x21, #63
extr x9, x21, x11, #63
lsr x2, x1, #63
extr x8, x1, x12, #63
extr x17, x12, x24, #63
extr x28, x24, x4, #63
lsl x14, x11, #1
mul x16, x25, x25
adds x7, x14, x6
adcs x21, x9, x3
adcs x1, x23, x20
adcs x12, x28, x22
adcs x4, x17, x15
adcs x24, x8, x5
adc x11, x2, x13
ldp x25, x14, [x0, #192]
ldp x6, x3, [x0, #208]
ldr x9, [x0, #64]
mul x20, x9, x14
mul x23, x9, x6
mul x28, x9, x3
umulh x22, x27, x11
mul x17, x27, x11
mul x15, x27, x12
umulh x8, x9, x25
umulh x5, x27, x12
mul x13, x27, x4
umulh x2, x9, x14
umulh x11, x27, x4
mul x12, x27, x24
umulh x4, x27, x24
adds x24, x16, x15
adcs x15, x7, x13
adcs x16, x21, x12
adcs x7, x1, x17
adc x13, x22, x10
umulh x12, x9, x6
umulh x21, x9, x3
ldr x1, [x0, #72]
mul x17, x9, x25
adds x22, x20, x8
adcs x9, x23, x2
adcs x20, x28, x12
adc x8, x21, x10
adds x23, x7, x4
adc x2, x13, x10
mul x28, x1, x25
mul x12, x1, x14
mul x21, x1, x6
mul x7, x1, x3
extr x4, x2, x23, #63
and x13, x23, #0x7fffffffffffffff
mul x2, x4, x26
adds x23, x22, x28
adcs x4, x9, x12
adcs x22, x20, x21
adcs x28, x8, x7
adc x9, x10, x10
adds x12, x24, x2
adcs x20, x15, x5
adcs x21, x16, x11
adc x7, x13, x10
umulh x8, x1, x25
umulh x24, x1, x14
umulh x2, x1, x6
umulh x5, x1, x3
stp x12, x20, [x0, #160]
stp x21, x7, [x0, #176]
ldr x15, [x0, #80]
adds x11, x4, x8
adcs x16, x22, x24
adcs x13, x28, x2
adc x1, x9, x5
ldr x20, [x0, #88]
mul x12, x15, x25
mul x21, x15, x14
mul x7, x15, x6
mul x4, x15, x3
umulh x8, x15, x25
umulh x22, x15, x14
umulh x24, x15, x6
umulh x2, x15, x3
mul x28, x20, x25
umulh x5, x20, x25
mul x9, x20, x14
adds x15, x11, x12
adcs x25, x16, x21
adcs x11, x13, x7
adcs x12, x1, x4
adc x21, x10, x10
umulh x16, x20, x14
mul x7, x20, x6
umulh x13, x20, x6
mul x4, x20, x3
umulh x1, x20, x3
adds x14, x25, x8
adcs x6, x11, x22
adcs x20, x12, x24
adc x3, x21, x2
adds x8, x14, x28
adcs x25, x6, x9
adcs x22, x20, x7
adcs x11, x3, x4
adc x24, x10, x10
adds x12, x25, x5
adcs x2, x22, x16
adcs x21, x11, x13
adc x28, x24, x1
umulh x14, x27, x28
mul x9, x27, x12
mul x6, x27, x2
mul x7, x27, x21
mul x20, x27, x28
umulh x4, x27, x21
umulh x3, x27, x12
umulh x5, x27, x2
adds x25, x17, x9
adcs x16, x23, x6
adcs x22, x15, x7
adcs x11, x8, x20
adc x13, x14, x10
adds x24, x11, x4
adc x1, x13, x10
extr x28, x1, x24, #63
and x21, x24, #0x7fffffffffffffff
mul x12, x28, x26
adds x2, x25, x12
adcs x17, x16, x3
adcs x9, x22, x5
adc x23, x21, x10
stp x2, x17, [x0, #192]
stp x9, x23, [x0, #208]
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
.globl lab_sc_o3_21_30_1
lab_sc_o3_21_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
umulh x3, x12, x9
umulh x7, x12, x25
umulh x11, x12, x24
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
mul x4, x12, x24
mul x8, x12, x25
umulh x2, x9, x24
mul x13, x25, x24
umulh x17, x9, x25
mul x14, x9, x24
umulh x1, x25, x24
mul x6, x9, x25
mul x20, x12, x9
adds x22, x8, x3
adcs x16, x4, x7
adc x23, x11, x10
umulh x15, x25, x25
mul x21, x25, x25
umulh x5, x9, x9
mul x28, x9, x9
umulh x3, x24, x24
mul x8, x24, x24
umulh x4, x12, x12
mul x7, x12, x12
lsl x11, x20, #1
adds x25, x16, x6
adcs x9, x23, x14
adc x24, x2, x10
extr x12, x22, x20, #63
adds x16, x9, x17
adcs x6, x24, x13
adc x23, x1, x10
extr x14, x25, x22, #63
lsr x2, x23, #63
extr x20, x23, x6, #63
extr x17, x6, x16, #63
extr x9, x16, x25, #63
adds x13, x11, x4
adcs x24, x12, x28
adcs x1, x14, x5
adcs x22, x9, x21
adcs x23, x17, x15
adcs x6, x20, x8
adc x16, x2, x3
ldp x25, x11, [x0, #272]
ldp x4, x12, [x0, #256]
umulh x28, x4, x12
umulh x5, x4, x25
mul x14, x4, x25
mul x21, x4, x11
mul x9, x4, x12
umulh x17, x27, x16
mul x15, x27, x16
mul x8, x27, x22
umulh x20, x4, x11
mul x3, x27, x23
umulh x2, x27, x23
umulh x16, x27, x22
mul x23, x27, x6
umulh x22, x27, x6
adds x6, x7, x8
adcs x8, x13, x3
adcs x7, x24, x23
adcs x13, x1, x15
adc x3, x17, x10
umulh x23, x12, x11
adds x24, x14, x28
adcs x15, x21, x5
adc x1, x20, x10
mul x17, x12, x11
umulh x14, x12, x25
umulh x28, x25, x11
mul x21, x25, x11
adds x5, x13, x22
adc x20, x3, x10
mul x13, x12, x25
extr x22, x20, x5, #63
and x3, x5, #0x7fffffffffffffff
adds x20, x15, x13
adcs x5, x1, x17
adc x15, x23, x10
mul x13, x22, x26
adds x1, x6, x13
adcs x17, x8, x16
adcs x23, x7, x2
adc x22, x3, x10
adds x6, x5, x14
adcs x13, x15, x21
adc x8, x28, x10
extr x16, x20, x24, #63
extr x7, x24, x9, #63
lsr x2, x8, #63
extr x3, x8, x13, #63
extr x5, x13, x6, #63
extr x14, x6, x20, #63
stp x23, x22, [x0, #368]
stp x1, x17, [x0, #352]
umulh x15, x12, x12
umulh x21, x4, x4
mul x28, x12, x12
mul x24, x25, x25
umulh x8, x11, x11
lsl x13, x9, #1
mul x20, x11, x11
umulh x6, x25, x25
mul x23, x4, x4
adds x22, x13, x21
adcs x1, x7, x28
adcs x17, x16, x15
adcs x12, x14, x24
adcs x9, x5, x6
adcs x11, x3, x20
adc x25, x2, x8
ldp x4, x21, [x0, #240]
ldr x13, [x0, #320]
ldp x28, x7, [x0, #224]
mul x15, x13, x4
mul x16, x13, x7
mul x14, x13, x21
mul x24, x13, x28
mul x5, x27, x12
umulh x6, x13, x28
mul x3, x27, x25
umulh x20, x27, x25
mul x2, x27, x9
umulh x8, x27, x9
umulh x25, x27, x12
mul x9, x27, x11
umulh x12, x27, x11
adds x11, x23, x5
adcs x5, x22, x2
adcs x23, x1, x9
adcs x2, x17, x3
adc x22, x20, x10
umulh x1, x13, x21
umulh x9, x13, x4
umulh x17, x13, x7
ldr x3, [x0, #328]
adds x20, x16, x6
adcs x13, x15, x17
adcs x16, x14, x9
adc x6, x1, x10
adds x15, x2, x12
adc x17, x22, x10
mul x14, x3, x28
mul x9, x3, x21
mul x1, x3, x7
mul x2, x3, x4
extr x12, x17, x15, #63
and x22, x15, #0x7fffffffffffffff
mul x17, x12, x26
adds x15, x20, x14
adcs x12, x13, x1
adcs x20, x16, x2
adcs x14, x6, x9
adc x13, x10, x10
adds x1, x11, x17
adcs x2, x5, x25
adcs x16, x23, x8
adc x9, x22, x10
umulh x6, x3, x21
umulh x11, x3, x4
umulh x17, x3, x28
umulh x25, x3, x7
stp x1, x2, [x0, #384]
stp x16, x9, [x0, #400]
ldr x5, [x0, #336]
adds x23, x12, x17
adcs x8, x20, x25
adcs x22, x14, x11
adc x3, x13, x6
ldr x1, [x0, #344]
mul x2, x5, x28
mul x16, x5, x21
mul x9, x5, x7
mul x12, x5, x4
umulh x17, x5, x4
umulh x25, x5, x28
umulh x20, x5, x21
umulh x11, x5, x7
mul x14, x1, x21
umulh x6, x1, x21
mul x13, x1, x28
adds x5, x23, x2
adcs x21, x8, x9
adcs x2, x22, x12
adcs x23, x3, x16
adc x9, x10, x10
umulh x8, x1, x28
umulh x12, x1, x7
mul x22, x1, x7
mul x16, x1, x4
umulh x3, x1, x4
adds x28, x21, x25
adcs x7, x2, x11
adcs x1, x23, x17
adc x4, x9, x20
adds x25, x28, x13
adcs x21, x7, x22
adcs x11, x1, x16
adcs x2, x4, x14
adc x17, x10, x10
ldp x23, x9, [x0, #256]
ldp x20, x13, [x0, #272]
ldr x28, [x0, #288]
adds x22, x21, x8
adcs x7, x11, x12
adcs x16, x2, x3
adc x1, x17, x6
mul x4, x28, x9
mul x14, x28, x13
mul x8, x28, x20
mul x21, x28, x23
umulh x11, x27, x1
mul x12, x27, x1
umulh x2, x27, x16
mul x3, x27, x16
mul x17, x27, x22
umulh x6, x28, x23
umulh x1, x27, x22
mul x16, x27, x7
umulh x22, x27, x7
adds x7, x24, x17
adcs x24, x15, x16
adcs x17, x5, x3
adcs x15, x25, x12
adc x16, x11, x10
umulh x5, x28, x20
umulh x3, x28, x9
umulh x25, x28, x13
ldr x12, [x0, #296]
adds x11, x4, x6
adcs x28, x8, x3
adcs x6, x14, x5
adc x4, x25, x10
adds x8, x15, x2
adc x3, x16, x10
mul x14, x12, x23
mul x5, x12, x9
mul x25, x12, x20
mul x2, x12, x13
extr x15, x3, x8, #63
and x16, x8, #0x7fffffffffffffff
mul x3, x15, x26
adds x8, x11, x14
adcs x15, x28, x5
adcs x14, x6, x25
adcs x11, x4, x2
adc x5, x10, x10
adds x28, x7, x3
adcs x6, x24, x1
adcs x25, x17, x22
adc x4, x16, x10
umulh x2, x12, x9
umulh x7, x12, x13
umulh x3, x12, x23
umulh x24, x12, x20
stp x28, x6, [x0, #448]
stp x25, x4, [x0, #464]
ldr x1, [x0, #304]
adds x22, x15, x3
adcs x17, x14, x2
adcs x16, x11, x24
adc x12, x5, x7
ldr x28, [x0, #312]
mul x6, x1, x23
mul x4, x1, x20
umulh x25, x1, x23
mul x15, x1, x9
umulh x3, x1, x20
mul x14, x1, x13
umulh x2, x1, x13
umulh x11, x1, x9
mul x24, x28, x20
umulh x5, x28, x20
mul x7, x28, x13
umulh x1, x28, x13
adds x20, x22, x6
adcs x13, x17, x15
adcs x22, x16, x4
adcs x6, x12, x14
adc x17, x10, x10
umulh x15, x28, x23
mul x16, x28, x23
mul x4, x28, x9
umulh x14, x28, x9
adds x12, x13, x25
adcs x23, x22, x11
adcs x9, x6, x3
adc x28, x17, x2
adds x13, x12, x16
adcs x25, x23, x4
adcs x22, x9, x24
adcs x11, x28, x7
adc x3, x10, x10
ldp x6, x2, [x0, #384]
ldp x17, x12, [x0, #368]
ldp x16, x4, [x0, #352]
adds x23, x25, x15
adcs x24, x22, x14
adcs x9, x11, x5
adc x7, x3, x1
ldp x28, x15, [x0, #400]
umulh x25, x27, x7
mul x14, x27, x7
mul x22, x27, x24
mul x5, x27, x9
umulh x11, x27, x9
umulh x1, x27, x24
mul x3, x27, x23
umulh x7, x27, x23
subs x9, x16, x6
sbcs x24, x4, x2
sbcs x23, x17, x28
sbcs x6, x12, x15
csel x16, x10, x27, hs
adds x2, x21, x3
adcs x4, x8, x22
adcs x17, x20, x5
adcs x28, x13, x14
adc x12, x25, x10
ldr x15, [x0, #352]
ldp x3, x21, [x0, #400]
ldp x22, x8, [x0, #384]
subs x20, x9, x16
sbcs x5, x24, x10
sbcs x14, x23, x10
sbc x13, x6, x10
adds x25, x28, x11
adc x16, x12, x10
mul x9, x15, x21
mul x24, x15, x3
mul x23, x15, x8
mul x6, x15, x22
extr x28, x16, x25, #63
and x11, x25, #0x7fffffffffffffff
stp x14, x13, [x0, #432]
stp x20, x5, [x0, #416]
mul x12, x28, x26
umulh x16, x15, x3
umulh x25, x15, x22
umulh x14, x15, x8
adds x13, x2, x12
adcs x20, x4, x7
adcs x5, x17, x1
adc x28, x11, x10
umulh x2, x15, x21
stp x13, x20, [x0, #480]
stp x5, x28, [x0, #496]
ldr x12, [x0, #360]
adds x4, x23, x25
adcs x7, x24, x14
adcs x17, x9, x16
adc x1, x2, x10
ldr x11, [x0, #368]
mul x15, x12, x22
mul x13, x12, x3
umulh x20, x12, x3
mul x5, x12, x8
mul x28, x12, x21
mul x25, x11, x21
umulh x23, x12, x21
mul x14, x11, x3
umulh x24, x12, x22
umulh x16, x12, x8
umulh x9, x11, x21
adds x2, x4, x15
adcs x12, x7, x5
adcs x15, x17, x13
adcs x4, x1, x28
adc x5, x10, x10
mul x7, x11, x22
umulh x13, x11, x3
mul x17, x11, x8
adds x28, x12, x24
adcs x1, x15, x16
adcs x24, x4, x20
adc x12, x5, x23
ldr x16, [x0, #376]
umulh x15, x11, x8
umulh x4, x11, x22
adds x20, x28, x7
adcs x5, x1, x17
adcs x23, x24, x14
adcs x11, x12, x25
adc x7, x10, x10
mul x28, x16, x22
umulh x17, x16, x22
mul x1, x16, x3
umulh x24, x16, x3
mul x14, x16, x21
umulh x12, x16, x21
mul x25, x16, x8
umulh x22, x16, x8
adds x3, x5, x4
adcs x21, x23, x15
adcs x8, x11, x13
adc x16, x7, x9
adds x5, x3, x28
adcs x4, x21, x25
adcs x23, x8, x1
adcs x15, x16, x14
adc x11, x10, x10
ldp x13, x7, [x0, #368]
ldp x9, x3, [x0, #416]
ldp x28, x21, [x0, #352]
adds x25, x4, x17
adcs x8, x23, x22
adcs x1, x15, x24
adc x14, x11, x12
movz x16, #56129, lsl #0
ldp x4, x17, [x0, #432]
movk x16, #1, lsl #16
mul x23, x9, x16
umulh x22, x27, x14
mul x24, x27, x14
mul x15, x27, x8
mul x12, x27, x25
umulh x11, x27, x25
umulh x14, x27, x8
mul x25, x27, x1
umulh x8, x27, x1
adds x1, x6, x12
adcs x6, x2, x15
adcs x12, x20, x25
adcs x2, x5, x24
adc x15, x22, x10
mul x25, x4, x16
umulh x20, x17, x16
mul x5, x17, x16
mul x24, x3, x16
umulh x22, x3, x16
umulh x17, x4, x16
umulh x3, x9, x16
adds x4, x28, x23
adcs x9, x21, x24
adcs x16, x13, x25
adcs x28, x7, x5
adc x23, x20, x10
adds x21, x2, x8
adc x24, x15, x10
extr x25, x24, x21, #63
and x13, x21, #0x7fffffffffffffff
mul x5, x25, x26
adds x7, x28, x28
adc x20, x23, x23
adds x2, x1, x5
adcs x8, x6, x11
adcs x15, x12, x14
adc x24, x13, x10
lsr x21, x7, #1
mul x25, x20, x26
adds x28, x4, x25
adcs x23, x9, x3
adcs x1, x16, x22
adc x5, x21, x17
stp x15, x24, [x0, #112]
stp x2, x8, [x0, #96]
ldr x11, [x0, #416]
ldr x6, [x0, #424]
stp x28, x23, [x0, #128]
stp x1, x5, [x0, #144]
ldp x12, x14, [x0, #128]
ldp x13, x7, [x0, #144]
ldr x20, [x0, #432]
umulh x4, x11, x12
umulh x25, x11, x13
umulh x3, x11, x7
umulh x9, x11, x14
mul x22, x11, x14
mul x16, x11, x7
mul x17, x6, x7
mul x21, x11, x13
umulh x15, x6, x13
mul x24, x6, x14
umulh x2, x6, x7
mul x8, x6, x12
mul x23, x6, x13
umulh x28, x6, x12
umulh x1, x6, x14
adds x5, x22, x4
adcs x6, x21, x9
adcs x22, x16, x25
adc x4, x3, x10
mul x21, x11, x12
mul x9, x20, x12
mul x16, x20, x14
mul x25, x20, x13
adds x3, x5, x8
adcs x11, x6, x24
adcs x5, x22, x23
adcs x8, x4, x17
adc x6, x10, x10
mul x24, x20, x7
umulh x22, x20, x14
umulh x23, x20, x7
adds x17, x11, x28
adcs x4, x5, x1
adcs x11, x8, x15
adc x28, x6, x2
umulh x5, x20, x13
umulh x1, x20, x12
ldr x15, [x0, #440]
adds x8, x17, x9
adcs x2, x4, x16
adcs x6, x11, x25
adcs x20, x28, x24
adc x17, x10, x10
mul x9, x15, x12
umulh x16, x15, x12
mul x4, x15, x7
umulh x25, x15, x7
mul x11, x15, x13
umulh x24, x15, x13
mul x28, x15, x14
umulh x12, x15, x14
adds x7, x2, x1
adcs x13, x6, x22
adcs x15, x20, x5
adc x14, x17, x23
adds x1, x7, x9
adcs x2, x13, x28
adcs x22, x15, x11
adcs x6, x14, x4
adc x5, x10, x10
ldp x20, x23, [x0, #480]
ldp x17, x9, [x0, #464]
ldp x7, x28, [x0, #448]
adds x13, x2, x16
adcs x11, x22, x12
adcs x15, x6, x24
adc x4, x5, x25
ldp x14, x16, [x0, #496]
umulh x2, x27, x4
mul x12, x27, x4
mul x22, x27, x11
mul x6, x27, x13
subs x24, x7, x20
sbcs x5, x28, x23
sbcs x25, x17, x14
sbcs x4, x9, x16
csel x7, x10, x27, hs
umulh x20, x27, x13
mul x28, x27, x15
umulh x23, x27, x15
umulh x17, x27, x11
adds x14, x21, x6
adcs x9, x3, x22
adcs x16, x8, x28
adcs x13, x1, x12
adc x15, x2, x10
subs x11, x24, x7
sbcs x21, x5, x10
sbcs x6, x25, x10
sbc x3, x4, x10
adds x22, x13, x23
adc x8, x15, x10
umulh x28, x11, x3
mul x12, x11, x3
umulh x1, x11, x6
mul x2, x11, x6
umulh x24, x11, x21
mul x7, x21, x3
umulh x5, x21, x6
mul x25, x21, x6
mul x4, x11, x21
extr x23, x8, x22, #63
umulh x13, x21, x3
and x15, x22, #0x7fffffffffffffff
mul x8, x23, x26
adds x22, x14, x8
adcs x23, x9, x20
adcs x14, x16, x17
adc x8, x15, x10
adds x9, x2, x24
adcs x20, x12, x1
adc x16, x28, x10
mul x17, x6, x3
umulh x15, x6, x3
adds x2, x20, x25
adcs x24, x16, x7
adc x12, x13, x10
stp x22, x23, [x0, #128]
stp x14, x8, [x0, #144]
umulh x1, x3, x3
mul x28, x21, x21
umulh x20, x21, x21
mul x25, x3, x3
mul x7, x6, x6
extr x16, x9, x4, #63
umulh x13, x6, x6
adds x22, x24, x5
adcs x23, x12, x17
adc x14, x15, x10
extr x8, x2, x9, #63
umulh x21, x11, x11
lsl x3, x4, #1
mul x6, x11, x11
lsr x24, x14, #63
extr x5, x22, x2, #63
extr x12, x23, x22, #63
extr x17, x14, x23, #63
adds x15, x3, x21
adcs x9, x16, x28
adcs x4, x8, x20
adcs x11, x5, x7
adcs x2, x12, x13
adcs x22, x17, x25
adc x23, x24, x1
ldp x14, x3, [x0, #448]
ldp x21, x16, [x0, #464]
ldp x28, x20, [x0, #496]
ldp x8, x5, [x0, #480]
adds x7, x14, x8
adcs x12, x3, x5
adcs x13, x21, x28
adcs x25, x16, x20
csel x17, x27, x10, hs
mul x1, x27, x2
mul x24, x27, x11
mul x14, x27, x23
umulh x8, x27, x23
umulh x3, x27, x2
mul x5, x27, x22
umulh x28, x27, x22
umulh x21, x27, x11
adds x20, x6, x24
adcs x16, x15, x1
adcs x23, x9, x5
adcs x2, x4, x14
adc x22, x8, x10
adds x11, x7, x17
adcs x24, x12, x10
adc x6, x13, x10
umulh x15, x11, x24
umulh x1, x11, x6
umulh x5, x11, x25
adds x9, x2, x28
adc x14, x22, x10
mul x4, x24, x6
mul x8, x11, x25
umulh x7, x24, x25
mul x17, x11, x6
mul x12, x24, x25
umulh x13, x24, x6
extr x28, x14, x9, #63
and x2, x9, #0x7fffffffffffffff
umulh x22, x6, x25
mul x14, x28, x26
adds x9, x17, x15
adcs x28, x8, x1
adc x17, x5, x10
mul x15, x6, x25
mul x8, x11, x24
adds x1, x20, x14
adcs x5, x16, x21
adcs x20, x23, x3
adc x14, x2, x10
adds x21, x28, x4
adcs x16, x17, x12
adc x3, x7, x10
stp x1, x5, [x0, #192]
stp x20, x14, [x0, #208]
umulh x23, x25, x25
adds x2, x16, x13
adcs x4, x3, x15
adc x28, x22, x10
umulh x17, x24, x24
umulh x12, x6, x6
extr x7, x21, x9, #63
extr x1, x9, x8, #63
mul x5, x25, x25
lsl x20, x8, #1
umulh x14, x11, x11
mul x16, x6, x6
mul x13, x24, x24
extr x3, x28, x4, #63
lsr x15, x28, #63
extr x22, x4, x2, #63
extr x9, x2, x21, #63
mul x25, x11, x11
adds x8, x20, x14
adcs x6, x1, x13
adcs x24, x7, x17
adcs x28, x9, x16
adcs x4, x22, x12
adcs x21, x3, x5
adc x2, x15, x23
ldp x11, x20, [x0, #192]
ldp x14, x13, [x0, #208]
ldr x1, [x0, #64]
mul x17, x1, x20
mul x7, x1, x13
mul x9, x1, x14
mul x16, x27, x28
umulh x22, x1, x11
umulh x12, x27, x2
mul x3, x27, x2
mul x5, x27, x21
umulh x23, x27, x21
umulh x15, x27, x28
mul x2, x27, x4
umulh x21, x27, x4
adds x28, x25, x16
adcs x4, x8, x2
adcs x16, x6, x5
adcs x25, x24, x3
adc x8, x12, x10
umulh x2, x1, x14
umulh x5, x1, x20
umulh x6, x1, x13
ldr x24, [x0, #72]
mul x3, x1, x11
adds x12, x17, x22
adcs x1, x9, x5
adcs x17, x7, x2
adc x22, x6, x10
adds x9, x25, x23
adc x5, x8, x10
mul x7, x24, x20
mul x2, x24, x11
mul x6, x24, x14
mul x25, x24, x13
extr x23, x5, x9, #63
and x8, x9, #0x7fffffffffffffff
mul x5, x23, x26
adds x9, x12, x2
adcs x23, x1, x7
adcs x12, x17, x6
adcs x2, x22, x25
adc x1, x10, x10
adds x7, x28, x5
adcs x17, x4, x15
adcs x6, x16, x21
adc x25, x8, x10
umulh x22, x24, x11
umulh x28, x24, x13
umulh x5, x24, x20
umulh x15, x24, x14
stp x7, x17, [x0, #160]
stp x6, x25, [x0, #176]
ldr x4, [x0, #80]
adds x21, x23, x22
adcs x16, x12, x5
adcs x8, x2, x15
adc x24, x1, x28
ldr x17, [x0, #88]
mul x7, x4, x11
mul x6, x4, x13
mul x25, x4, x14
mul x23, x4, x20
umulh x22, x4, x20
umulh x12, x4, x13
umulh x5, x4, x14
umulh x15, x4, x11
mul x2, x17, x14
umulh x28, x17, x14
mul x1, x17, x13
adds x4, x21, x7
adcs x14, x16, x23
adcs x21, x8, x25
adcs x7, x24, x6
adc x23, x10, x10
umulh x16, x17, x13
mul x25, x17, x20
umulh x8, x17, x20
mul x6, x17, x11
umulh x24, x17, x11
adds x13, x14, x15
adcs x20, x21, x22
adcs x17, x7, x5
adc x11, x23, x12
adds x15, x13, x6
adcs x14, x20, x25
adcs x22, x17, x2
adcs x21, x11, x1
adc x5, x10, x10
adds x7, x14, x24
adcs x12, x22, x8
adcs x23, x21, x28
adc x6, x5, x16
umulh x13, x27, x6
mul x25, x27, x12
mul x20, x27, x7
mul x2, x27, x23
mul x17, x27, x6
umulh x1, x27, x23
umulh x11, x27, x7
umulh x24, x27, x12
adds x14, x3, x20
adcs x8, x9, x25
adcs x22, x4, x2
adcs x21, x15, x17
adc x28, x13, x10
adds x5, x21, x1
adc x16, x28, x10
extr x6, x16, x5, #63
and x23, x5, #0x7fffffffffffffff
mul x7, x6, x26
adds x12, x14, x7
adcs x3, x8, x11
adcs x20, x22, x24
adc x9, x23, x10
stp x12, x3, [x0, #192]
stp x20, x9, [x0, #208]
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
.globl lab_sc_o3_21_15_0
lab_sc_o3_21_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
umulh x17, x9, x7
umulh x1, x9, x16
umulh x12, x9, x21
mul x14, x9, x16
mul x20, x9, x21
umulh x13, x7, x21
mul x4, x7, x16
mul x22, x7, x21
umulh x6, x7, x16
umulh x2, x16, x21
mul x11, x16, x21
mul x15, x9, x7
adds x8, x14, x17
adcs x28, x20, x1
adc x23, x12, x10
umulh x25, x9, x9
mul x24, x7, x7
mul x3, x9, x9
lsl x5, x15, #1
adds x17, x28, x4
adcs x14, x23, x22
adc x20, x13, x10
umulh x1, x7, x7
umulh x12, x16, x16
mul x9, x16, x16
extr x28, x8, x15, #63
adds x4, x14, x6
adcs x23, x20, x11
adc x22, x2, x10
umulh x13, x21, x21
mul x7, x21, x21
extr x16, x17, x8, #63
lsr x15, x22, #63
extr x6, x22, x23, #63
extr x14, x23, x4, #63
extr x11, x4, x17, #63
adds x20, x5, x25
adcs x2, x28, x24
adcs x21, x16, x1
adcs x8, x11, x9
adcs x22, x14, x12
adcs x23, x6, x7
adc x4, x15, x13
umulh x17, x27, x4
mul x5, x27, x8
mul x25, x27, x22
mul x28, x27, x23
mul x24, x27, x4
umulh x1, x27, x23
umulh x16, x27, x8
umulh x9, x27, x22
adds x11, x3, x5
adcs x14, x20, x25
adcs x12, x2, x28
adcs x7, x21, x24
adc x6, x17, x10
ldp x13, x15, [x0, #256]
ldp x4, x23, [x0, #272]
adds x8, x7, x1
adc x22, x6, x10
umulh x5, x13, x15
umulh x3, x13, x4
mul x20, x13, x4
mul x25, x13, x23
mul x28, x13, x15
extr x2, x22, x8, #63
umulh x24, x13, x23
and x21, x8, #0x7fffffffffffffff
mul x17, x15, x4
mul x7, x2, x26
mul x1, x15, x23
adds x6, x11, x7
adcs x22, x14, x16
adcs x8, x12, x9
adc x2, x21, x10
umulh x11, x15, x23
umulh x7, x15, x4
umulh x14, x4, x23
mul x16, x4, x23
stp x6, x22, [x0, #352]
adds x12, x20, x5
adcs x9, x25, x3
adc x21, x24, x10
stp x8, x2, [x0, #368]
umulh x6, x13, x13
mul x22, x15, x15
mul x20, x13, x13
lsl x5, x28, #1
adds x25, x9, x17
adcs x3, x21, x1
adc x24, x11, x10
umulh x8, x15, x15
umulh x2, x4, x4
mul x13, x4, x4
extr x9, x12, x28, #63
adds x17, x3, x7
adcs x21, x24, x16
adc x1, x14, x10
umulh x11, x23, x23
mul x15, x23, x23
extr x4, x25, x12, #63
lsr x28, x1, #63
extr x3, x1, x21, #63
extr x7, x21, x17, #63
extr x24, x17, x25, #63
adds x16, x5, x6
adcs x14, x9, x22
adcs x23, x4, x8
adcs x12, x24, x13
adcs x1, x7, x2
adcs x21, x3, x15
adc x25, x28, x11
umulh x17, x27, x25
mul x6, x27, x12
mul x5, x27, x1
mul x22, x27, x21
mul x9, x27, x25
umulh x8, x27, x21
umulh x4, x27, x12
umulh x24, x27, x1
adds x13, x20, x6
adcs x7, x16, x5
adcs x2, x14, x22
adcs x3, x23, x9
adc x15, x17, x10
ldp x28, x11, [x0, #224]
ldp x25, x21, [x0, #240]
ldr x12, [x0, #320]
adds x1, x3, x8
adc x6, x15, x10
mul x20, x12, x11
mul x5, x12, x25
mul x16, x12, x21
mul x14, x12, x28
extr x22, x6, x1, #63
umulh x23, x12, x28
and x9, x1, #0x7fffffffffffffff
umulh x17, x12, x11
mul x3, x22, x26
umulh x8, x12, x25
adds x15, x13, x3
adcs x6, x7, x4
adcs x1, x2, x24
adc x22, x9, x10
umulh x13, x12, x21
adds x3, x20, x23
adcs x4, x5, x17
adcs x7, x16, x8
adc x2, x13, x10
stp x15, x6, [x0, #384]
stp x1, x22, [x0, #400]
ldr x24, [x0, #328]
mul x9, x24, x28
mul x12, x24, x11
mul x20, x24, x25
mul x23, x24, x21
umulh x5, x24, x28
umulh x17, x24, x11
umulh x16, x24, x25
umulh x8, x24, x21
ldr x13, [x0, #336]
adds x15, x3, x9
adcs x6, x4, x12
adcs x1, x7, x20
adcs x22, x2, x23
adc x24, x10, x10
mul x3, x13, x28
mul x9, x13, x11
mul x4, x13, x25
mul x12, x13, x21
umulh x20, x13, x28
umulh x7, x13, x11
adds x23, x6, x5
adcs x2, x1, x17
adcs x6, x22, x16
adc x5, x24, x8
umulh x17, x13, x25
umulh x1, x13, x21
ldr x16, [x0, #344]
adds x22, x23, x3
adcs x8, x2, x9
adcs x24, x6, x4
adcs x13, x5, x12
adc x3, x10, x10
mul x23, x16, x28
umulh x9, x16, x28
mul x2, x16, x11
umulh x4, x16, x11
mul x6, x16, x25
mul x12, x16, x21
adds x5, x8, x20
adcs x28, x24, x7
adcs x11, x13, x17
adc x20, x3, x1
umulh x8, x16, x25
umulh x7, x16, x21
adds x24, x5, x23
adcs x17, x28, x2
adcs x13, x11, x6
adcs x3, x20, x12
adc x1, x10, x10
adds x25, x17, x9
adcs x16, x13, x4
adcs x21, x3, x8
adc x23, x1, x7
umulh x5, x27, x23
mul x2, x27, x25
mul x28, x27, x16
mul x6, x27, x21
mul x11, x27, x23
umulh x20, x27, x21
umulh x12, x27, x25
umulh x9, x27, x16
adds x17, x14, x2
adcs x13, x15, x28
adcs x4, x22, x6
adcs x3, x24, x11
adc x8, x5, x10
ldp x1, x7, [x0, #256]
ldp x23, x21, [x0, #272]
ldr x25, [x0, #288]
adds x16, x3, x20
adc x14, x8, x10
mul x2, x25, x7
mul x15, x25, x23
mul x28, x25, x21
mul x22, x25, x1
extr x6, x14, x16, #63
umulh x24, x25, x1
and x11, x16, #0x7fffffffffffffff
umulh x5, x25, x7
mul x20, x6, x26
umulh x3, x25, x23
adds x8, x17, x20
adcs x14, x13, x12
adcs x16, x4, x9
adc x6, x11, x10
umulh x17, x25, x21
adds x20, x2, x24
adcs x13, x15, x5
adcs x12, x28, x3
adc x9, x17, x10
stp x8, x14, [x0, #448]
stp x16, x6, [x0, #464]
ldr x4, [x0, #296]
mul x11, x4, x1
mul x25, x4, x7
mul x24, x4, x23
mul x2, x4, x21
umulh x15, x4, x1
umulh x5, x4, x7
umulh x28, x4, x23
umulh x3, x4, x21
ldr x17, [x0, #304]
adds x8, x20, x11
adcs x14, x13, x25
adcs x6, x12, x24
adcs x16, x9, x2
adc x4, x10, x10
mul x11, x17, x1
mul x20, x17, x7
mul x25, x17, x23
mul x13, x17, x21
umulh x12, x17, x1
umulh x24, x17, x7
adds x9, x14, x15
adcs x2, x6, x5
adcs x14, x16, x28
adc x15, x4, x3
umulh x6, x17, x23
umulh x5, x17, x21
ldr x16, [x0, #312]
adds x28, x9, x11
adcs x4, x2, x20
adcs x3, x14, x25
adcs x17, x15, x13
adc x9, x10, x10
mul x11, x16, x1
umulh x2, x16, x1
mul x20, x16, x7
umulh x14, x16, x7
mul x25, x16, x23
mul x13, x16, x21
adds x15, x4, x12
adcs x1, x3, x24
adcs x7, x17, x6
adc x4, x9, x5
umulh x12, x16, x23
umulh x3, x16, x21
adds x24, x15, x11
adcs x6, x1, x20
adcs x17, x7, x25
adcs x5, x4, x13
adc x9, x10, x10
adds x23, x6, x2
adcs x21, x17, x14
adcs x16, x5, x12
adc x15, x9, x3
umulh x11, x27, x15
mul x20, x27, x23
mul x1, x27, x21
mul x25, x27, x16
mul x7, x27, x15
umulh x13, x27, x16
umulh x4, x27, x23
umulh x2, x27, x21
adds x6, x22, x20
adcs x14, x8, x1
adcs x17, x28, x25
adcs x12, x24, x7
adc x5, x11, x10
ldp x3, x9, [x0, #352]
ldp x15, x16, [x0, #368]
ldp x23, x21, [x0, #384]
ldp x20, x22, [x0, #400]
adds x1, x12, x13
adc x8, x5, x10
subs x28, x3, x23
sbcs x25, x9, x21
sbcs x7, x15, x20
sbcs x24, x16, x22
csel x11, x10, x27, hs
extr x12, x8, x1, #63
and x13, x1, #0x7fffffffffffffff
mul x5, x12, x26
adds x23, x6, x5
adcs x3, x14, x4
adcs x21, x17, x2
adc x9, x13, x10
subs x15, x28, x11
sbcs x20, x25, x10
sbcs x16, x7, x10
sbc x22, x24, x10
stp x23, x3, [x0, #480]
stp x21, x9, [x0, #496]
ldp x8, x1, [x0, #384]
ldp x12, x6, [x0, #400]
stp x16, x22, [x0, #432]
stp x15, x20, [x0, #416]
ldr x5, [x0, #352]
ldr x14, [x0, #360]
umulh x4, x5, x8
umulh x17, x5, x1
umulh x2, x5, x12
umulh x13, x5, x6
mul x11, x5, x1
mul x28, x5, x12
mul x25, x5, x6
mul x7, x14, x8
mul x24, x14, x1
mul x23, x14, x12
mul x3, x5, x8
mul x21, x14, x6
umulh x9, x14, x8
umulh x16, x14, x1
adds x22, x11, x4
adcs x15, x28, x17
adcs x20, x25, x2
adc x5, x13, x10
umulh x4, x14, x12
umulh x11, x14, x6
ldr x17, [x0, #368]
adds x28, x22, x7
adcs x2, x15, x24
adcs x25, x20, x23
adcs x13, x5, x21
adc x14, x10, x10
mul x7, x17, x8
mul x22, x17, x1
mul x24, x17, x12
mul x15, x17, x6
umulh x23, x17, x8
umulh x20, x17, x1
adds x21, x2, x9
adcs x5, x25, x16
adcs x9, x13, x4
adc x2, x14, x11
umulh x16, x17, x12
umulh x25, x17, x6
ldr x13, [x0, #376]
adds x4, x21, x7
adcs x14, x5, x22
adcs x11, x9, x24
adcs x17, x2, x15
adc x7, x10, x10
mul x21, x13, x8
umulh x22, x13, x8
mul x5, x13, x1
umulh x9, x13, x1
mul x24, x13, x12
mul x2, x13, x6
adds x15, x14, x23
adcs x8, x11, x20
adcs x1, x17, x16
adc x14, x7, x25
umulh x23, x13, x12
umulh x11, x13, x6
adds x20, x15, x21
adcs x17, x8, x5
adcs x16, x1, x24
adcs x7, x14, x2
adc x25, x10, x10
adds x12, x17, x22
adcs x6, x16, x9
adcs x13, x7, x23
adc x15, x25, x11
umulh x21, x27, x15
mul x8, x27, x12
mul x5, x27, x6
mul x1, x27, x13
mul x24, x27, x15
umulh x2, x27, x13
umulh x14, x27, x12
umulh x17, x27, x6
adds x22, x3, x8
adcs x16, x28, x5
adcs x9, x4, x1
adcs x23, x20, x24
adc x7, x21, x10
ldp x11, x25, [x0, #432]
ldp x15, x13, [x0, #416]
movz x12, #56129, lsl #0
ldp x6, x3, [x0, #352]
ldp x8, x28, [x0, #368]
adds x5, x23, x2
adc x1, x7, x10
movk x12, #1, lsl #16
mul x4, x15, x12
extr x20, x1, x5, #63
mul x24, x13, x12
and x21, x5, #0x7fffffffffffffff
mul x23, x11, x12
mul x2, x20, x26
mul x7, x25, x12
adds x1, x22, x2
adcs x5, x16, x14
adcs x20, x9, x17
adc x22, x21, x10
umulh x2, x25, x12
adds x14, x6, x4
adcs x16, x3, x24
adcs x9, x8, x23
adcs x17, x28, x7
adc x21, x2, x10
stp x1, x5, [x0, #96]
stp x20, x22, [x0, #112]
umulh x25, x15, x12
umulh x6, x13, x12
umulh x4, x11, x12
ldr x3, [x0, #416]
adds x24, x17, x17
adc x23, x21, x21
mul x8, x23, x26
lsr x7, x24, #1
adds x28, x14, x8
adcs x2, x16, x25
adcs x1, x9, x6
adc x5, x7, x4
stp x28, x2, [x0, #128]
stp x1, x5, [x0, #144]
ldr x20, [x0, #424]
ldp x22, x15, [x0, #128]
ldp x13, x11, [x0, #144]
umulh x12, x3, x22
umulh x17, x3, x15
umulh x21, x3, x13
umulh x23, x3, x11
mul x24, x3, x15
mul x14, x3, x13
mul x8, x3, x11
mul x25, x20, x22
mul x16, x20, x15
mul x6, x20, x13
mul x9, x3, x22
mul x4, x20, x11
umulh x7, x20, x22
umulh x2, x20, x15
adds x28, x24, x12
adcs x1, x14, x17
adcs x5, x8, x21
adc x3, x23, x10
umulh x24, x20, x13
umulh x12, x20, x11
ldr x14, [x0, #432]
adds x17, x28, x25
adcs x8, x1, x16
adcs x21, x5, x6
adcs x23, x3, x4
adc x20, x10, x10
mul x28, x14, x22
mul x25, x14, x15
mul x1, x14, x13
mul x16, x14, x11
umulh x5, x14, x22
umulh x6, x14, x15
adds x4, x8, x7
adcs x3, x21, x2
adcs x8, x23, x24
adc x7, x20, x12
umulh x21, x14, x13
umulh x2, x14, x11
ldr x24, [x0, #440]
adds x23, x4, x28
adcs x12, x3, x25
adcs x20, x8, x1
adcs x14, x7, x16
adc x4, x10, x10
mul x28, x24, x22
umulh x25, x24, x22
mul x3, x24, x15
umulh x1, x24, x15
mul x8, x24, x13
mul x16, x24, x11
adds x7, x12, x5
adcs x22, x20, x6
adcs x15, x14, x21
adc x5, x4, x2
umulh x12, x24, x13
umulh x6, x24, x11
adds x20, x7, x28
adcs x21, x22, x3
adcs x14, x15, x8
adcs x2, x5, x16
adc x4, x10, x10
adds x13, x21, x25
adcs x24, x14, x1
adcs x11, x2, x12
adc x28, x4, x6
umulh x7, x27, x28
mul x3, x27, x13
mul x22, x27, x24
mul x8, x27, x11
mul x15, x27, x28
umulh x16, x27, x11
umulh x5, x27, x13
umulh x25, x27, x24
adds x21, x9, x3
adcs x1, x17, x22
adcs x14, x23, x8
adcs x2, x20, x15
adc x12, x7, x10
ldp x4, x6, [x0, #448]
ldp x28, x11, [x0, #464]
ldp x13, x24, [x0, #480]
ldp x9, x3, [x0, #496]
adds x17, x2, x16
adc x22, x12, x10
subs x23, x4, x13
sbcs x8, x6, x24
sbcs x15, x28, x9
sbcs x20, x11, x3
csel x7, x10, x27, hs
extr x16, x22, x17, #63
and x2, x17, #0x7fffffffffffffff
mul x12, x16, x26
adds x4, x21, x12
adcs x13, x1, x5
adcs x6, x14, x25
adc x24, x2, x10
subs x28, x23, x7
sbcs x9, x8, x10
sbcs x11, x15, x10
sbc x3, x20, x10
stp x4, x13, [x0, #128]
stp x6, x24, [x0, #144]
umulh x22, x28, x9
umulh x17, x28, x11
umulh x16, x28, x3
mul x21, x28, x11
mul x12, x28, x3
umulh x1, x9, x3
mul x5, x9, x11
mul x14, x9, x3
umulh x25, x9, x11
umulh x2, x11, x3
mul x23, x11, x3
mul x7, x28, x9
adds x8, x21, x22
adcs x15, x12, x17
adc x20, x16, x10
umulh x4, x28, x28
mul x13, x9, x9
mul x6, x28, x28
lsl x24, x7, #1
adds x21, x15, x5
adcs x22, x20, x14
adc x12, x1, x10
umulh x17, x9, x9
umulh x16, x11, x11
mul x28, x11, x11
extr x15, x8, x7, #63
adds x5, x22, x25
adcs x14, x12, x23
adc x20, x2, x10
umulh x1, x3, x3
mul x9, x3, x3
extr x11, x21, x8, #63
lsr x7, x20, #63
extr x22, x20, x14, #63
extr x25, x14, x5, #63
extr x12, x5, x21, #63
adds x23, x24, x4
adcs x2, x15, x13
adcs x3, x11, x17
adcs x8, x12, x28
adcs x20, x25, x16
adcs x14, x22, x9
adc x21, x7, x1
umulh x5, x27, x21
mul x24, x27, x8
mul x4, x27, x20
mul x15, x27, x14
mul x13, x27, x21
umulh x17, x27, x14
umulh x11, x27, x8
umulh x12, x27, x20
adds x28, x6, x24
adcs x25, x23, x4
adcs x16, x2, x15
adcs x9, x3, x13
adc x22, x5, x10
ldp x1, x7, [x0, #448]
ldp x21, x14, [x0, #464]
ldp x8, x20, [x0, #480]
ldp x24, x6, [x0, #496]
adds x23, x9, x17
adc x4, x22, x10
adds x15, x1, x8
adcs x2, x7, x20
adcs x13, x21, x24
adcs x3, x14, x6
csel x5, x27, x10, hs
extr x17, x4, x23, #63
and x9, x23, #0x7fffffffffffffff
mul x22, x17, x26
adds x1, x28, x22
adcs x8, x25, x11
adcs x7, x16, x12
adc x20, x9, x10
adds x24, x15, x5
adcs x21, x2, x10
adc x6, x13, x10
stp x1, x8, [x0, #192]
stp x7, x20, [x0, #208]
umulh x14, x24, x21
umulh x4, x24, x6
umulh x23, x24, x3
mul x17, x24, x6
mul x28, x24, x3
umulh x22, x21, x3
mul x11, x21, x6
mul x25, x21, x3
umulh x12, x21, x6
umulh x16, x6, x3
mul x9, x6, x3
mul x15, x24, x21
adds x5, x17, x14
adcs x2, x28, x4
adc x13, x23, x10
umulh x1, x24, x24
mul x8, x21, x21
mul x7, x24, x24
lsl x20, x15, #1
adds x17, x2, x11
adcs x14, x13, x25
adc x28, x22, x10
umulh x4, x21, x21
umulh x23, x6, x6
mul x24, x6, x6
extr x11, x5, x15, #63
adds x2, x14, x12
adcs x13, x28, x9
adc x25, x16, x10
umulh x22, x3, x3
mul x21, x3, x3
extr x6, x17, x5, #63
lsr x15, x25, #63
extr x14, x25, x13, #63
extr x12, x13, x2, #63
extr x28, x2, x17, #63
adds x9, x20, x1
adcs x16, x11, x8
adcs x3, x6, x4
adcs x5, x28, x24
adcs x25, x12, x23
adcs x13, x14, x21
adc x17, x15, x22
umulh x2, x27, x17
mul x20, x27, x5
mul x1, x27, x25
mul x8, x27, x13
mul x11, x27, x17
umulh x4, x27, x13
umulh x6, x27, x5
umulh x28, x27, x25
adds x24, x7, x20
adcs x12, x9, x1
adcs x23, x16, x8
adcs x14, x3, x11
adc x21, x2, x10
ldp x22, x15, [x0, #192]
ldp x17, x13, [x0, #208]
ldr x5, [x0, #64]
adds x25, x14, x4
adc x20, x21, x10
mul x7, x5, x15
mul x9, x5, x17
mul x1, x5, x13
mul x8, x5, x22
extr x16, x20, x25, #63
umulh x3, x5, x22
and x11, x25, #0x7fffffffffffffff
umulh x2, x5, x15
mul x14, x16, x26
umulh x4, x5, x17
adds x21, x24, x14
adcs x20, x12, x6
adcs x25, x23, x28
adc x16, x11, x10
umulh x24, x5, x13
adds x14, x7, x3
adcs x6, x9, x2
adcs x12, x1, x4
adc x28, x24, x10
stp x21, x20, [x0, #160]
stp x25, x16, [x0, #176]
ldr x23, [x0, #72]
mul x11, x23, x22
mul x5, x23, x15
mul x7, x23, x17
mul x3, x23, x13
umulh x9, x23, x22
umulh x2, x23, x15
umulh x1, x23, x17
umulh x4, x23, x13
ldr x24, [x0, #80]
adds x20, x14, x11
adcs x21, x6, x5
adcs x25, x12, x7
adcs x16, x28, x3
adc x23, x10, x10
mul x14, x24, x22
mul x11, x24, x15
mul x6, x24, x17
mul x5, x24, x13
umulh x12, x24, x22
umulh x7, x24, x15
adds x3, x21, x9
adcs x28, x25, x2
adcs x21, x16, x1
adc x9, x23, x4
umulh x25, x24, x17
umulh x2, x24, x13
ldr x1, [x0, #88]
adds x16, x3, x14
adcs x4, x28, x11
adcs x23, x21, x6
adcs x24, x9, x5
adc x3, x10, x10
mul x14, x1, x22
umulh x11, x1, x22
mul x28, x1, x15
umulh x6, x1, x15
mul x21, x1, x17
mul x5, x1, x13
adds x9, x4, x12
adcs x22, x23, x7
adcs x15, x24, x25
adc x12, x3, x2
umulh x4, x1, x17
umulh x7, x1, x13
adds x23, x9, x14
adcs x25, x22, x28
adcs x24, x15, x21
adcs x2, x12, x5
adc x3, x10, x10
adds x17, x25, x11
adcs x1, x24, x6
adcs x13, x2, x4
adc x14, x3, x7
umulh x9, x27, x14
mul x28, x27, x17
mul x22, x27, x1
mul x21, x27, x13
mul x15, x27, x14
umulh x5, x27, x13
umulh x12, x27, x17
umulh x11, x27, x1
adds x25, x8, x28
adcs x6, x20, x22
adcs x24, x16, x21
adcs x2, x23, x15
adc x4, x9, x10
adds x3, x2, x5
adc x7, x4, x10
extr x14, x7, x3, #63
and x13, x3, #0x7fffffffffffffff
mul x17, x14, x26
adds x1, x25, x17
adcs x8, x6, x12
adcs x28, x24, x11
adc x20, x13, x10
stp x1, x8, [x0, #192]
stp x28, x20, [x0, #208]
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
.globl lab_sc_o3_21_15_1
lab_sc_o3_21_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
umulh x3, x6, x16
umulh x7, x6, x23
umulh x11, x6, x15
mul x4, x6, x15
mul x8, x6, x23
umulh x2, x16, x15
mul x13, x23, x15
umulh x17, x16, x23
mul x5, x16, x15
umulh x1, x23, x15
mul x9, x16, x23
mul x12, x6, x16
adds x21, x8, x3
adcs x20, x4, x7
adc x22, x11, x10
umulh x28, x6, x6
mul x24, x16, x16
mul x25, x6, x6
lsl x14, x12, #1
adds x3, x20, x9
adcs x8, x22, x5
adc x4, x2, x10
umulh x7, x23, x23
mul x11, x23, x23
umulh x6, x16, x16
extr x20, x21, x12, #63
adds x9, x8, x17
adcs x22, x4, x13
adc x5, x1, x10
umulh x2, x15, x15
extr x23, x3, x21, #63
mul x16, x15, x15
lsr x12, x5, #63
extr x17, x5, x22, #63
extr x8, x22, x9, #63
extr x13, x9, x3, #63
adds x4, x14, x28
adcs x1, x20, x24
adcs x21, x23, x6
adcs x15, x13, x11
adcs x5, x8, x7
adcs x22, x17, x16
adc x9, x12, x2
umulh x3, x27, x9
mul x14, x27, x15
mul x28, x27, x5
mul x20, x27, x9
mul x24, x27, x22
umulh x6, x27, x22
umulh x23, x27, x5
umulh x11, x27, x15
adds x13, x25, x14
adcs x8, x4, x28
adcs x7, x1, x24
adcs x16, x21, x20
adc x17, x3, x10
ldp x2, x12, [x0, #272]
ldp x9, x22, [x0, #256]
adds x5, x16, x6
adc x15, x17, x10
umulh x14, x9, x2
mul x25, x9, x2
mul x4, x9, x12
umulh x28, x9, x22
mul x24, x9, x22
extr x1, x15, x5, #63
umulh x20, x9, x12
and x21, x5, #0x7fffffffffffffff
mul x3, x22, x2
mul x16, x1, x26
mul x6, x22, x12
adds x17, x13, x16
adcs x15, x8, x11
adcs x5, x7, x23
adc x1, x21, x10
umulh x13, x22, x12
umulh x16, x22, x2
umulh x8, x2, x12
mul x11, x2, x12
stp x17, x15, [x0, #352]
adds x7, x25, x28
adcs x23, x4, x14
adc x21, x20, x10
stp x5, x1, [x0, #368]
umulh x17, x9, x9
mul x15, x22, x22
mul x25, x9, x9
lsl x28, x24, #1
adds x4, x23, x3
adcs x14, x21, x6
adc x20, x13, x10
umulh x5, x22, x22
mul x1, x2, x2
extr x9, x7, x24, #63
umulh x23, x2, x2
adds x3, x14, x16
adcs x21, x20, x11
adc x6, x8, x10
extr x13, x4, x7, #63
umulh x22, x12, x12
mul x24, x12, x12
lsr x2, x6, #63
extr x14, x6, x21, #63
extr x16, x21, x3, #63
extr x20, x3, x4, #63
adds x11, x28, x17
adcs x8, x9, x15
adcs x7, x13, x5
adcs x12, x20, x1
adcs x6, x16, x23
adcs x21, x14, x24
adc x4, x2, x22
umulh x3, x27, x4
mul x17, x27, x12
mul x28, x27, x4
mul x15, x27, x6
mul x9, x27, x21
umulh x5, x27, x21
umulh x13, x27, x6
umulh x20, x27, x12
adds x1, x25, x17
adcs x16, x11, x15
adcs x23, x8, x9
adcs x14, x7, x28
adc x24, x3, x10
ldp x2, x22, [x0, #240]
ldr x4, [x0, #320]
ldp x21, x6, [x0, #224]
adds x12, x14, x5
adc x17, x24, x10
mul x25, x4, x2
mul x15, x4, x6
mul x11, x4, x22
mul x8, x4, x21
extr x9, x17, x12, #63
umulh x7, x4, x21
and x28, x12, #0x7fffffffffffffff
umulh x3, x4, x6
mul x14, x9, x26
umulh x5, x4, x2
adds x24, x1, x14
adcs x17, x16, x20
adcs x12, x23, x13
adc x9, x28, x10
umulh x1, x4, x22
adds x14, x15, x7
adcs x20, x25, x3
adcs x16, x11, x5
adc x23, x1, x10
stp x24, x17, [x0, #384]
stp x12, x9, [x0, #400]
ldr x13, [x0, #328]
mul x28, x13, x21
mul x4, x13, x22
mul x15, x13, x6
mul x7, x13, x2
umulh x25, x13, x22
ldr x3, [x0, #336]
umulh x11, x13, x2
umulh x5, x13, x21
umulh x1, x13, x6
adds x24, x14, x28
adcs x17, x20, x15
adcs x12, x16, x7
adcs x9, x23, x4
adc x13, x10, x10
mul x14, x3, x21
mul x28, x3, x22
mul x20, x3, x6
mul x15, x3, x2
umulh x7, x3, x21
umulh x16, x3, x6
adds x4, x17, x5
adcs x23, x12, x1
adcs x17, x9, x11
adc x5, x13, x25
umulh x1, x3, x2
umulh x12, x3, x22
ldr x11, [x0, #344]
adds x9, x4, x14
adcs x25, x23, x20
adcs x13, x17, x15
adcs x3, x5, x28
adc x14, x10, x10
mul x4, x11, x21
umulh x20, x11, x21
mul x23, x11, x22
umulh x15, x11, x6
mul x17, x11, x6
mul x28, x11, x2
adds x5, x25, x7
adcs x21, x13, x16
adcs x6, x3, x1
adc x7, x14, x12
umulh x25, x11, x22
umulh x16, x11, x2
adds x13, x5, x4
adcs x1, x21, x17
adcs x3, x6, x28
adcs x14, x7, x23
adc x12, x10, x10
adds x22, x1, x20
adcs x11, x3, x15
adcs x2, x14, x16
adc x4, x12, x25
umulh x5, x27, x4
mul x17, x27, x4
umulh x21, x27, x2
mul x28, x27, x22
mul x6, x27, x11
mul x7, x27, x2
umulh x23, x27, x11
umulh x20, x27, x22
adds x1, x8, x28
adcs x3, x24, x6
adcs x15, x9, x7
adcs x14, x13, x17
adc x16, x5, x10
ldp x12, x25, [x0, #256]
ldp x4, x2, [x0, #272]
ldr x11, [x0, #288]
adds x22, x14, x21
adc x8, x16, x10
mul x28, x11, x25
mul x24, x11, x2
mul x6, x11, x4
mul x9, x11, x12
extr x7, x8, x22, #63
umulh x13, x11, x12
and x17, x22, #0x7fffffffffffffff
umulh x5, x11, x25
mul x21, x7, x26
umulh x14, x11, x4
adds x16, x1, x21
adcs x8, x3, x20
adcs x22, x15, x23
adc x7, x17, x10
umulh x1, x11, x2
adds x21, x28, x13
adcs x3, x6, x5
adcs x20, x24, x14
adc x23, x1, x10
stp x16, x8, [x0, #448]
stp x22, x7, [x0, #464]
ldr x15, [x0, #296]
mul x17, x15, x12
mul x11, x15, x25
umulh x13, x15, x25
umulh x28, x15, x2
mul x6, x15, x4
umulh x5, x15, x12
mul x24, x15, x2
umulh x14, x15, x4
ldr x1, [x0, #304]
adds x16, x21, x17
adcs x8, x3, x11
adcs x7, x20, x6
adcs x22, x23, x24
adc x15, x10, x10
mul x17, x1, x12
mul x21, x1, x4
umulh x11, x1, x12
mul x3, x1, x25
mul x20, x1, x2
umulh x6, x1, x25
adds x23, x8, x5
adcs x24, x7, x13
adcs x8, x22, x14
adc x5, x15, x28
umulh x7, x1, x4
umulh x13, x1, x2
ldr x22, [x0, #312]
adds x14, x23, x17
adcs x15, x24, x3
adcs x28, x8, x21
adcs x1, x5, x20
adc x23, x10, x10
mul x17, x22, x12
umulh x24, x22, x12
mul x3, x22, x4
mul x8, x22, x2
mul x21, x22, x25
umulh x20, x22, x25
adds x5, x15, x11
adcs x12, x28, x6
adcs x25, x1, x7
adc x15, x23, x13
umulh x11, x22, x4
umulh x28, x22, x2
adds x6, x5, x17
adcs x7, x12, x21
adcs x1, x25, x3
adcs x13, x15, x8
adc x23, x10, x10
adds x4, x7, x24
adcs x2, x1, x20
adcs x22, x13, x11
adc x5, x23, x28
umulh x17, x27, x5
mul x21, x27, x2
mul x12, x27, x5
mul x3, x27, x22
umulh x25, x27, x22
mul x8, x27, x4
umulh x15, x27, x2
umulh x24, x27, x4
adds x7, x9, x8
adcs x20, x16, x21
adcs x1, x14, x3
adcs x11, x6, x12
adc x13, x17, x10
ldp x28, x23, [x0, #384]
ldp x5, x22, [x0, #368]
ldp x2, x4, [x0, #352]
ldp x8, x9, [x0, #400]
adds x21, x11, x25
adc x16, x13, x10
subs x14, x2, x28
sbcs x3, x4, x23
sbcs x12, x5, x8
sbcs x6, x22, x9
csel x17, x10, x27, hs
extr x11, x16, x21, #63
and x25, x21, #0x7fffffffffffffff
mul x13, x11, x26
adds x28, x7, x13
adcs x2, x20, x24
adcs x23, x1, x15
adc x4, x25, x10
subs x5, x14, x17
sbcs x8, x3, x10
sbcs x22, x12, x10
sbc x9, x6, x10
stp x28, x2, [x0, #480]
stp x23, x4, [x0, #496]
ldr x16, [x0, #352]
ldp x21, x11, [x0, #400]
stp x22, x9, [x0, #432]
stp x5, x8, [x0, #416]
ldr x7, [x0, #360]
ldp x13, x20, [x0, #384]
umulh x24, x16, x21
umulh x1, x16, x11
mul x15, x16, x11
mul x25, x16, x21
umulh x17, x16, x13
umulh x14, x16, x20
mul x3, x16, x20
mul x12, x7, x21
mul x6, x7, x13
mul x28, x7, x20
mul x2, x16, x13
mul x23, x7, x11
umulh x4, x7, x13
umulh x22, x7, x20
adds x9, x3, x17
adcs x5, x25, x14
adcs x8, x15, x24
adc x16, x1, x10
umulh x17, x7, x21
umulh x3, x7, x11
ldr x14, [x0, #368]
adds x25, x9, x6
adcs x24, x5, x28
adcs x15, x8, x12
adcs x1, x16, x23
adc x7, x10, x10
mul x6, x14, x13
mul x9, x14, x11
mul x28, x14, x21
mul x5, x14, x20
umulh x12, x14, x20
umulh x8, x14, x13
adds x23, x24, x4
adcs x16, x15, x22
adcs x4, x1, x17
adc x24, x7, x3
umulh x22, x14, x11
umulh x15, x14, x21
ldr x1, [x0, #376]
adds x17, x23, x6
adcs x7, x16, x5
adcs x3, x4, x28
adcs x14, x24, x9
adc x6, x10, x10
mul x23, x1, x13
umulh x5, x1, x13
mul x16, x1, x21
mul x4, x1, x11
mul x28, x1, x20
umulh x24, x1, x20
adds x9, x7, x8
adcs x13, x3, x12
adcs x20, x14, x15
adc x7, x6, x22
umulh x8, x1, x21
umulh x3, x1, x11
adds x12, x9, x23
adcs x14, x13, x28
adcs x15, x20, x16
adcs x6, x7, x4
adc x22, x10, x10
adds x21, x14, x5
adcs x11, x15, x24
adcs x1, x6, x8
adc x9, x22, x3
umulh x23, x27, x9
mul x13, x27, x11
mul x28, x27, x21
mul x20, x27, x1
umulh x16, x27, x1
mul x4, x27, x9
umulh x7, x27, x21
umulh x14, x27, x11
adds x5, x2, x28
adcs x15, x25, x13
adcs x24, x17, x20
adcs x8, x12, x4
adc x6, x23, x10
movz x3, #56129, lsl #0
ldp x22, x1, [x0, #368]
ldp x9, x21, [x0, #432]
ldp x11, x2, [x0, #416]
ldp x28, x25, [x0, #352]
adds x13, x8, x16
adc x20, x6, x10
movk x3, #1, lsl #16
mul x17, x11, x3
extr x12, x20, x13, #63
mul x4, x2, x3
and x23, x13, #0x7fffffffffffffff
mul x8, x9, x3
mul x16, x12, x26
mul x6, x21, x3
adds x20, x5, x16
adcs x13, x15, x7
adcs x12, x24, x14
adc x5, x23, x10
umulh x16, x21, x3
adds x7, x28, x17
adcs x15, x25, x4
adcs x24, x22, x8
adcs x14, x1, x6
adc x23, x16, x10
stp x12, x5, [x0, #112]
stp x20, x13, [x0, #96]
umulh x21, x2, x3
umulh x28, x9, x3
umulh x17, x11, x3
ldr x25, [x0, #416]
adds x4, x14, x14
adc x8, x23, x23
mul x22, x8, x26
lsr x6, x4, #1
adds x1, x7, x22
adcs x16, x15, x17
adcs x12, x24, x21
adc x5, x6, x28
stp x1, x16, [x0, #128]
stp x12, x5, [x0, #144]
ldr x20, [x0, #424]
ldp x13, x2, [x0, #128]
ldp x9, x11, [x0, #144]
umulh x3, x25, x13
umulh x14, x25, x9
umulh x23, x25, x11
umulh x8, x25, x2
mul x4, x25, x2
mul x7, x25, x11
mul x22, x25, x9
mul x17, x20, x2
mul x15, x20, x13
mul x21, x20, x9
mul x24, x25, x13
mul x28, x20, x11
umulh x6, x20, x13
umulh x16, x20, x2
adds x1, x4, x3
adcs x12, x22, x8
adcs x5, x7, x14
adc x25, x23, x10
umulh x4, x20, x9
umulh x3, x20, x11
ldr x22, [x0, #432]
adds x8, x1, x15
adcs x7, x12, x17
adcs x14, x5, x21
adcs x23, x25, x28
adc x20, x10, x10
mul x1, x22, x13
mul x15, x22, x2
mul x12, x22, x9
mul x17, x22, x11
umulh x5, x22, x2
umulh x21, x22, x13
adds x28, x7, x6
adcs x25, x14, x16
adcs x7, x23, x4
adc x6, x20, x3
umulh x14, x22, x11
umulh x16, x22, x9
ldr x4, [x0, #440]
adds x23, x28, x1
adcs x3, x25, x15
adcs x20, x7, x12
adcs x22, x6, x17
adc x28, x10, x10
mul x1, x4, x13
umulh x15, x4, x13
mul x25, x4, x11
mul x12, x4, x9
mul x7, x4, x2
umulh x17, x4, x2
adds x6, x3, x21
adcs x13, x20, x5
adcs x2, x22, x16
adc x21, x28, x14
umulh x3, x4, x9
umulh x5, x4, x11
adds x20, x6, x1
adcs x16, x13, x7
adcs x22, x2, x12
adcs x14, x21, x25
adc x28, x10, x10
adds x9, x16, x15
adcs x4, x22, x17
adcs x11, x14, x3
adc x1, x28, x5
umulh x6, x27, x1
mul x7, x27, x1
mul x13, x27, x4
mul x12, x27, x9
mul x2, x27, x11
umulh x25, x27, x11
umulh x21, x27, x9
umulh x15, x27, x4
adds x16, x24, x12
adcs x17, x8, x13
adcs x22, x23, x2
adcs x14, x20, x7
adc x3, x6, x10
ldp x28, x5, [x0, #480]
ldp x1, x11, [x0, #464]
ldp x9, x4, [x0, #496]
ldp x24, x12, [x0, #448]
adds x8, x14, x25
adc x13, x3, x10
subs x23, x24, x28
sbcs x2, x12, x5
sbcs x7, x1, x9
sbcs x20, x11, x4
csel x6, x10, x27, hs
and x25, x8, #0x7fffffffffffffff
extr x14, x13, x8, #63
mul x3, x14, x26
adds x24, x16, x3
adcs x28, x17, x21
adcs x12, x22, x15
adc x5, x25, x10
subs x1, x23, x6
sbcs x9, x2, x10
sbcs x11, x7, x10
sbc x4, x20, x10
stp x24, x28, [x0, #128]
stp x12, x5, [x0, #144]
umulh x13, x1, x9
umulh x8, x1, x4
mul x14, x1, x4
umulh x16, x1, x11
mul x3, x1, x11
umulh x17, x9, x4
mul x21, x9, x4
umulh x22, x9, x11
mul x15, x9, x11
mul x25, x11, x4
umulh x23, x11, x4
mul x6, x1, x9
adds x2, x3, x13
adcs x7, x14, x16
adc x20, x8, x10
mul x24, x9, x9
umulh x28, x1, x1
mul x12, x1, x1
lsl x5, x6, #1
adds x3, x7, x15
adcs x13, x20, x21
adc x14, x17, x10
umulh x16, x9, x9
mul x8, x11, x11
extr x1, x2, x6, #63
umulh x7, x11, x11
adds x15, x13, x22
adcs x21, x14, x25
adc x20, x23, x10
umulh x17, x4, x4
mul x9, x4, x4
extr x6, x3, x2, #63
lsr x11, x20, #63
extr x13, x15, x3, #63
extr x22, x21, x15, #63
extr x14, x20, x21, #63
adds x25, x5, x28
adcs x23, x1, x24
adcs x4, x6, x16
adcs x2, x13, x8
adcs x3, x22, x7
adcs x15, x14, x9
adc x21, x11, x17
umulh x20, x27, x21
mul x5, x27, x3
mul x28, x27, x2
mul x1, x27, x21
mul x24, x27, x15
umulh x16, x27, x15
umulh x6, x27, x3
umulh x13, x27, x2
adds x8, x12, x28
adcs x22, x25, x5
adcs x7, x23, x24
adcs x9, x4, x1
adc x14, x20, x10
ldp x17, x11, [x0, #448]
ldp x21, x15, [x0, #464]
ldp x3, x2, [x0, #496]
ldp x28, x12, [x0, #480]
adds x25, x9, x16
adc x5, x14, x10
adds x24, x17, x28
adcs x23, x11, x12
adcs x1, x21, x3
adcs x4, x15, x2
csel x20, x27, x10, hs
extr x16, x5, x25, #63
and x9, x25, #0x7fffffffffffffff
mul x14, x16, x26
adds x17, x8, x14
adcs x28, x22, x13
adcs x11, x7, x6
adc x12, x9, x10
adds x3, x24, x20
adcs x21, x23, x10
adc x2, x1, x10
stp x17, x28, [x0, #192]
stp x11, x12, [x0, #208]
umulh x15, x3, x2
umulh x5, x3, x4
mul x25, x21, x2
mul x16, x3, x4
umulh x8, x21, x4
mul x14, x3, x2
umulh x13, x3, x21
umulh x22, x2, x4
mul x6, x21, x4
umulh x7, x21, x2
mul x9, x2, x4
mul x24, x3, x21
adds x20, x14, x13
adcs x23, x16, x15
adc x1, x5, x10
lsl x17, x24, #1
umulh x28, x3, x3
mul x11, x3, x3
mul x12, x21, x21
adds x14, x23, x25
adcs x13, x1, x6
adc x16, x8, x10
umulh x15, x21, x21
umulh x5, x2, x2
extr x3, x20, x24, #63
mul x25, x2, x2
adds x23, x13, x7
adcs x1, x16, x9
adc x6, x22, x10
umulh x8, x4, x4
extr x21, x14, x20, #63
mul x24, x4, x4
lsr x2, x6, #63
extr x13, x6, x1, #63
extr x7, x1, x23, #63
extr x16, x23, x14, #63
adds x9, x17, x28
adcs x22, x3, x12
adcs x20, x21, x15
adcs x4, x16, x25
adcs x6, x7, x5
adcs x1, x13, x24
adc x14, x2, x8
umulh x23, x27, x14
mul x17, x27, x4
mul x28, x27, x14
mul x12, x27, x1
mul x3, x27, x6
umulh x15, x27, x1
umulh x21, x27, x6
umulh x16, x27, x4
adds x25, x11, x17
adcs x7, x9, x3
adcs x5, x22, x12
adcs x13, x20, x28
adc x24, x23, x10
ldp x8, x2, [x0, #192]
ldp x14, x1, [x0, #208]
ldr x6, [x0, #64]
adds x4, x13, x15
adc x17, x24, x10
mul x11, x6, x2
mul x9, x6, x1
mul x3, x6, x14
mul x12, x6, x8
extr x22, x17, x4, #63
umulh x20, x6, x8
and x28, x4, #0x7fffffffffffffff
umulh x23, x6, x2
mul x13, x22, x26
umulh x15, x6, x14
adds x24, x25, x13
adcs x17, x7, x16
adcs x4, x5, x21
adc x22, x28, x10
umulh x25, x6, x1
adds x13, x11, x20
adcs x16, x3, x23
adcs x7, x9, x15
adc x21, x25, x10
stp x24, x17, [x0, #160]
stp x4, x22, [x0, #176]
ldr x5, [x0, #72]
mul x28, x5, x8
mul x6, x5, x2
mul x11, x5, x14
mul x20, x5, x1
umulh x3, x5, x8
umulh x23, x5, x1
umulh x9, x5, x2
umulh x15, x5, x14
ldr x25, [x0, #80]
adds x17, x13, x28
adcs x24, x16, x6
adcs x4, x7, x11
adcs x22, x21, x20
adc x5, x10, x10
mul x13, x25, x8
mul x28, x25, x1
mul x16, x25, x14
mul x6, x25, x2
umulh x7, x25, x2
umulh x11, x25, x8
adds x20, x24, x3
adcs x21, x4, x9
adcs x24, x22, x15
adc x3, x5, x23
umulh x4, x25, x1
umulh x9, x25, x14
ldr x15, [x0, #88]
adds x22, x20, x13
adcs x23, x21, x6
adcs x5, x24, x16
adcs x25, x3, x28
adc x20, x10, x10
mul x13, x15, x8
umulh x6, x15, x8
mul x21, x15, x14
mul x16, x15, x1
mul x24, x15, x2
umulh x28, x15, x2
adds x3, x23, x11
adcs x8, x5, x7
adcs x2, x25, x9
adc x11, x20, x4
umulh x23, x15, x14
umulh x7, x15, x1
adds x5, x3, x13
adcs x9, x8, x24
adcs x25, x2, x21
adcs x4, x11, x16
adc x20, x10, x10
adds x14, x9, x6
adcs x15, x25, x28
adcs x1, x4, x23
adc x13, x20, x7
umulh x3, x27, x13
mul x24, x27, x15
mul x8, x27, x14
mul x21, x27, x1
mul x2, x27, x13
umulh x16, x27, x1
umulh x11, x27, x14
umulh x6, x27, x15
adds x9, x12, x8
adcs x28, x17, x24
adcs x25, x22, x21
adcs x4, x5, x2
adc x23, x3, x10
adds x20, x4, x16
adc x7, x23, x10
extr x13, x7, x20, #63
and x1, x20, #0x7fffffffffffffff
mul x14, x13, x26
adds x15, x9, x14
adcs x12, x28, x11
adcs x8, x25, x6
adc x17, x1, x10
stp x15, x12, [x0, #192]
stp x8, x17, [x0, #208]
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
.globl lab_sc_o3_22_30_0
lab_sc_o3_22_30_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
ldp x11, x24, [x0, #192]
ldp x5, x28, [x0, #208]
subs x6, x17, x21
sbcs x15, x12, x10
sbcs x8, x20, x10
sbc x23, x13, x10
adds x9, x14, x4
adcs x21, x22, x10
adc x17, x2, x10
subs x12, x25, x11
sbcs x20, x7, x24
sbcs x13, x16, x5
sbcs x4, x1, x28
csel x14, x10, x27, hs
adds x22, x25, x11
adcs x2, x7, x24
adcs x11, x16, x5
adcs x25, x1, x28
csel x24, x27, x10, hs
stp x9, x21, [x0, #224]
stp x17, x3, [x0, #240]
stp x6, x15, [x0, #256]
stp x8, x23, [x0, #272]
subs x7, x12, x14
sbcs x16, x20, x10
sbcs x5, x13, x10
sbc x28, x4, x10
adds x1, x22, x24
adcs x9, x2, x10
adc x21, x11, x10
ldp x17, x3, [x0, #224]
ldp x6, x15, [x0, #240]
stp x7, x16, [x0, #320]
stp x1, x9, [x0, #288]
stp x21, x25, [x0, #304]
stp x5, x28, [x0, #336]
umulh x8, x17, x3
umulh x23, x17, x6
umulh x12, x17, x15
mul x14, x17, x6
mul x20, x17, x15
umulh x13, x3, x15
mul x4, x3, x6
mul x22, x3, x15
umulh x24, x3, x6
umulh x2, x6, x15
mul x11, x6, x15
mul x7, x17, x3
umulh x16, x17, x17
umulh x1, x3, x3
adds x9, x14, x8
adcs x21, x20, x23
adc x25, x12, x10
umulh x5, x6, x6
mul x28, x3, x3
mul x8, x6, x6
umulh x14, x15, x15
mul x20, x15, x15
mul x23, x17, x17
lsl x12, x7, #1
adds x3, x21, x4
adcs x6, x25, x22
adc x15, x13, x10
extr x17, x9, x7, #63
adds x21, x6, x24
adcs x4, x15, x11
adc x25, x2, x10
extr x22, x3, x9, #63
lsr x13, x25, #63
extr x7, x25, x4, #63
extr x24, x4, x21, #63
extr x6, x21, x3, #63
adds x11, x12, x16
adcs x15, x17, x28
adcs x2, x22, x1
adcs x9, x6, x8
adcs x25, x24, x5
adcs x4, x7, x20
adc x21, x13, x14
ldp x3, x12, [x0, #256]
ldp x16, x17, [x0, #272]
umulh x28, x3, x12
umulh x1, x3, x16
mul x22, x3, x16
mul x8, x3, x17
mul x6, x3, x12
umulh x24, x27, x21
mul x5, x27, x21
mul x20, x27, x9
umulh x7, x3, x17
umulh x14, x27, x9
mul x13, x27, x25
mul x21, x12, x16
umulh x9, x27, x25
mul x25, x27, x4
umulh x4, x27, x4
adds x20, x23, x20
adcs x23, x11, x13
adcs x11, x15, x25
adcs x13, x2, x5
adc x25, x24, x10
adds x15, x22, x28
adcs x5, x8, x1
adc x2, x7, x10
umulh x24, x12, x17
mul x22, x12, x17
umulh x28, x12, x16
umulh x8, x16, x17
mul x1, x16, x17
adds x7, x5, x21
adcs x5, x2, x22
adc x21, x24, x10
adds x2, x13, x4
adc x22, x25, x10
extr x24, x22, x2, #63
adds x13, x5, x28
adcs x4, x21, x1
adc x25, x8, x10
mul x22, x24, x26
and x5, x2, #0x7fffffffffffffff
adds x28, x20, x22
adcs x21, x23, x14
adcs x1, x11, x9
adc x8, x5, x10
lsr x24, x25, #63
extr x2, x25, x4, #63
extr x20, x4, x13, #63
extr x22, x13, x7, #63
extr x23, x7, x15, #63
extr x14, x15, x6, #63
stp x28, x21, [x0, #352]
lsl x11, x6, #1
stp x1, x8, [x0, #368]
umulh x9, x3, x3
umulh x5, x12, x12
umulh x25, x16, x16
umulh x4, x17, x17
mul x13, x12, x12
mul x7, x16, x16
mul x15, x17, x17
mul x28, x3, x3
adds x21, x11, x9
adcs x6, x14, x13
adcs x1, x23, x5
adcs x8, x22, x7
adcs x12, x20, x25
adcs x16, x2, x15
adc x17, x24, x4
ldp x3, x9, [x0, #224]
ldp x11, x13, [x0, #240]
ldr x14, [x0, #320]
mul x5, x14, x9
mul x23, x14, x11
mul x22, x14, x13
mul x7, x14, x3
umulh x20, x27, x17
mul x25, x27, x17
mul x2, x27, x8
umulh x15, x14, x3
umulh x24, x27, x8
mul x4, x27, x12
umulh x17, x14, x9
umulh x8, x27, x12
mul x12, x27, x16
umulh x16, x27, x16
adds x2, x28, x2
adcs x28, x21, x4
adcs x4, x6, x12
adcs x21, x1, x25
adc x6, x20, x10
umulh x12, x14, x11
umulh x1, x14, x13
ldr x25, [x0, #328]
adds x20, x5, x15
adcs x14, x23, x17
adcs x5, x22, x12
adc x15, x1, x10
adds x23, x21, x16
adc x17, x6, x10
mul x22, x25, x3
mul x12, x25, x9
mul x1, x25, x11
mul x21, x25, x13
extr x16, x17, x23, #63
and x6, x23, #0x7fffffffffffffff
mul x17, x16, x26
adds x23, x20, x22
adcs x16, x14, x12
adcs x20, x5, x1
adcs x22, x15, x21
adc x14, x10, x10
adds x12, x2, x17
adcs x1, x28, x24
adcs x5, x4, x8
adc x21, x6, x10
umulh x15, x25, x3
umulh x2, x25, x9
umulh x17, x25, x11
umulh x24, x25, x13
stp x12, x1, [x0, #384]
stp x5, x21, [x0, #400]
ldr x28, [x0, #336]
adds x4, x16, x15
adcs x8, x20, x2
adcs x6, x22, x17
adc x25, x14, x24
ldr x12, [x0, #344]
mul x1, x28, x3
mul x5, x28, x9
mul x21, x28, x11
mul x16, x28, x13
umulh x15, x28, x3
umulh x2, x28, x9
umulh x20, x28, x11
umulh x17, x28, x13
mul x22, x12, x3
umulh x24, x12, x3
mul x14, x12, x9
adds x28, x4, x1
adcs x3, x8, x5
adcs x1, x6, x21
adcs x4, x25, x16
adc x5, x10, x10
umulh x8, x12, x9
mul x21, x12, x11
umulh x6, x12, x11
mul x16, x12, x13
umulh x25, x12, x13
adds x9, x3, x15
adcs x11, x1, x2
adcs x12, x4, x20
adc x13, x5, x17
adds x15, x9, x22
adcs x3, x11, x14
adcs x2, x12, x21
adcs x1, x13, x16
adc x20, x10, x10
ldp x4, x5, [x0, #256]
ldp x17, x22, [x0, #272]
ldr x9, [x0, #288]
adds x14, x3, x24
adcs x11, x2, x8
adcs x21, x1, x6
adc x12, x20, x25
mul x13, x9, x5
mul x16, x9, x17
mul x24, x9, x22
mul x3, x9, x4
umulh x2, x27, x12
mul x8, x27, x12
mul x1, x27, x14
umulh x6, x9, x4
umulh x20, x27, x14
mul x25, x27, x11
umulh x12, x9, x5
umulh x14, x27, x11
mul x11, x27, x21
umulh x21, x27, x21
adds x7, x7, x1
adcs x1, x23, x25
adcs x23, x28, x11
adcs x25, x15, x8
adc x28, x2, x10
umulh x11, x9, x17
umulh x15, x9, x22
ldr x8, [x0, #296]
adds x2, x13, x6
adcs x9, x16, x12
adcs x6, x24, x11
adc x13, x15, x10
adds x16, x25, x21
adc x12, x28, x10
mul x24, x8, x4
mul x11, x8, x5
mul x15, x8, x17
mul x21, x8, x22
extr x25, x12, x16, #63
and x28, x16, #0x7fffffffffffffff
mul x12, x25, x26
adds x16, x2, x24
adcs x25, x9, x11
adcs x24, x6, x15
adcs x2, x13, x21
adc x11, x10, x10
adds x9, x7, x12
adcs x6, x1, x20
adcs x15, x23, x14
adc x13, x28, x10
umulh x21, x8, x4
umulh x7, x8, x5
umulh x12, x8, x17
umulh x1, x8, x22
stp x9, x6, [x0, #448]
stp x15, x13, [x0, #464]
ldr x20, [x0, #304]
adds x14, x25, x21
adcs x23, x24, x7
adcs x28, x2, x12
adc x8, x11, x1
ldr x9, [x0, #312]
mul x6, x20, x4
mul x13, x20, x5
mul x15, x20, x17
mul x25, x20, x22
umulh x21, x20, x4
umulh x24, x20, x5
umulh x7, x20, x17
umulh x2, x20, x22
mul x12, x9, x4
umulh x11, x9, x4
mul x1, x9, x5
adds x20, x14, x6
adcs x4, x23, x13
adcs x14, x28, x15
adcs x6, x8, x25
adc x23, x10, x10
umulh x13, x9, x5
mul x28, x9, x17
umulh x15, x9, x17
mul x25, x9, x22
umulh x8, x9, x22
adds x5, x4, x21
adcs x17, x14, x24
adcs x22, x6, x7
adc x9, x23, x2
adds x4, x5, x12
adcs x21, x17, x1
adcs x14, x22, x28
adcs x24, x9, x25
adc x7, x10, x10
ldp x6, x2, [x0, #352]
ldp x23, x5, [x0, #368]
ldp x12, x1, [x0, #384]
adds x17, x21, x11
adcs x28, x14, x13
adcs x22, x24, x15
adc x25, x7, x8
ldp x9, x11, [x0, #400]
umulh x21, x27, x25
mul x13, x27, x25
mul x14, x27, x17
umulh x15, x27, x17
mul x24, x27, x28
umulh x8, x27, x28
mul x7, x27, x22
umulh x25, x27, x22
subs x17, x6, x12
sbcs x28, x2, x1
sbcs x22, x23, x9
sbcs x12, x5, x11
csel x6, x10, x27, hs
adds x1, x3, x14
adcs x2, x16, x24
adcs x23, x20, x7
adcs x9, x4, x13
adc x5, x21, x10
ldp x11, x14, [x0, #384]
ldp x3, x24, [x0, #400]
ldr x16, [x0, #352]
subs x20, x17, x6
sbcs x7, x28, x10
sbcs x13, x22, x10
sbc x4, x12, x10
adds x21, x9, x25
adc x6, x5, x10
mul x17, x16, x14
mul x28, x16, x3
mul x22, x16, x24
mul x12, x16, x11
extr x9, x6, x21, #63
and x25, x21, #0x7fffffffffffffff
stp x13, x4, [x0, #432]
stp x20, x7, [x0, #416]
mul x5, x9, x26
umulh x6, x16, x11
umulh x21, x16, x14
umulh x13, x16, x3
adds x4, x1, x5
adcs x20, x2, x15
adcs x7, x23, x8
adc x9, x25, x10
umulh x1, x16, x24
stp x4, x20, [x0, #480]
stp x7, x9, [x0, #496]
ldr x5, [x0, #360]
adds x2, x17, x6
adcs x15, x28, x21
adcs x23, x22, x13
adc x8, x1, x10
ldr x25, [x0, #368]
mul x16, x5, x11
mul x4, x5, x14
mul x20, x5, x3
mul x7, x5, x24
umulh x9, x5, x11
umulh x6, x5, x14
umulh x17, x5, x3
umulh x21, x5, x24
mul x28, x25, x11
mul x13, x25, x14
mul x22, x25, x3
adds x1, x2, x16
adcs x5, x15, x4
adcs x16, x23, x20
adcs x2, x8, x7
adc x4, x10, x10
mul x15, x25, x24
umulh x20, x25, x11
umulh x23, x25, x14
umulh x7, x25, x3
umulh x8, x25, x24
adds x25, x5, x9
adcs x9, x16, x6
adcs x5, x2, x17
adc x6, x4, x21
ldr x16, [x0, #376]
adds x2, x25, x28
adcs x17, x9, x13
adcs x4, x5, x22
adcs x21, x6, x15
adc x28, x10, x10
mul x25, x16, x11
umulh x13, x16, x11
mul x9, x16, x14
umulh x5, x16, x14
mul x22, x16, x3
umulh x6, x16, x3
mul x15, x16, x24
umulh x11, x16, x24
adds x14, x17, x20
adcs x3, x4, x23
adcs x24, x21, x7
adc x16, x28, x8
adds x17, x14, x25
adcs x20, x3, x9
adcs x4, x24, x22
adcs x23, x16, x15
adc x21, x10, x10
ldp x7, x28, [x0, #416]
ldp x8, x14, [x0, #352]
ldp x25, x3, [x0, #368]
adds x9, x20, x13
adcs x24, x4, x5
adcs x22, x23, x6
adc x15, x21, x11
ldp x16, x20, [x0, #432]
movz x13, #56129, lsl #0
movk x13, #1, lsl #16
mul x4, x7, x13
umulh x5, x27, x15
mul x6, x27, x15
mul x23, x27, x9
mul x11, x28, x13
umulh x21, x27, x9
mul x15, x27, x24
umulh x9, x27, x24
mul x24, x27, x22
umulh x22, x27, x22
adds x12, x12, x23
adcs x23, x1, x15
adcs x1, x2, x24
adcs x15, x17, x6
adc x24, x5, x10
umulh x2, x7, x13
umulh x17, x28, x13
umulh x6, x20, x13
mul x5, x20, x13
mul x7, x16, x13
umulh x28, x16, x13
adds x20, x8, x4
adcs x16, x14, x11
adcs x13, x25, x7
adcs x8, x3, x5
adc x4, x6, x10
adds x14, x15, x22
adc x11, x24, x10
extr x7, x11, x14, #63
and x25, x14, #0x7fffffffffffffff
mul x5, x7, x26
adds x3, x8, x8
adc x6, x4, x4
adds x15, x12, x5
adcs x22, x23, x21
adcs x24, x1, x9
adc x11, x25, x10
mul x14, x6, x26
lsr x7, x3, #1
adds x8, x20, x14
adcs x4, x16, x2
adcs x12, x13, x17
adc x5, x7, x28
stp x15, x22, [x0, #96]
stp x24, x11, [x0, #112]
ldr x21, [x0, #416]
ldr x23, [x0, #424]
stp x8, x4, [x0, #128]
stp x12, x5, [x0, #144]
ldp x1, x9, [x0, #128]
ldp x25, x6, [x0, #144]
ldr x3, [x0, #432]
umulh x20, x21, x1
umulh x14, x21, x9
umulh x2, x21, x25
umulh x16, x21, x6
mul x17, x21, x9
mul x13, x21, x25
mul x28, x21, x6
mul x7, x23, x1
mul x15, x23, x9
mul x22, x23, x25
mul x24, x23, x6
umulh x11, x23, x1
umulh x4, x23, x9
umulh x8, x23, x25
umulh x12, x23, x6
adds x5, x17, x20
adcs x23, x13, x14
adcs x17, x28, x2
adc x20, x16, x10
mul x13, x21, x1
mul x14, x3, x1
mul x28, x3, x9
mul x2, x3, x25
mul x16, x3, x6
adds x21, x5, x7
adcs x5, x23, x15
adcs x7, x17, x22
adcs x23, x20, x24
adc x15, x10, x10
umulh x17, x3, x1
umulh x22, x3, x9
umulh x24, x3, x25
umulh x20, x3, x6
adds x3, x5, x11
adcs x5, x7, x4
adcs x11, x23, x8
adc x7, x15, x12
ldr x4, [x0, #440]
adds x8, x3, x14
adcs x23, x5, x28
adcs x12, x11, x2
adcs x15, x7, x16
adc x3, x10, x10
mul x14, x4, x1
umulh x28, x4, x1
mul x5, x4, x9
umulh x2, x4, x9
mul x11, x4, x25
umulh x16, x4, x25
mul x7, x4, x6
umulh x1, x4, x6
adds x9, x23, x17
adcs x25, x12, x22
adcs x4, x15, x24
adc x6, x3, x20
adds x17, x9, x14
adcs x23, x25, x5
adcs x22, x4, x11
adcs x12, x6, x7
adc x24, x10, x10
ldp x15, x20, [x0, #448]
ldp x3, x14, [x0, #464]
ldp x9, x5, [x0, #480]
adds x25, x23, x28
adcs x11, x22, x2
adcs x4, x12, x16
adc x7, x24, x1
ldp x6, x28, [x0, #496]
umulh x23, x27, x7
mul x2, x27, x7
mul x22, x27, x25
umulh x12, x27, x25
subs x16, x15, x9
sbcs x24, x20, x5
sbcs x1, x3, x6
sbcs x7, x14, x28
csel x25, x10, x27, hs
mul x15, x27, x11
mul x9, x27, x4
umulh x20, x27, x4
umulh x5, x27, x11
adds x3, x13, x22
adcs x6, x21, x15
adcs x14, x8, x9
adcs x28, x17, x2
adc x4, x23, x10
subs x11, x16, x25
sbcs x13, x24, x10
sbcs x22, x1, x10
sbc x21, x7, x10
adds x15, x28, x20
adc x8, x4, x10
umulh x9, x11, x13
umulh x2, x11, x22
umulh x17, x11, x21
mul x23, x11, x22
mul x16, x11, x21
mul x25, x13, x22
mul x24, x13, x21
umulh x1, x13, x22
mul x7, x11, x13
extr x20, x8, x15, #63
umulh x28, x13, x21
and x4, x15, #0x7fffffffffffffff
mul x8, x22, x21
mul x15, x20, x26
adds x20, x3, x15
adcs x3, x6, x12
adcs x15, x14, x5
adc x6, x4, x10
adds x12, x23, x9
adcs x14, x16, x2
adc x5, x17, x10
umulh x4, x22, x21
adds x23, x14, x25
adcs x9, x5, x24
adc x16, x28, x10
stp x20, x3, [x0, #128]
stp x15, x6, [x0, #144]
umulh x2, x11, x11
umulh x17, x13, x13
umulh x14, x22, x22
umulh x25, x21, x21
mul x24, x13, x13
mul x5, x22, x22
mul x28, x21, x21
adds x20, x9, x1
adcs x3, x16, x8
adc x15, x4, x10
extr x6, x23, x12, #63
extr x13, x12, x7, #63
lsl x22, x7, #1
mul x21, x11, x11
lsr x9, x15, #63
extr x1, x15, x3, #63
extr x16, x3, x20, #63
extr x8, x20, x23, #63
adds x4, x22, x2
adcs x12, x13, x24
adcs x7, x6, x17
adcs x11, x8, x5
adcs x15, x16, x14
adcs x3, x1, x28
adc x23, x9, x25
ldp x20, x22, [x0, #448]
ldp x2, x13, [x0, #464]
ldp x24, x17, [x0, #480]
ldp x6, x8, [x0, #496]
adds x5, x20, x24
adcs x16, x22, x17
adcs x14, x2, x6
adcs x28, x13, x8
csel x1, x27, x10, hs
umulh x25, x27, x23
mul x9, x27, x11
mul x20, x27, x15
mul x24, x27, x3
mul x22, x27, x23
umulh x17, x27, x3
umulh x6, x27, x11
umulh x2, x27, x15
adds x8, x21, x9
adcs x13, x4, x20
adcs x23, x12, x24
adcs x3, x7, x22
adc x11, x25, x10
adds x15, x5, x1
adcs x9, x16, x10
adc x21, x14, x10
umulh x4, x15, x9
umulh x20, x15, x21
umulh x24, x15, x28
adds x12, x3, x17
adc x22, x11, x10
mul x7, x15, x21
mul x25, x15, x28
umulh x5, x9, x28
mul x1, x9, x21
mul x16, x9, x28
umulh x14, x9, x21
extr x17, x22, x12, #63
and x3, x12, #0x7fffffffffffffff
umulh x11, x21, x28
mul x22, x21, x28
mul x12, x17, x26
adds x17, x7, x4
adcs x7, x25, x20
adc x4, x24, x10
mul x25, x15, x9
adds x20, x8, x12
adcs x24, x13, x6
adcs x8, x23, x2
adc x12, x3, x10
adds x6, x7, x1
adcs x13, x4, x16
adc x2, x5, x10
stp x20, x24, [x0, #192]
stp x8, x12, [x0, #208]
adds x23, x13, x14
adcs x3, x2, x22
adc x1, x11, x10
umulh x7, x15, x15
umulh x4, x9, x9
umulh x16, x21, x21
umulh x5, x28, x28
mul x20, x9, x9
mul x24, x21, x21
mul x8, x28, x28
extr x12, x6, x17, #63
extr x13, x17, x25, #63
lsr x14, x1, #63
extr x2, x1, x3, #63
extr x22, x3, x23, #63
extr x11, x23, x6, #63
lsl x9, x25, #1
mul x21, x15, x15
adds x28, x9, x7
adcs x17, x13, x20
adcs x1, x12, x4
adcs x3, x11, x24
adcs x6, x22, x16
adcs x23, x2, x8
adc x25, x14, x5
ldp x15, x9, [x0, #192]
ldp x7, x20, [x0, #208]
ldr x13, [x0, #64]
mul x4, x13, x9
mul x12, x13, x7
mul x11, x13, x20
umulh x24, x27, x25
mul x22, x27, x25
mul x16, x27, x3
umulh x2, x13, x15
umulh x8, x27, x3
mul x5, x27, x6
umulh x14, x13, x9
umulh x25, x27, x6
mul x3, x27, x23
umulh x6, x27, x23
adds x23, x21, x16
adcs x16, x28, x5
adcs x21, x17, x3
adcs x28, x1, x22
adc x5, x24, x10
umulh x3, x13, x7
umulh x17, x13, x20
ldr x1, [x0, #72]
mul x22, x13, x15
adds x24, x4, x2
adcs x13, x12, x14
adcs x4, x11, x3
adc x2, x17, x10
adds x12, x28, x6
adc x14, x5, x10
mul x11, x1, x15
mul x3, x1, x9
mul x17, x1, x7
mul x28, x1, x20
extr x6, x14, x12, #63
and x5, x12, #0x7fffffffffffffff
mul x14, x6, x26
adds x12, x24, x11
adcs x6, x13, x3
adcs x24, x4, x17
adcs x11, x2, x28
adc x13, x10, x10
adds x3, x23, x14
adcs x4, x16, x8
adcs x17, x21, x25
adc x28, x5, x10
umulh x2, x1, x15
umulh x23, x1, x9
umulh x14, x1, x7
umulh x8, x1, x20
stp x3, x4, [x0, #160]
stp x17, x28, [x0, #176]
ldr x16, [x0, #80]
adds x25, x6, x2
adcs x21, x24, x23
adcs x5, x11, x14
adc x1, x13, x8
ldr x4, [x0, #88]
mul x3, x16, x15
mul x17, x16, x9
mul x28, x16, x7
mul x6, x16, x20
umulh x2, x16, x15
umulh x24, x16, x9
umulh x23, x16, x7
umulh x14, x16, x20
mul x11, x4, x15
umulh x8, x4, x15
mul x13, x4, x9
adds x16, x25, x3
adcs x15, x21, x17
adcs x25, x5, x28
adcs x3, x1, x6
adc x17, x10, x10
umulh x21, x4, x9
mul x28, x4, x7
umulh x5, x4, x7
mul x6, x4, x20
umulh x1, x4, x20
adds x9, x15, x2
adcs x7, x25, x24
adcs x4, x3, x23
adc x20, x17, x14
adds x2, x9, x11
adcs x15, x7, x13
adcs x24, x4, x28
adcs x25, x20, x6
adc x23, x10, x10
adds x3, x15, x8
adcs x14, x24, x21
adcs x17, x25, x5
adc x11, x23, x1
umulh x9, x27, x11
mul x13, x27, x3
mul x7, x27, x14
mul x28, x27, x17
mul x4, x27, x11
umulh x6, x27, x17
umulh x20, x27, x3
umulh x8, x27, x14
adds x15, x22, x13
adcs x21, x12, x7
adcs x24, x16, x28
adcs x25, x2, x4
adc x5, x9, x10
adds x23, x25, x6
adc x1, x5, x10
extr x11, x1, x23, #63
and x17, x23, #0x7fffffffffffffff
mul x3, x11, x26
adds x14, x15, x3
adcs x22, x21, x20
adcs x13, x24, x8
adc x12, x17, x10
stp x14, x22, [x0, #192]
stp x13, x12, [x0, #208]
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
.globl lab_sc_o3_22_30_1
lab_sc_o3_22_30_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
ldp x9, x24, [x0, #192]
ldp x5, x28, [x0, #208]
adds x6, x7, x3
adcs x21, x11, x10
adc x14, x8, x10
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x6, x21, [x0, #224]
stp x14, x12, [x0, #240]
subs x11, x25, x9
sbcs x8, x20, x24
sbcs x2, x22, x5
sbcs x13, x16, x28
csel x4, x10, x27, hs
adds x17, x25, x9
adcs x1, x20, x24
adcs x6, x22, x5
adcs x21, x16, x28
csel x14, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
ldp x12, x9, [x0, #224]
ldp x25, x24, [x0, #240]
subs x20, x11, x4
sbcs x22, x8, x10
sbcs x5, x2, x10
sbc x28, x13, x10
adds x16, x17, x14
adcs x23, x1, x10
adc x15, x6, x10
umulh x3, x12, x9
umulh x7, x12, x25
umulh x11, x12, x24
stp x20, x22, [x0, #320]
stp x16, x23, [x0, #288]
stp x15, x21, [x0, #304]
stp x5, x28, [x0, #336]
mul x4, x12, x24
mul x8, x12, x25
umulh x2, x9, x24
mul x13, x25, x24
umulh x17, x9, x25
mul x14, x9, x24
umulh x1, x25, x24
mul x6, x9, x25
mul x20, x12, x9
adds x22, x8, x3
adcs x16, x4, x7
adc x23, x11, x10
umulh x15, x25, x25
mul x21, x25, x25
umulh x5, x9, x9
umulh x28, x24, x24
mul x3, x24, x24
mul x8, x9, x9
umulh x4, x12, x12
mul x7, x12, x12
lsl x11, x20, #1
adds x25, x16, x6
adcs x24, x23, x14
adc x9, x2, x10
extr x12, x22, x20, #63
adds x16, x24, x17
adcs x6, x9, x13
adc x23, x1, x10
extr x14, x25, x22, #63
lsr x2, x23, #63
extr x20, x23, x6, #63
extr x17, x6, x16, #63
extr x24, x16, x25, #63
adds x13, x11, x4
adcs x9, x12, x8
adcs x1, x14, x5
adcs x22, x24, x21
adcs x23, x17, x15
adcs x6, x20, x3
adc x16, x2, x28
ldp x25, x11, [x0, #272]
ldp x4, x12, [x0, #256]
umulh x8, x4, x12
umulh x5, x4, x25
mul x14, x4, x25
mul x21, x4, x11
mul x24, x4, x12
umulh x17, x27, x16
mul x15, x27, x16
mul x3, x27, x22
umulh x20, x4, x11
mul x28, x27, x23
mul x2, x12, x25
umulh x16, x27, x23
umulh x23, x27, x22
mul x22, x27, x6
umulh x6, x27, x6
adds x3, x7, x3
adcs x7, x13, x28
adcs x13, x9, x22
adcs x28, x1, x15
adc x22, x17, x10
adds x9, x14, x8
adcs x15, x21, x5
adc x1, x20, x10
umulh x17, x12, x11
mul x14, x12, x11
umulh x8, x12, x25
umulh x21, x25, x11
mul x5, x25, x11
adds x20, x15, x2
adcs x15, x1, x14
adc x2, x17, x10
adds x1, x28, x6
adc x14, x22, x10
extr x17, x14, x1, #63
adds x28, x15, x8
adcs x6, x2, x5
adc x22, x21, x10
mul x14, x17, x26
and x15, x1, #0x7fffffffffffffff
adds x8, x3, x14
adcs x2, x7, x23
adcs x5, x13, x16
adc x21, x15, x10
extr x17, x22, x6, #63
extr x1, x6, x28, #63
extr x3, x20, x9, #63
extr x14, x9, x24, #63
extr x7, x28, x20, #63
lsr x23, x22, #63
stp x8, x2, [x0, #352]
lsl x13, x24, #1
stp x5, x21, [x0, #368]
umulh x16, x12, x12
umulh x15, x4, x4
mul x6, x12, x12
mul x9, x25, x25
umulh x20, x11, x11
mul x28, x11, x11
umulh x22, x25, x25
mul x8, x4, x4
adds x2, x13, x15
adcs x24, x14, x6
adcs x5, x3, x16
adcs x21, x7, x9
adcs x12, x1, x22
adcs x11, x17, x28
adc x25, x23, x20
ldp x4, x15, [x0, #240]
ldr x13, [x0, #320]
ldp x6, x14, [x0, #224]
mul x16, x13, x4
mul x3, x13, x14
mul x7, x13, x15
mul x9, x13, x6
mul x1, x27, x21
umulh x22, x13, x6
mul x17, x27, x25
umulh x28, x27, x25
mul x23, x27, x12
umulh x20, x13, x14
umulh x25, x27, x12
umulh x12, x27, x21
mul x21, x27, x11
umulh x11, x27, x11
adds x1, x8, x1
adcs x8, x2, x23
adcs x23, x24, x21
adcs x2, x5, x17
adc x24, x28, x10
umulh x21, x13, x15
umulh x5, x13, x4
ldr x17, [x0, #328]
adds x28, x3, x22
adcs x13, x16, x20
adcs x3, x7, x5
adc x22, x21, x10
adds x16, x2, x11
adc x20, x24, x10
mul x7, x17, x6
mul x5, x17, x15
mul x21, x17, x14
mul x2, x17, x4
extr x11, x20, x16, #63
and x24, x16, #0x7fffffffffffffff
mul x20, x11, x26
adds x16, x28, x7
adcs x11, x13, x21
adcs x28, x3, x2
adcs x7, x22, x5
adc x13, x10, x10
adds x21, x1, x20
adcs x2, x8, x12
adcs x3, x23, x25
adc x5, x24, x10
umulh x22, x17, x15
umulh x1, x17, x4
umulh x20, x17, x6
umulh x12, x17, x14
stp x21, x2, [x0, #384]
stp x3, x5, [x0, #400]
ldr x8, [x0, #336]
adds x23, x11, x20
adcs x25, x28, x12
adcs x24, x7, x1
adc x17, x13, x22
ldr x21, [x0, #344]
mul x2, x8, x6
mul x3, x8, x15
mul x5, x8, x14
mul x11, x8, x4
umulh x20, x8, x4
umulh x12, x8, x6
umulh x28, x8, x15
umulh x1, x8, x14
mul x7, x21, x15
umulh x22, x21, x15
mul x13, x21, x6
adds x8, x23, x2
adcs x15, x25, x5
adcs x2, x24, x11
adcs x23, x17, x3
adc x5, x10, x10
umulh x25, x21, x6
umulh x11, x21, x14
mul x24, x21, x14
mul x3, x21, x4
umulh x17, x21, x4
adds x6, x15, x12
adcs x14, x2, x1
adcs x21, x23, x20
adc x4, x5, x28
adds x12, x6, x13
adcs x15, x14, x24
adcs x1, x21, x3
adcs x2, x4, x7
adc x20, x10, x10
ldp x23, x5, [x0, #256]
ldp x28, x13, [x0, #272]
ldr x6, [x0, #288]
adds x24, x15, x25
adcs x14, x1, x11
adcs x3, x2, x17
adc x21, x20, x22
mul x4, x6, x5
mul x7, x6, x13
mul x25, x6, x28
mul x15, x6, x23
umulh x1, x27, x21
mul x11, x27, x21
umulh x2, x27, x3
mul x17, x27, x3
mul x20, x27, x24
umulh x22, x6, x23
mul x21, x27, x14
umulh x3, x27, x14
umulh x14, x27, x24
adds x24, x9, x20
adcs x9, x16, x21
adcs x20, x8, x17
adcs x16, x12, x11
adc x21, x1, x10
umulh x8, x6, x28
umulh x17, x6, x5
umulh x12, x6, x13
ldr x11, [x0, #296]
adds x1, x4, x22
adcs x6, x25, x17
adcs x22, x7, x8
adc x4, x12, x10
adds x25, x16, x2
adc x17, x21, x10
mul x7, x11, x23
mul x8, x11, x5
mul x12, x11, x28
mul x2, x11, x13
extr x16, x17, x25, #63
and x21, x25, #0x7fffffffffffffff
mul x17, x16, x26
adds x25, x1, x7
adcs x16, x6, x8
adcs x7, x22, x12
adcs x1, x4, x2
adc x8, x10, x10
adds x6, x24, x17
adcs x22, x9, x14
adcs x12, x20, x3
adc x4, x21, x10
umulh x2, x11, x5
umulh x24, x11, x13
umulh x17, x11, x23
umulh x9, x11, x28
stp x6, x22, [x0, #448]
stp x12, x4, [x0, #464]
ldr x14, [x0, #304]
adds x3, x16, x17
adcs x20, x7, x2
adcs x21, x1, x9
adc x11, x8, x24
ldr x6, [x0, #312]
mul x22, x14, x23
mul x4, x14, x28
umulh x12, x14, x23
mul x16, x14, x5
umulh x17, x14, x28
mul x7, x14, x13
umulh x2, x14, x13
umulh x1, x14, x5
mul x9, x6, x28
umulh x8, x6, x28
mul x24, x6, x13
umulh x14, x6, x13
umulh x28, x6, x23
adds x13, x3, x22
adcs x3, x20, x16
adcs x22, x21, x4
adcs x20, x11, x7
adc x16, x10, x10
mul x21, x6, x23
mul x4, x6, x5
umulh x7, x6, x5
adds x11, x3, x12
adcs x23, x22, x1
adcs x5, x20, x17
adc x6, x16, x2
adds x3, x11, x21
adcs x12, x23, x4
adcs x22, x5, x9
adcs x1, x6, x24
adc x17, x10, x10
ldp x20, x2, [x0, #384]
ldp x16, x11, [x0, #368]
ldp x21, x4, [x0, #352]
adds x23, x12, x28
adcs x9, x22, x7
adcs x5, x1, x8
adc x24, x17, x14
ldp x6, x28, [x0, #400]
umulh x12, x27, x24
mul x7, x27, x24
mul x22, x27, x9
mul x8, x27, x5
umulh x1, x27, x5
umulh x14, x27, x9
mul x17, x27, x23
umulh x24, x27, x23
subs x5, x21, x20
sbcs x9, x4, x2
sbcs x23, x16, x6
sbcs x20, x11, x28
csel x21, x10, x27, hs
adds x2, x15, x17
adcs x4, x25, x22
adcs x16, x13, x8
adcs x6, x3, x7
adc x11, x12, x10
ldr x28, [x0, #352]
ldp x17, x15, [x0, #400]
ldp x22, x25, [x0, #384]
subs x13, x5, x21
sbcs x8, x9, x10
sbcs x7, x23, x10
sbc x3, x20, x10
adds x12, x6, x1
adc x21, x11, x10
mul x5, x28, x15
mul x9, x28, x17
mul x23, x28, x25
mul x20, x28, x22
extr x6, x21, x12, #63
and x1, x12, #0x7fffffffffffffff
stp x7, x3, [x0, #432]
stp x13, x8, [x0, #416]
mul x11, x6, x26
umulh x21, x28, x17
umulh x12, x28, x22
umulh x7, x28, x25
adds x3, x2, x11
adcs x13, x4, x24
adcs x8, x16, x14
adc x6, x1, x10
umulh x2, x28, x15
stp x3, x13, [x0, #480]
stp x8, x6, [x0, #496]
ldr x11, [x0, #360]
adds x4, x23, x12
adcs x24, x9, x7
adcs x16, x5, x21
adc x14, x2, x10
ldr x1, [x0, #368]
mul x28, x11, x22
mul x3, x11, x17
umulh x13, x11, x17
mul x8, x11, x25
mul x6, x11, x15
mul x12, x1, x15
umulh x23, x11, x15
mul x7, x1, x17
umulh x9, x11, x22
umulh x21, x11, x25
umulh x5, x1, x15
mul x2, x1, x22
adds x11, x4, x28
adcs x28, x24, x8
adcs x4, x16, x3
adcs x8, x14, x6
adc x24, x10, x10
umulh x3, x1, x17
mul x16, x1, x25
ldr x6, [x0, #376]
adds x14, x28, x9
adcs x9, x4, x21
adcs x28, x8, x13
adc x21, x24, x23
umulh x4, x1, x25
umulh x8, x1, x22
mul x13, x6, x22
umulh x24, x6, x22
mul x23, x6, x17
umulh x1, x6, x17
mul x22, x6, x15
umulh x17, x6, x15
adds x15, x14, x2
adcs x2, x9, x16
adcs x14, x28, x7
adcs x16, x21, x12
adc x9, x10, x10
mul x28, x6, x25
umulh x7, x6, x25
adds x21, x2, x8
adcs x12, x14, x4
adcs x25, x16, x3
adc x6, x9, x5
adds x2, x21, x13
adcs x8, x12, x28
adcs x14, x25, x23
adcs x4, x6, x22
adc x16, x10, x10
ldp x3, x9, [x0, #368]
ldp x5, x21, [x0, #416]
ldp x13, x12, [x0, #352]
adds x28, x8, x24
adcs x25, x14, x7
adcs x23, x4, x1
adc x22, x16, x17
movz x6, #56129, lsl #0
ldp x8, x24, [x0, #432]
movk x6, #1, lsl #16
mul x14, x5, x6
umulh x7, x27, x22
mul x1, x27, x22
mul x4, x27, x25
mul x17, x27, x28
mul x16, x21, x6
umulh x22, x27, x28
umulh x28, x27, x25
mul x25, x27, x23
umulh x23, x27, x23
adds x20, x20, x17
adcs x17, x11, x4
adcs x11, x15, x25
adcs x4, x2, x1
adc x25, x7, x10
umulh x15, x21, x6
mul x2, x8, x6
umulh x1, x24, x6
mul x7, x24, x6
umulh x21, x8, x6
umulh x24, x5, x6
adds x8, x13, x14
adcs x5, x12, x16
adcs x6, x3, x2
adcs x13, x9, x7
adc x14, x1, x10
adds x12, x4, x23
adc x16, x25, x10
extr x2, x16, x12, #63
and x3, x12, #0x7fffffffffffffff
mul x7, x2, x26
adds x9, x13, x13
adc x1, x14, x14
adds x4, x20, x7
adcs x23, x17, x22
adcs x25, x11, x28
adc x16, x3, x10
lsr x12, x9, #1
mul x2, x1, x26
adds x13, x8, x2
adcs x14, x5, x24
adcs x20, x6, x15
adc x7, x12, x21
stp x25, x16, [x0, #112]
stp x4, x23, [x0, #96]
ldr x22, [x0, #416]
ldr x17, [x0, #424]
stp x13, x14, [x0, #128]
stp x20, x7, [x0, #144]
ldp x11, x28, [x0, #128]
ldp x3, x9, [x0, #144]
ldr x1, [x0, #432]
umulh x8, x22, x11
umulh x2, x22, x3
umulh x24, x22, x9
umulh x5, x22, x28
mul x15, x22, x28
mul x6, x22, x9
mul x21, x17, x9
mul x12, x22, x3
umulh x25, x17, x3
mul x16, x17, x28
umulh x4, x17, x9
mul x23, x17, x11
mul x14, x17, x3
umulh x13, x17, x11
umulh x20, x17, x28
adds x7, x15, x8
adcs x17, x12, x5
adcs x15, x6, x2
adc x8, x24, x10
mul x12, x22, x11
mul x5, x1, x11
mul x6, x1, x28
mul x2, x1, x3
mul x24, x1, x9
adds x22, x7, x23
adcs x7, x17, x16
adcs x23, x15, x14
adcs x17, x8, x21
adc x16, x10, x10
umulh x15, x1, x28
umulh x14, x1, x9
umulh x21, x1, x3
umulh x8, x1, x11
adds x1, x7, x13
adcs x7, x23, x20
adcs x13, x17, x25
adc x23, x16, x4
ldr x20, [x0, #440]
adds x25, x1, x5
adcs x17, x7, x6
adcs x4, x13, x2
adcs x16, x23, x24
adc x1, x10, x10
mul x5, x20, x9
umulh x6, x20, x9
mul x7, x20, x3
umulh x2, x20, x3
mul x13, x20, x11
umulh x24, x20, x11
mul x23, x20, x28
umulh x9, x20, x28
adds x3, x17, x8
adcs x11, x4, x15
adcs x20, x16, x21
adc x28, x1, x14
adds x8, x3, x13
adcs x17, x11, x23
adcs x15, x20, x7
adcs x4, x28, x5
adc x21, x10, x10
ldp x16, x14, [x0, #480]
ldp x1, x13, [x0, #464]
ldp x3, x23, [x0, #448]
adds x11, x17, x24
adcs x7, x15, x9
adcs x20, x4, x2
adc x5, x21, x6
ldp x28, x24, [x0, #496]
umulh x17, x27, x5
mul x9, x27, x5
mul x15, x27, x7
mul x4, x27, x11
subs x2, x3, x16
sbcs x21, x23, x14
sbcs x6, x1, x28
sbcs x5, x13, x24
csel x3, x10, x27, hs
mul x16, x27, x20
umulh x23, x27, x20
umulh x14, x27, x11
umulh x1, x27, x7
adds x28, x12, x4
adcs x13, x22, x15
adcs x24, x25, x16
adcs x20, x8, x9
adc x11, x17, x10
subs x7, x2, x3
sbcs x12, x21, x10
sbcs x4, x6, x10
sbc x22, x5, x10
adds x15, x20, x23
adc x25, x11, x10
umulh x16, x7, x12
umulh x9, x7, x22
mul x8, x7, x22
umulh x17, x7, x4
mul x2, x7, x4
mul x3, x12, x22
umulh x21, x12, x4
mul x6, x12, x4
mul x5, x7, x12
extr x23, x25, x15, #63
umulh x20, x12, x22
and x11, x15, #0x7fffffffffffffff
mul x25, x4, x22
mul x15, x23, x26
adds x23, x28, x15
adcs x28, x13, x14
adcs x15, x24, x1
adc x13, x11, x10
adds x14, x2, x16
adcs x24, x8, x17
adc x1, x9, x10
umulh x11, x4, x22
adds x2, x24, x6
adcs x16, x1, x3
adc x8, x20, x10
stp x23, x28, [x0, #128]
stp x15, x13, [x0, #144]
umulh x17, x22, x22
mul x9, x12, x12
umulh x24, x12, x12
mul x6, x22, x22
mul x3, x4, x4
extr x1, x14, x5, #63
umulh x20, x4, x4
adds x23, x16, x21
adcs x28, x8, x25
adc x15, x11, x10
extr x13, x2, x14, #63
umulh x12, x7, x7
lsl x22, x5, #1
mul x4, x7, x7
lsr x16, x15, #63
extr x21, x23, x2, #63
extr x8, x28, x23, #63
extr x25, x15, x28, #63
adds x11, x22, x12
adcs x14, x1, x9
adcs x5, x13, x24
adcs x7, x21, x3
adcs x2, x8, x20
adcs x23, x25, x6
adc x28, x16, x17
ldp x15, x22, [x0, #448]
ldp x12, x1, [x0, #464]
ldp x9, x24, [x0, #496]
ldp x13, x21, [x0, #480]
adds x3, x15, x13
adcs x8, x22, x21
adcs x20, x12, x9
adcs x6, x1, x24
csel x25, x27, x10, hs
mul x17, x27, x2
mul x16, x27, x7
mul x15, x27, x28
mul x13, x27, x23
umulh x22, x27, x28
umulh x21, x27, x23
umulh x9, x27, x2
umulh x12, x27, x7
adds x24, x3, x25
adcs x1, x8, x10
adc x28, x20, x10
adds x23, x4, x16
adcs x2, x11, x17
adcs x7, x14, x13
adcs x3, x5, x15
adc x25, x22, x10
umulh x8, x24, x1
umulh x20, x24, x28
umulh x16, x24, x6
mul x4, x1, x28
mul x11, x24, x6
mul x17, x24, x28
mul x13, x1, x6
mul x14, x24, x1
adds x15, x3, x21
adc x5, x25, x10
umulh x22, x1, x6
umulh x21, x1, x28
extr x3, x5, x15, #63
and x25, x15, #0x7fffffffffffffff
umulh x5, x28, x6
mul x15, x3, x26
adds x3, x17, x8
adcs x17, x11, x20
adc x8, x16, x10
mul x11, x28, x6
adds x20, x23, x15
adcs x16, x2, x12
adcs x23, x7, x9
adc x15, x25, x10
adds x12, x17, x4
adcs x2, x8, x13
adc x9, x22, x10
stp x20, x16, [x0, #192]
stp x23, x15, [x0, #208]
umulh x7, x6, x6
adds x25, x2, x21
adcs x4, x9, x11
adc x17, x5, x10
umulh x8, x1, x1
umulh x13, x28, x28
extr x22, x12, x3, #63
extr x20, x3, x14, #63
mul x16, x6, x6
lsl x23, x14, #1
umulh x15, x24, x24
mul x2, x28, x28
mul x21, x1, x1
extr x9, x17, x4, #63
lsr x11, x17, #63
extr x5, x4, x25, #63
extr x3, x25, x12, #63
mul x6, x24, x24
adds x14, x23, x15
adcs x28, x20, x21
adcs x1, x22, x8
adcs x17, x3, x2
adcs x4, x5, x13
adcs x12, x9, x16
adc x25, x11, x7
ldp x24, x23, [x0, #192]
ldp x15, x21, [x0, #208]
ldr x20, [x0, #64]
mul x8, x20, x23
mul x22, x20, x21
mul x3, x20, x15
mul x2, x27, x17
umulh x5, x20, x24
umulh x13, x27, x25
mul x9, x27, x25
mul x16, x27, x12
umulh x7, x27, x12
umulh x11, x27, x17
mul x25, x27, x4
umulh x12, x20, x15
umulh x17, x27, x4
adds x4, x6, x2
adcs x2, x14, x25
adcs x6, x28, x16
adcs x14, x1, x9
adc x25, x13, x10
umulh x16, x20, x23
umulh x28, x20, x21
ldr x1, [x0, #72]
mul x9, x20, x24
adds x13, x8, x5
adcs x20, x3, x16
adcs x8, x22, x12
adc x5, x28, x10
adds x3, x14, x7
adc x16, x25, x10
mul x22, x1, x23
mul x12, x1, x24
mul x28, x1, x15
mul x14, x1, x21
extr x7, x16, x3, #63
and x25, x3, #0x7fffffffffffffff
mul x16, x7, x26
adds x3, x13, x12
adcs x7, x20, x22
adcs x13, x8, x28
adcs x12, x5, x14
adc x20, x10, x10
adds x22, x4, x16
adcs x8, x2, x11
adcs x28, x6, x17
adc x14, x25, x10
umulh x5, x1, x24
umulh x4, x1, x21
umulh x16, x1, x23
umulh x11, x1, x15
stp x22, x8, [x0, #160]
stp x28, x14, [x0, #176]
ldr x2, [x0, #80]
adds x17, x7, x5
adcs x6, x13, x16
adcs x25, x12, x11
adc x1, x20, x4
ldr x8, [x0, #88]
mul x22, x2, x24
mul x28, x2, x21
mul x14, x2, x15
mul x7, x2, x23
umulh x5, x2, x23
umulh x13, x2, x21
umulh x16, x2, x15
umulh x11, x2, x24
mul x12, x8, x15
umulh x4, x8, x15
mul x20, x8, x21
adds x2, x17, x22
adcs x15, x6, x7
adcs x17, x25, x14
adcs x22, x1, x28
adc x7, x10, x10
umulh x6, x8, x21
mul x14, x8, x23
umulh x25, x8, x23
mul x28, x8, x24
umulh x1, x8, x24
adds x21, x15, x11
adcs x23, x17, x5
adcs x8, x22, x16
adc x24, x7, x13
adds x11, x21, x28
adcs x15, x23, x14
adcs x5, x8, x12
adcs x17, x24, x20
adc x16, x10, x10
adds x22, x15, x1
adcs x13, x5, x25
adcs x7, x17, x4
adc x28, x16, x6
umulh x21, x27, x28
mul x14, x27, x13
mul x23, x27, x22
mul x12, x27, x7
mul x8, x27, x28
umulh x20, x27, x7
umulh x24, x27, x22
umulh x1, x27, x13
adds x15, x9, x23
adcs x25, x3, x14
adcs x5, x2, x12
adcs x17, x11, x8
adc x4, x21, x10
adds x16, x17, x20
adc x6, x4, x10
extr x28, x6, x16, #63
and x7, x16, #0x7fffffffffffffff
mul x22, x28, x26
adds x13, x15, x22
adcs x9, x25, x24
adcs x23, x5, x1
adc x3, x7, x10
stp x13, x9, [x0, #192]
stp x23, x3, [x0, #208]
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
.globl lab_sc_o3_22_15_0
lab_sc_o3_22_15_0:
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
mov w26, #19
mov w27, #38
sub x19, x19, #1
ldp x1, x2, [x0, #96]
ldp x3, x4, [x0, #112]
ldp x5, x6, [x0, #160]
add x7, x0, x19
ldp x8, x9, [x0, #176]
ldp x11, x12, [x0, #128]
ldp x13, x14, [x0, #144]
ldrb w15, [x7, #1984]
ldrb w16, [x7, #1985]
ldp x17, x20, [x0, #192]
ldp x21, x22, [x0, #208]
eor x23, x15, x16
tst x23, x23
csel x24, x5, x1, ne
csel x25, x1, x5, ne
csel x28, x6, x2, ne
csel x7, x2, x6, ne
csel x15, x8, x3, ne
csel x16, x3, x8, ne
csel x23, x9, x4, ne
csel x1, x4, x9, ne
csel x5, x17, x11, ne
csel x2, x11, x17, ne
csel x6, x20, x12, ne
csel x3, x12, x20, ne
csel x8, x21, x13, ne
csel x4, x13, x21, ne
csel x9, x22, x14, ne
csel x11, x14, x22, ne
stp x2, x3, [x0, #192]
stp x4, x11, [x0, #208]
subs x17, x24, x5
sbcs x12, x28, x6
sbcs x20, x15, x8
sbcs x13, x23, x9
csel x21, x10, x27, hs
adds x14, x24, x5
adcs x22, x28, x6
adcs x2, x15, x8
adcs x3, x23, x9
csel x4, x27, x10, hs
subs x11, x17, x21
sbcs x24, x12, x10
sbcs x5, x20, x10
sbc x28, x13, x10
adds x6, x14, x4
adcs x15, x22, x10
adc x8, x2, x10
ldp x23, x9, [x0, #192]
ldp x21, x17, [x0, #208]
stp x11, x24, [x0, #256]
stp x6, x15, [x0, #224]
stp x8, x3, [x0, #240]
stp x5, x28, [x0, #272]
subs x12, x25, x23
sbcs x20, x7, x9
sbcs x13, x16, x21
sbcs x4, x1, x17
csel x14, x10, x27, hs
adds x22, x25, x23
adcs x2, x7, x9
adcs x11, x16, x21
adcs x24, x1, x17
csel x6, x27, x10, hs
subs x15, x12, x14
sbcs x8, x20, x10
sbcs x3, x13, x10
sbc x5, x4, x10
adds x28, x22, x6
adcs x23, x2, x10
adc x25, x11, x10
ldp x9, x7, [x0, #224]
ldp x16, x21, [x0, #240]
stp x15, x8, [x0, #320]
stp x28, x23, [x0, #288]
stp x25, x24, [x0, #304]
stp x3, x5, [x0, #336]
umulh x17, x9, x7
umulh x1, x9, x16
umulh x12, x9, x21
mul x14, x9, x16
mul x20, x9, x21
umulh x13, x7, x21
mul x4, x7, x16
mul x22, x7, x21
umulh x6, x7, x16
umulh x2, x16, x21
mul x11, x16, x21
mul x15, x9, x7
adds x8, x14, x17
adcs x28, x20, x1
adc x23, x12, x10
umulh x25, x9, x9
mul x24, x7, x7
lsl x3, x15, #1
mul x5, x9, x9
adds x17, x28, x4
adcs x14, x23, x22
adc x20, x13, x10
umulh x1, x7, x7
umulh x12, x16, x16
mul x9, x16, x16
extr x28, x8, x15, #63
adds x4, x14, x6
adcs x23, x20, x11
adc x22, x2, x10
umulh x13, x21, x21
mul x7, x21, x21
extr x16, x17, x8, #63
lsr x15, x22, #63
extr x6, x22, x23, #63
extr x14, x23, x4, #63
extr x11, x4, x17, #63
adds x20, x3, x25
adcs x2, x28, x24
adcs x21, x16, x1
adcs x8, x11, x9
adcs x22, x14, x12
adcs x23, x6, x7
adc x4, x15, x13
umulh x17, x27, x4
mul x3, x27, x8
mul x25, x27, x22
mul x28, x27, x23
mul x24, x27, x4
umulh x1, x27, x23
umulh x16, x27, x8
umulh x9, x27, x22
adds x11, x5, x3
adcs x14, x20, x25
adcs x12, x2, x28
adcs x7, x21, x24
adc x6, x17, x10
ldp x13, x15, [x0, #256]
ldp x4, x23, [x0, #272]
adds x8, x7, x1
adc x22, x6, x10
umulh x3, x13, x15
umulh x5, x13, x4
mul x20, x13, x4
mul x25, x13, x23
mul x28, x13, x15
extr x2, x22, x8, #63
umulh x24, x13, x23
and x21, x8, #0x7fffffffffffffff
mul x17, x15, x4
mul x7, x2, x26
mul x1, x15, x23
adds x6, x11, x7
adcs x22, x14, x16
adcs x8, x12, x9
adc x2, x21, x10
umulh x11, x15, x23
umulh x7, x15, x4
umulh x14, x4, x23
mul x16, x4, x23
stp x6, x22, [x0, #352]
adds x12, x20, x3
adcs x9, x25, x5
adc x21, x24, x10
stp x8, x2, [x0, #368]
umulh x6, x13, x13
mul x22, x15, x15
lsl x20, x28, #1
mul x3, x13, x13
adds x25, x9, x17
adcs x5, x21, x1
adc x24, x11, x10
umulh x8, x15, x15
umulh x2, x4, x4
mul x13, x4, x4
extr x9, x12, x28, #63
adds x17, x5, x7
adcs x21, x24, x16
adc x1, x14, x10
umulh x11, x23, x23
mul x15, x23, x23
extr x4, x25, x12, #63
lsr x28, x1, #63
extr x5, x1, x21, #63
extr x7, x21, x17, #63
extr x24, x17, x25, #63
adds x16, x20, x6
adcs x14, x9, x22
adcs x23, x4, x8
adcs x12, x24, x13
adcs x1, x7, x2
adcs x21, x5, x15
adc x25, x28, x11
umulh x17, x27, x25
mul x6, x27, x12
mul x20, x27, x1
mul x22, x27, x21
mul x9, x27, x25
umulh x8, x27, x21
umulh x4, x27, x12
umulh x24, x27, x1
adds x13, x3, x6
adcs x7, x16, x20
adcs x2, x14, x22
adcs x5, x23, x9
adc x15, x17, x10
ldp x28, x11, [x0, #224]
ldp x25, x21, [x0, #240]
ldr x12, [x0, #320]
adds x1, x5, x8
adc x6, x15, x10
mul x3, x12, x11
mul x20, x12, x25
mul x16, x12, x21
mul x14, x12, x28
extr x22, x6, x1, #63
umulh x23, x12, x28
and x9, x1, #0x7fffffffffffffff
umulh x17, x12, x11
mul x5, x22, x26
umulh x8, x12, x25
adds x15, x13, x5
adcs x6, x7, x4
adcs x1, x2, x24
adc x22, x9, x10
umulh x13, x12, x21
adds x5, x3, x23
adcs x4, x20, x17
adcs x7, x16, x8
adc x2, x13, x10
stp x15, x6, [x0, #384]
stp x1, x22, [x0, #400]
ldr x24, [x0, #328]
mul x9, x24, x28
mul x12, x24, x11
mul x3, x24, x25
mul x23, x24, x21
umulh x20, x24, x28
umulh x17, x24, x11
umulh x16, x24, x25
umulh x8, x24, x21
ldr x13, [x0, #336]
adds x15, x5, x9
adcs x6, x4, x12
adcs x1, x7, x3
adcs x22, x2, x23
adc x24, x10, x10
mul x5, x13, x28
mul x9, x13, x11
mul x4, x13, x25
mul x12, x13, x21
umulh x3, x13, x28
umulh x7, x13, x11
adds x23, x6, x20
adcs x2, x1, x17
adcs x6, x22, x16
adc x20, x24, x8
umulh x17, x13, x25
umulh x1, x13, x21
ldr x16, [x0, #344]
adds x22, x23, x5
adcs x8, x2, x9
adcs x24, x6, x4
adcs x13, x20, x12
adc x5, x10, x10
mul x23, x16, x28
umulh x9, x16, x28
mul x2, x16, x11
umulh x4, x16, x11
mul x6, x16, x25
mul x12, x16, x21
adds x20, x8, x3
adcs x28, x24, x7
adcs x11, x13, x17
adc x3, x5, x1
umulh x8, x16, x25
umulh x7, x16, x21
adds x24, x20, x23
adcs x17, x28, x2
adcs x13, x11, x6
adcs x5, x3, x12
adc x1, x10, x10
adds x25, x17, x9
adcs x16, x13, x4
adcs x21, x5, x8
adc x23, x1, x7
umulh x20, x27, x23
mul x2, x27, x25
mul x28, x27, x16
mul x6, x27, x21
mul x11, x27, x23
umulh x3, x27, x21
umulh x12, x27, x25
umulh x9, x27, x16
adds x17, x14, x2
adcs x13, x15, x28
adcs x4, x22, x6
adcs x5, x24, x11
adc x8, x20, x10
ldp x1, x7, [x0, #256]
ldp x23, x21, [x0, #272]
ldr x25, [x0, #288]
adds x16, x5, x3
adc x14, x8, x10
mul x2, x25, x7
mul x15, x25, x23
mul x28, x25, x21
mul x22, x25, x1
extr x6, x14, x16, #63
umulh x24, x25, x1
and x11, x16, #0x7fffffffffffffff
umulh x20, x25, x7
mul x3, x6, x26
umulh x5, x25, x23
adds x8, x17, x3
adcs x14, x13, x12
adcs x16, x4, x9
adc x6, x11, x10
umulh x17, x25, x21
adds x3, x2, x24
adcs x13, x15, x20
adcs x12, x28, x5
adc x9, x17, x10
stp x8, x14, [x0, #448]
stp x16, x6, [x0, #464]
ldr x4, [x0, #296]
mul x11, x4, x1
mul x25, x4, x7
mul x24, x4, x23
mul x2, x4, x21
umulh x15, x4, x1
umulh x20, x4, x7
umulh x28, x4, x23
umulh x5, x4, x21
ldr x17, [x0, #304]
adds x8, x3, x11
adcs x14, x13, x25
adcs x6, x12, x24
adcs x16, x9, x2
adc x4, x10, x10
mul x11, x17, x1
mul x3, x17, x7
mul x25, x17, x23
mul x13, x17, x21
umulh x12, x17, x1
umulh x24, x17, x7
adds x9, x14, x15
adcs x2, x6, x20
adcs x14, x16, x28
adc x15, x4, x5
umulh x6, x17, x23
umulh x20, x17, x21
ldr x16, [x0, #312]
adds x28, x9, x11
adcs x4, x2, x3
adcs x5, x14, x25
adcs x17, x15, x13
adc x9, x10, x10
mul x11, x16, x1
umulh x2, x16, x1
mul x3, x16, x7
umulh x14, x16, x7
mul x25, x16, x23
mul x13, x16, x21
adds x15, x4, x12
adcs x1, x5, x24
adcs x7, x17, x6
adc x4, x9, x20
umulh x12, x16, x23
umulh x5, x16, x21
adds x24, x15, x11
adcs x6, x1, x3
adcs x17, x7, x25
adcs x20, x4, x13
adc x9, x10, x10
adds x23, x6, x2
adcs x21, x17, x14
adcs x16, x20, x12
adc x15, x9, x5
umulh x11, x27, x15
mul x3, x27, x23
mul x1, x27, x21
mul x25, x27, x16
mul x7, x27, x15
umulh x13, x27, x16
umulh x4, x27, x23
umulh x2, x27, x21
adds x6, x22, x3
adcs x14, x8, x1
adcs x17, x28, x25
adcs x12, x24, x7
adc x20, x11, x10
ldp x5, x9, [x0, #352]
ldp x15, x16, [x0, #368]
ldp x23, x21, [x0, #384]
ldp x3, x22, [x0, #400]
adds x1, x12, x13
adc x8, x20, x10
subs x28, x5, x23
sbcs x25, x9, x21
sbcs x7, x15, x3
sbcs x24, x16, x22
csel x11, x10, x27, hs
extr x12, x8, x1, #63
and x13, x1, #0x7fffffffffffffff
mul x20, x12, x26
adds x23, x6, x20
adcs x5, x14, x4
adcs x21, x17, x2
adc x9, x13, x10
subs x15, x28, x11
sbcs x3, x25, x10
sbcs x16, x7, x10
sbc x22, x24, x10
stp x23, x5, [x0, #480]
stp x21, x9, [x0, #496]
ldp x8, x1, [x0, #384]
ldp x12, x6, [x0, #400]
stp x16, x22, [x0, #432]
stp x15, x3, [x0, #416]
ldr x20, [x0, #352]
ldr x14, [x0, #360]
umulh x4, x20, x8
umulh x17, x20, x1
umulh x2, x20, x12
umulh x13, x20, x6
mul x11, x20, x1
mul x28, x20, x12
mul x25, x20, x6
mul x7, x14, x8
mul x24, x14, x1
mul x23, x14, x12
mul x5, x20, x8
mul x21, x14, x6
umulh x9, x14, x8
umulh x16, x14, x1
adds x22, x11, x4
adcs x15, x28, x17
adcs x3, x25, x2
adc x20, x13, x10
umulh x4, x14, x12
umulh x11, x14, x6
ldr x17, [x0, #368]
adds x28, x22, x7
adcs x2, x15, x24
adcs x25, x3, x23
adcs x13, x20, x21
adc x14, x10, x10
mul x7, x17, x8
mul x22, x17, x1
mul x24, x17, x12
mul x15, x17, x6
umulh x23, x17, x8
umulh x3, x17, x1
adds x21, x2, x9
adcs x20, x25, x16
adcs x9, x13, x4
adc x2, x14, x11
umulh x16, x17, x12
umulh x25, x17, x6
ldr x13, [x0, #376]
adds x4, x21, x7
adcs x14, x20, x22
adcs x11, x9, x24
adcs x17, x2, x15
adc x7, x10, x10
mul x21, x13, x8
umulh x22, x13, x8
mul x20, x13, x1
umulh x9, x13, x1
mul x24, x13, x12
mul x2, x13, x6
adds x15, x14, x23
adcs x8, x11, x3
adcs x1, x17, x16
adc x14, x7, x25
umulh x23, x13, x12
umulh x11, x13, x6
adds x3, x15, x21
adcs x17, x8, x20
adcs x16, x1, x24
adcs x7, x14, x2
adc x25, x10, x10
adds x12, x17, x22
adcs x6, x16, x9
adcs x13, x7, x23
adc x15, x25, x11
umulh x21, x27, x15
mul x8, x27, x12
mul x20, x27, x6
mul x1, x27, x13
mul x24, x27, x15
umulh x2, x27, x13
umulh x14, x27, x12
umulh x17, x27, x6
adds x22, x5, x8
adcs x16, x28, x20
adcs x9, x4, x1
adcs x23, x3, x24
adc x7, x21, x10
ldp x11, x25, [x0, #432]
ldp x15, x13, [x0, #416]
movz x12, #56129, lsl #0
ldp x6, x5, [x0, #352]
ldp x8, x28, [x0, #368]
adds x20, x23, x2
adc x1, x7, x10
movk x12, #1, lsl #16
mul x4, x15, x12
extr x3, x1, x20, #63
mul x24, x13, x12
and x21, x20, #0x7fffffffffffffff
mul x23, x11, x12
mul x2, x3, x26
mul x7, x25, x12
adds x1, x22, x2
adcs x20, x16, x14
adcs x3, x9, x17
adc x22, x21, x10
umulh x2, x25, x12
adds x14, x6, x4
adcs x16, x5, x24
adcs x9, x8, x23
adcs x17, x28, x7
adc x21, x2, x10
stp x1, x20, [x0, #96]
stp x3, x22, [x0, #112]
umulh x25, x15, x12
umulh x6, x13, x12
umulh x4, x11, x12
ldr x5, [x0, #416]
adds x24, x17, x17
adc x23, x21, x21
mul x8, x23, x26
lsr x7, x24, #1
adds x28, x14, x8
adcs x2, x16, x25
adcs x1, x9, x6
adc x20, x7, x4
stp x28, x2, [x0, #128]
stp x1, x20, [x0, #144]
ldr x3, [x0, #424]
ldp x22, x15, [x0, #128]
ldp x13, x11, [x0, #144]
umulh x12, x5, x22
umulh x17, x5, x15
umulh x21, x5, x13
umulh x23, x5, x11
mul x24, x5, x15
mul x14, x5, x13
mul x8, x5, x11
mul x25, x3, x22
mul x16, x3, x15
mul x6, x3, x13
mul x9, x5, x22
mul x4, x3, x11
umulh x7, x3, x22
umulh x2, x3, x15
adds x28, x24, x12
adcs x1, x14, x17
adcs x20, x8, x21
adc x5, x23, x10
umulh x24, x3, x13
umulh x12, x3, x11
ldr x14, [x0, #432]
adds x17, x28, x25
adcs x8, x1, x16
adcs x21, x20, x6
adcs x23, x5, x4
adc x3, x10, x10
mul x28, x14, x22
mul x25, x14, x15
mul x1, x14, x13
mul x16, x14, x11
umulh x20, x14, x22
umulh x6, x14, x15
adds x4, x8, x7
adcs x5, x21, x2
adcs x8, x23, x24
adc x7, x3, x12
umulh x21, x14, x13
umulh x2, x14, x11
ldr x24, [x0, #440]
adds x23, x4, x28
adcs x12, x5, x25
adcs x3, x8, x1
adcs x14, x7, x16
adc x4, x10, x10
mul x28, x24, x22
umulh x25, x24, x22
mul x5, x24, x15
umulh x1, x24, x15
mul x8, x24, x13
mul x16, x24, x11
adds x7, x12, x20
adcs x22, x3, x6
adcs x15, x14, x21
adc x20, x4, x2
umulh x12, x24, x13
umulh x6, x24, x11
adds x3, x7, x28
adcs x21, x22, x5
adcs x14, x15, x8
adcs x2, x20, x16
adc x4, x10, x10
adds x13, x21, x25
adcs x24, x14, x1
adcs x11, x2, x12
adc x28, x4, x6
umulh x7, x27, x28
mul x5, x27, x13
mul x22, x27, x24
mul x8, x27, x11
mul x15, x27, x28
umulh x16, x27, x11
umulh x20, x27, x13
umulh x25, x27, x24
adds x21, x9, x5
adcs x1, x17, x22
adcs x14, x23, x8
adcs x2, x3, x15
adc x12, x7, x10
ldp x4, x6, [x0, #448]
ldp x28, x11, [x0, #464]
ldp x13, x24, [x0, #480]
ldp x9, x5, [x0, #496]
adds x17, x2, x16
adc x22, x12, x10
subs x23, x4, x13
sbcs x8, x6, x24
sbcs x15, x28, x9
sbcs x3, x11, x5
csel x7, x10, x27, hs
extr x16, x22, x17, #63
and x2, x17, #0x7fffffffffffffff
mul x12, x16, x26
adds x4, x21, x12
adcs x13, x1, x20
adcs x6, x14, x25
adc x24, x2, x10
subs x28, x23, x7
sbcs x9, x8, x10
sbcs x11, x15, x10
sbc x5, x3, x10
stp x4, x13, [x0, #128]
stp x6, x24, [x0, #144]
umulh x22, x28, x9
umulh x17, x28, x11
umulh x16, x28, x5
mul x21, x28, x11
mul x12, x28, x5
umulh x1, x9, x5
mul x20, x9, x11
mul x14, x9, x5
umulh x25, x9, x11
umulh x2, x11, x5
mul x23, x11, x5
mul x7, x28, x9
adds x8, x21, x22
adcs x15, x12, x17
adc x3, x16, x10
umulh x4, x28, x28
mul x13, x9, x9
lsl x6, x7, #1
mul x24, x28, x28
adds x21, x15, x20
adcs x22, x3, x14
adc x12, x1, x10
umulh x17, x9, x9
umulh x16, x11, x11
mul x28, x11, x11
extr x15, x8, x7, #63
adds x20, x22, x25
adcs x14, x12, x23
adc x3, x2, x10
umulh x1, x5, x5
mul x9, x5, x5
extr x11, x21, x8, #63
lsr x7, x3, #63
extr x22, x3, x14, #63
extr x25, x14, x20, #63
extr x12, x20, x21, #63
adds x23, x6, x4
adcs x2, x15, x13
adcs x5, x11, x17
adcs x8, x12, x28
adcs x3, x25, x16
adcs x14, x22, x9
adc x21, x7, x1
umulh x20, x27, x21
mul x6, x27, x8
mul x4, x27, x3
mul x15, x27, x14
mul x13, x27, x21
umulh x17, x27, x14
umulh x11, x27, x8
umulh x12, x27, x3
adds x28, x24, x6
adcs x25, x23, x4
adcs x16, x2, x15
adcs x9, x5, x13
adc x22, x20, x10
ldp x1, x7, [x0, #448]
ldp x21, x14, [x0, #464]
ldp x8, x3, [x0, #480]
ldp x6, x24, [x0, #496]
adds x23, x9, x17
adc x4, x22, x10
adds x15, x1, x8
adcs x2, x7, x3
adcs x13, x21, x6
adcs x5, x14, x24
csel x20, x27, x10, hs
extr x17, x4, x23, #63
and x9, x23, #0x7fffffffffffffff
mul x22, x17, x26
adds x1, x28, x22
adcs x8, x25, x11
adcs x7, x16, x12
adc x3, x9, x10
adds x6, x15, x20
adcs x21, x2, x10
adc x24, x13, x10
stp x1, x8, [x0, #192]
stp x7, x3, [x0, #208]
umulh x14, x6, x21
umulh x4, x6, x24
umulh x23, x6, x5
mul x17, x6, x24
mul x28, x6, x5
umulh x22, x21, x5
mul x11, x21, x24
mul x25, x21, x5
umulh x12, x21, x24
umulh x16, x24, x5
mul x9, x24, x5
mul x15, x6, x21
adds x20, x17, x14
adcs x2, x28, x4
adc x13, x23, x10
umulh x1, x6, x6
mul x8, x21, x21
lsl x7, x15, #1
mul x3, x6, x6
adds x17, x2, x11
adcs x14, x13, x25
adc x28, x22, x10
umulh x4, x21, x21
umulh x23, x24, x24
mul x6, x24, x24
extr x11, x20, x15, #63
adds x2, x14, x12
adcs x13, x28, x9
adc x25, x16, x10
umulh x22, x5, x5
mul x21, x5, x5
extr x24, x17, x20, #63
lsr x15, x25, #63
extr x14, x25, x13, #63
extr x12, x13, x2, #63
extr x28, x2, x17, #63
adds x9, x7, x1
adcs x16, x11, x8
adcs x5, x24, x4
adcs x20, x28, x6
adcs x25, x12, x23
adcs x13, x14, x21
adc x17, x15, x22
umulh x2, x27, x17
mul x7, x27, x20
mul x1, x27, x25
mul x8, x27, x13
mul x11, x27, x17
umulh x4, x27, x13
umulh x24, x27, x20
umulh x28, x27, x25
adds x6, x3, x7
adcs x12, x9, x1
adcs x23, x16, x8
adcs x14, x5, x11
adc x21, x2, x10
ldp x22, x15, [x0, #192]
ldp x17, x13, [x0, #208]
ldr x20, [x0, #64]
adds x25, x14, x4
adc x7, x21, x10
mul x3, x20, x15
mul x9, x20, x17
mul x1, x20, x13
mul x8, x20, x22
extr x16, x7, x25, #63
umulh x5, x20, x22
and x11, x25, #0x7fffffffffffffff
umulh x2, x20, x15
mul x14, x16, x26
umulh x4, x20, x17
adds x21, x6, x14
adcs x7, x12, x24
adcs x25, x23, x28
adc x16, x11, x10
umulh x6, x20, x13
adds x14, x3, x5
adcs x24, x9, x2
adcs x12, x1, x4
adc x28, x6, x10
stp x21, x7, [x0, #160]
stp x25, x16, [x0, #176]
ldr x23, [x0, #72]
mul x11, x23, x22
mul x20, x23, x15
mul x3, x23, x17
mul x5, x23, x13
umulh x9, x23, x22
umulh x2, x23, x15
umulh x1, x23, x17
umulh x4, x23, x13
ldr x6, [x0, #80]
adds x7, x14, x11
adcs x21, x24, x20
adcs x25, x12, x3
adcs x16, x28, x5
adc x23, x10, x10
mul x14, x6, x22
mul x11, x6, x15
mul x24, x6, x17
mul x20, x6, x13
umulh x12, x6, x22
umulh x3, x6, x15
adds x5, x21, x9
adcs x28, x25, x2
adcs x21, x16, x1
adc x9, x23, x4
umulh x25, x6, x17
umulh x2, x6, x13
ldr x1, [x0, #88]
adds x16, x5, x14
adcs x4, x28, x11
adcs x23, x21, x24
adcs x6, x9, x20
adc x5, x10, x10
mul x14, x1, x22
umulh x11, x1, x22
mul x28, x1, x15
umulh x24, x1, x15
mul x21, x1, x17
mul x20, x1, x13
adds x9, x4, x12
adcs x22, x23, x3
adcs x15, x6, x25
adc x12, x5, x2
umulh x4, x1, x17
umulh x3, x1, x13
adds x23, x9, x14
adcs x25, x22, x28
adcs x6, x15, x21
adcs x2, x12, x20
adc x5, x10, x10
adds x17, x25, x11
adcs x1, x6, x24
adcs x13, x2, x4
adc x14, x5, x3
umulh x9, x27, x14
mul x28, x27, x17
mul x22, x27, x1
mul x21, x27, x13
mul x15, x27, x14
umulh x20, x27, x13
umulh x12, x27, x17
umulh x11, x27, x1
adds x25, x8, x28
adcs x24, x7, x22
adcs x6, x16, x21
adcs x2, x23, x15
adc x4, x9, x10
adds x5, x2, x20
adc x3, x4, x10
extr x14, x3, x5, #63
and x13, x5, #0x7fffffffffffffff
mul x17, x14, x26
adds x1, x25, x17
adcs x8, x24, x12
adcs x28, x6, x11
adc x7, x13, x10
stp x1, x8, [x0, #192]
stp x28, x7, [x0, #208]
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
.globl lab_sc_o3_22_15_1
lab_sc_o3_22_15_1:
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
mov w26, #19
mov w27, #38
ldp x1, x2, [x0, #112]
ldp x3, x4, [x0, #208]
ldp x5, x6, [x0, #160]
ldp x7, x8, [x0, #192]
ldp x9, x11, [x0, #128]
sub x19, x19, #1
ldp x12, x13, [x0, #144]
ldp x14, x15, [x0, #176]
ldp x16, x17, [x0, #96]
add x20, x0, x19
ldrb w21, [x20, #1984]
ldrb w22, [x20, #1985]
eor x23, x21, x22
tst x23, x23
csel x24, x5, x16, ne
csel x25, x16, x5, ne
csel x28, x6, x17, ne
csel x20, x17, x6, ne
csel x21, x14, x1, ne
csel x22, x1, x14, ne
csel x23, x15, x2, ne
csel x16, x2, x15, ne
csel x5, x7, x9, ne
csel x17, x9, x7, ne
csel x6, x8, x11, ne
csel x1, x11, x8, ne
csel x14, x3, x12, ne
csel x2, x12, x3, ne
csel x15, x4, x13, ne
csel x9, x13, x4, ne
stp x17, x1, [x0, #192]
stp x2, x9, [x0, #208]
adds x7, x24, x5
adcs x11, x28, x6
adcs x8, x21, x14
adcs x12, x23, x15
csel x3, x27, x10, hs
subs x13, x24, x5
sbcs x4, x28, x6
sbcs x17, x21, x14
sbcs x1, x23, x15
csel x2, x10, x27, hs
adds x9, x7, x3
adcs x24, x11, x10
adc x5, x8, x10
ldp x28, x6, [x0, #208]
ldp x21, x14, [x0, #192]
subs x23, x13, x2
sbcs x15, x4, x10
sbcs x3, x17, x10
sbc x7, x1, x10
stp x9, x24, [x0, #224]
stp x5, x12, [x0, #240]
subs x11, x25, x21
sbcs x8, x20, x14
sbcs x2, x22, x28
sbcs x13, x16, x6
csel x4, x10, x27, hs
adds x17, x25, x21
adcs x1, x20, x14
adcs x9, x22, x28
adcs x24, x16, x6
csel x5, x27, x10, hs
stp x23, x15, [x0, #256]
stp x3, x7, [x0, #272]
subs x12, x11, x4
sbcs x21, x8, x10
sbcs x25, x2, x10
sbc x14, x13, x10
adds x20, x17, x5
adcs x22, x1, x10
adc x28, x9, x10
ldp x6, x16, [x0, #224]
ldp x23, x15, [x0, #240]
stp x12, x21, [x0, #320]
stp x20, x22, [x0, #288]
stp x28, x24, [x0, #304]
stp x25, x14, [x0, #336]
umulh x3, x6, x16
umulh x7, x6, x23
umulh x11, x6, x15
mul x4, x6, x15
mul x8, x6, x23
umulh x2, x16, x15
mul x13, x23, x15
umulh x17, x16, x23
mul x5, x16, x15
umulh x1, x23, x15
mul x9, x16, x23
mul x12, x6, x16
adds x21, x8, x3
adcs x20, x4, x7
adc x22, x11, x10
umulh x28, x6, x6
mul x24, x16, x16
lsl x25, x12, #1
mul x14, x6, x6
adds x3, x20, x9
adcs x8, x22, x5
adc x4, x2, x10
umulh x7, x23, x23
mul x11, x23, x23
umulh x6, x16, x16
extr x20, x21, x12, #63
adds x9, x8, x17
adcs x22, x4, x13
adc x5, x1, x10
umulh x2, x15, x15
extr x23, x3, x21, #63
mul x16, x15, x15
lsr x12, x5, #63
extr x17, x5, x22, #63
extr x8, x22, x9, #63
extr x13, x9, x3, #63
adds x4, x25, x28
adcs x1, x20, x24
adcs x21, x23, x6
adcs x15, x13, x11
adcs x5, x8, x7
adcs x22, x17, x16
adc x9, x12, x2
umulh x3, x27, x9
mul x25, x27, x15
mul x28, x27, x5
mul x20, x27, x9
mul x24, x27, x22
umulh x6, x27, x22
umulh x23, x27, x5
umulh x11, x27, x15
adds x13, x14, x25
adcs x8, x4, x28
adcs x7, x1, x24
adcs x16, x21, x20
adc x17, x3, x10
ldp x2, x12, [x0, #272]
ldp x9, x22, [x0, #256]
adds x5, x16, x6
adc x15, x17, x10
umulh x25, x9, x2
mul x14, x9, x2
mul x4, x9, x12
umulh x28, x9, x22
mul x24, x9, x22
extr x1, x15, x5, #63
umulh x20, x9, x12
and x21, x5, #0x7fffffffffffffff
mul x3, x22, x2
mul x16, x1, x26
mul x6, x22, x12
adds x17, x13, x16
adcs x15, x8, x11
adcs x5, x7, x23
adc x1, x21, x10
umulh x13, x22, x12
umulh x16, x22, x2
umulh x8, x2, x12
mul x11, x2, x12
stp x17, x15, [x0, #352]
adds x7, x14, x28
adcs x23, x4, x25
adc x21, x20, x10
stp x5, x1, [x0, #368]
umulh x17, x9, x9
mul x15, x22, x22
lsl x14, x24, #1
mul x28, x9, x9
adds x4, x23, x3
adcs x25, x21, x6
adc x20, x13, x10
umulh x5, x22, x22
mul x1, x2, x2
extr x9, x7, x24, #63
umulh x23, x2, x2
adds x3, x25, x16
adcs x21, x20, x11
adc x6, x8, x10
extr x13, x4, x7, #63
umulh x22, x12, x12
mul x24, x12, x12
lsr x2, x6, #63
extr x25, x6, x21, #63
extr x16, x21, x3, #63
extr x20, x3, x4, #63
adds x11, x14, x17
adcs x8, x9, x15
adcs x7, x13, x5
adcs x12, x20, x1
adcs x6, x16, x23
adcs x21, x25, x24
adc x4, x2, x22
umulh x3, x27, x4
mul x17, x27, x12
mul x14, x27, x4
mul x15, x27, x6
mul x9, x27, x21
umulh x5, x27, x21
umulh x13, x27, x6
umulh x20, x27, x12
adds x1, x28, x17
adcs x16, x11, x15
adcs x23, x8, x9
adcs x25, x7, x14
adc x24, x3, x10
ldp x2, x22, [x0, #240]
ldr x4, [x0, #320]
ldp x21, x6, [x0, #224]
adds x12, x25, x5
adc x17, x24, x10
mul x28, x4, x2
mul x15, x4, x6
mul x11, x4, x22
mul x8, x4, x21
extr x9, x17, x12, #63
umulh x7, x4, x21
and x14, x12, #0x7fffffffffffffff
umulh x3, x4, x6
mul x25, x9, x26
umulh x5, x4, x2
adds x24, x1, x25
adcs x17, x16, x20
adcs x12, x23, x13
adc x9, x14, x10
umulh x1, x4, x22
adds x25, x15, x7
adcs x20, x28, x3
adcs x16, x11, x5
adc x23, x1, x10
stp x24, x17, [x0, #384]
stp x12, x9, [x0, #400]
ldr x13, [x0, #328]
mul x14, x13, x21
mul x4, x13, x22
mul x15, x13, x6
mul x7, x13, x2
umulh x28, x13, x22
ldr x3, [x0, #336]
umulh x11, x13, x2
umulh x5, x13, x21
umulh x1, x13, x6
adds x24, x25, x14
adcs x17, x20, x15
adcs x12, x16, x7
adcs x9, x23, x4
adc x13, x10, x10
mul x25, x3, x21
mul x14, x3, x22
mul x20, x3, x6
mul x15, x3, x2
umulh x7, x3, x21
umulh x16, x3, x6
adds x4, x17, x5
adcs x23, x12, x1
adcs x17, x9, x11
adc x5, x13, x28
umulh x1, x3, x2
umulh x12, x3, x22
ldr x11, [x0, #344]
adds x9, x4, x25
adcs x28, x23, x20
adcs x13, x17, x15
adcs x3, x5, x14
adc x25, x10, x10
mul x4, x11, x21
umulh x20, x11, x21
mul x23, x11, x22
umulh x15, x11, x6
mul x17, x11, x6
mul x14, x11, x2
adds x5, x28, x7
adcs x21, x13, x16
adcs x6, x3, x1
adc x7, x25, x12
umulh x28, x11, x22
umulh x16, x11, x2
adds x13, x5, x4
adcs x1, x21, x17
adcs x3, x6, x14
adcs x25, x7, x23
adc x12, x10, x10
adds x22, x1, x20
adcs x11, x3, x15
adcs x2, x25, x16
adc x4, x12, x28
umulh x5, x27, x4
mul x17, x27, x4
umulh x21, x27, x2
mul x14, x27, x22
mul x6, x27, x11
mul x7, x27, x2
umulh x23, x27, x11
umulh x20, x27, x22
adds x1, x8, x14
adcs x3, x24, x6
adcs x15, x9, x7
adcs x25, x13, x17
adc x16, x5, x10
ldp x12, x28, [x0, #256]
ldp x4, x2, [x0, #272]
ldr x11, [x0, #288]
adds x22, x25, x21
adc x8, x16, x10
mul x14, x11, x28
mul x24, x11, x2
mul x6, x11, x4
mul x9, x11, x12
extr x7, x8, x22, #63
umulh x13, x11, x12
and x17, x22, #0x7fffffffffffffff
umulh x5, x11, x28
mul x21, x7, x26
umulh x25, x11, x4
adds x16, x1, x21
adcs x8, x3, x20
adcs x22, x15, x23
adc x7, x17, x10
umulh x1, x11, x2
adds x21, x14, x13
adcs x3, x6, x5
adcs x20, x24, x25
adc x23, x1, x10
stp x16, x8, [x0, #448]
stp x22, x7, [x0, #464]
ldr x15, [x0, #296]
mul x17, x15, x12
mul x11, x15, x28
umulh x13, x15, x28
umulh x14, x15, x2
mul x6, x15, x4
umulh x5, x15, x12
mul x24, x15, x2
umulh x25, x15, x4
ldr x1, [x0, #304]
adds x16, x21, x17
adcs x8, x3, x11
adcs x7, x20, x6
adcs x22, x23, x24
adc x15, x10, x10
mul x17, x1, x12
mul x21, x1, x4
umulh x11, x1, x12
mul x3, x1, x28
mul x20, x1, x2
umulh x6, x1, x28
adds x23, x8, x5
adcs x24, x7, x13
adcs x8, x22, x25
adc x5, x15, x14
umulh x7, x1, x4
umulh x13, x1, x2
ldr x22, [x0, #312]
adds x25, x23, x17
adcs x15, x24, x3
adcs x14, x8, x21
adcs x1, x5, x20
adc x23, x10, x10
mul x17, x22, x12
umulh x24, x22, x12
mul x3, x22, x4
mul x8, x22, x2
mul x21, x22, x28
umulh x20, x22, x28
adds x5, x15, x11
adcs x12, x14, x6
adcs x28, x1, x7
adc x15, x23, x13
umulh x11, x22, x4
umulh x14, x22, x2
adds x6, x5, x17
adcs x7, x12, x21
adcs x1, x28, x3
adcs x13, x15, x8
adc x23, x10, x10
adds x4, x7, x24
adcs x2, x1, x20
adcs x22, x13, x11
adc x5, x23, x14
umulh x17, x27, x5
mul x21, x27, x2
mul x12, x27, x5
mul x3, x27, x22
umulh x28, x27, x22
mul x8, x27, x4
umulh x15, x27, x2
umulh x24, x27, x4
adds x7, x9, x8
adcs x20, x16, x21
adcs x1, x25, x3
adcs x11, x6, x12
adc x13, x17, x10
ldp x14, x23, [x0, #384]
ldp x5, x22, [x0, #368]
ldp x2, x4, [x0, #352]
ldp x8, x9, [x0, #400]
adds x21, x11, x28
adc x16, x13, x10
subs x25, x2, x14
sbcs x3, x4, x23
sbcs x12, x5, x8
sbcs x6, x22, x9
csel x17, x10, x27, hs
extr x11, x16, x21, #63
and x28, x21, #0x7fffffffffffffff
mul x13, x11, x26
adds x14, x7, x13
adcs x2, x20, x24
adcs x23, x1, x15
adc x4, x28, x10
subs x5, x25, x17
sbcs x8, x3, x10
sbcs x22, x12, x10
sbc x9, x6, x10
stp x14, x2, [x0, #480]
stp x23, x4, [x0, #496]
ldr x16, [x0, #352]
ldp x21, x11, [x0, #400]
stp x22, x9, [x0, #432]
stp x5, x8, [x0, #416]
ldr x7, [x0, #360]
ldp x13, x20, [x0, #384]
umulh x24, x16, x21
umulh x1, x16, x11
mul x15, x16, x11
mul x28, x16, x21
umulh x17, x16, x13
umulh x25, x16, x20
mul x3, x16, x20
mul x12, x7, x21
mul x6, x7, x13
mul x14, x7, x20
mul x2, x16, x13
mul x23, x7, x11
umulh x4, x7, x13
umulh x22, x7, x20
adds x9, x3, x17
adcs x5, x28, x25
adcs x8, x15, x24
adc x16, x1, x10
umulh x17, x7, x21
umulh x3, x7, x11
ldr x25, [x0, #368]
adds x28, x9, x6
adcs x24, x5, x14
adcs x15, x8, x12
adcs x1, x16, x23
adc x7, x10, x10
mul x6, x25, x13
mul x9, x25, x11
mul x14, x25, x21
mul x5, x25, x20
umulh x12, x25, x20
umulh x8, x25, x13
adds x23, x24, x4
adcs x16, x15, x22
adcs x4, x1, x17
adc x24, x7, x3
umulh x22, x25, x11
umulh x15, x25, x21
ldr x1, [x0, #376]
adds x17, x23, x6
adcs x7, x16, x5
adcs x3, x4, x14
adcs x25, x24, x9
adc x6, x10, x10
mul x23, x1, x13
umulh x5, x1, x13
mul x16, x1, x21
mul x4, x1, x11
mul x14, x1, x20
umulh x24, x1, x20
adds x9, x7, x8
adcs x13, x3, x12
adcs x20, x25, x15
adc x7, x6, x22
umulh x8, x1, x21
umulh x3, x1, x11
adds x12, x9, x23
adcs x25, x13, x14
adcs x15, x20, x16
adcs x6, x7, x4
adc x22, x10, x10
adds x21, x25, x5
adcs x11, x15, x24
adcs x1, x6, x8
adc x9, x22, x3
umulh x23, x27, x9
mul x13, x27, x11
mul x14, x27, x21
mul x20, x27, x1
umulh x16, x27, x1
mul x4, x27, x9
umulh x7, x27, x21
umulh x25, x27, x11
adds x5, x2, x14
adcs x15, x28, x13
adcs x24, x17, x20
adcs x8, x12, x4
adc x6, x23, x10
movz x3, #56129, lsl #0
ldp x22, x1, [x0, #368]
ldp x9, x21, [x0, #432]
ldp x11, x2, [x0, #416]
ldp x14, x28, [x0, #352]
adds x13, x8, x16
adc x20, x6, x10
movk x3, #1, lsl #16
mul x17, x11, x3
extr x12, x20, x13, #63
mul x4, x2, x3
and x23, x13, #0x7fffffffffffffff
mul x8, x9, x3
mul x16, x12, x26
mul x6, x21, x3
adds x20, x5, x16
adcs x13, x15, x7
adcs x12, x24, x25
adc x5, x23, x10
umulh x16, x21, x3
adds x7, x14, x17
adcs x15, x28, x4
adcs x24, x22, x8
adcs x25, x1, x6
adc x23, x16, x10
stp x12, x5, [x0, #112]
stp x20, x13, [x0, #96]
umulh x21, x2, x3
umulh x14, x9, x3
umulh x17, x11, x3
ldr x28, [x0, #416]
adds x4, x25, x25
adc x8, x23, x23
mul x22, x8, x26
lsr x6, x4, #1
adds x1, x7, x22
adcs x16, x15, x17
adcs x12, x24, x21
adc x5, x6, x14
stp x1, x16, [x0, #128]
stp x12, x5, [x0, #144]
ldr x20, [x0, #424]
ldp x13, x2, [x0, #128]
ldp x9, x11, [x0, #144]
umulh x3, x28, x13
umulh x25, x28, x9
umulh x23, x28, x11
umulh x8, x28, x2
mul x4, x28, x2
mul x7, x28, x11
mul x22, x28, x9
mul x17, x20, x2
mul x15, x20, x13
mul x21, x20, x9
mul x24, x28, x13
mul x14, x20, x11
umulh x6, x20, x13
umulh x16, x20, x2
adds x1, x4, x3
adcs x12, x22, x8
adcs x5, x7, x25
adc x28, x23, x10
umulh x4, x20, x9
umulh x3, x20, x11
ldr x22, [x0, #432]
adds x8, x1, x15
adcs x7, x12, x17
adcs x25, x5, x21
adcs x23, x28, x14
adc x20, x10, x10
mul x1, x22, x13
mul x15, x22, x2
mul x12, x22, x9
mul x17, x22, x11
umulh x5, x22, x2
umulh x21, x22, x13
adds x14, x7, x6
adcs x28, x25, x16
adcs x7, x23, x4
adc x6, x20, x3
umulh x25, x22, x11
umulh x16, x22, x9
ldr x4, [x0, #440]
adds x23, x14, x1
adcs x3, x28, x15
adcs x20, x7, x12
adcs x22, x6, x17
adc x14, x10, x10
mul x1, x4, x13
umulh x15, x4, x13
mul x28, x4, x11
mul x12, x4, x9
mul x7, x4, x2
umulh x17, x4, x2
adds x6, x3, x21
adcs x13, x20, x5
adcs x2, x22, x16
adc x21, x14, x25
umulh x3, x4, x9
umulh x5, x4, x11
adds x20, x6, x1
adcs x16, x13, x7
adcs x22, x2, x12
adcs x25, x21, x28
adc x14, x10, x10
adds x9, x16, x15
adcs x4, x22, x17
adcs x11, x25, x3
adc x1, x14, x5
umulh x6, x27, x1
mul x7, x27, x1
mul x13, x27, x4
mul x12, x27, x9
mul x2, x27, x11
umulh x28, x27, x11
umulh x21, x27, x9
umulh x15, x27, x4
adds x16, x24, x12
adcs x17, x8, x13
adcs x22, x23, x2
adcs x25, x20, x7
adc x3, x6, x10
ldp x14, x5, [x0, #480]
ldp x1, x11, [x0, #464]
ldp x9, x4, [x0, #496]
ldp x24, x12, [x0, #448]
adds x8, x25, x28
adc x13, x3, x10
subs x23, x24, x14
sbcs x2, x12, x5
sbcs x7, x1, x9
sbcs x20, x11, x4
csel x6, x10, x27, hs
and x28, x8, #0x7fffffffffffffff
extr x25, x13, x8, #63
mul x3, x25, x26
adds x24, x16, x3
adcs x14, x17, x21
adcs x12, x22, x15
adc x5, x28, x10
subs x1, x23, x6
sbcs x9, x2, x10
sbcs x11, x7, x10
sbc x4, x20, x10
stp x24, x14, [x0, #128]
stp x12, x5, [x0, #144]
umulh x13, x1, x9
umulh x8, x1, x4
mul x25, x1, x4
umulh x16, x1, x11
mul x3, x1, x11
umulh x17, x9, x4
mul x21, x9, x4
umulh x22, x9, x11
mul x15, x9, x11
mul x28, x11, x4
umulh x23, x11, x4
mul x6, x1, x9
adds x2, x3, x13
adcs x7, x25, x16
adc x20, x8, x10
mul x24, x9, x9
umulh x14, x1, x1
lsl x12, x6, #1
mul x5, x1, x1
adds x3, x7, x15
adcs x13, x20, x21
adc x25, x17, x10
umulh x16, x9, x9
mul x8, x11, x11
extr x1, x2, x6, #63
umulh x7, x11, x11
adds x15, x13, x22
adcs x21, x25, x28
adc x20, x23, x10
umulh x17, x4, x4
mul x9, x4, x4
extr x6, x3, x2, #63
lsr x11, x20, #63
extr x13, x15, x3, #63
extr x22, x21, x15, #63
extr x25, x20, x21, #63
adds x28, x12, x14
adcs x23, x1, x24
adcs x4, x6, x16
adcs x2, x13, x8
adcs x3, x22, x7
adcs x15, x25, x9
adc x21, x11, x17
umulh x20, x27, x21
mul x12, x27, x3
mul x14, x27, x2
mul x1, x27, x21
mul x24, x27, x15
umulh x16, x27, x15
umulh x6, x27, x3
umulh x13, x27, x2
adds x8, x5, x14
adcs x22, x28, x12
adcs x7, x23, x24
adcs x9, x4, x1
adc x25, x20, x10
ldp x17, x11, [x0, #448]
ldp x21, x15, [x0, #464]
ldp x3, x2, [x0, #496]
ldp x14, x5, [x0, #480]
adds x28, x9, x16
adc x12, x25, x10
adds x24, x17, x14
adcs x23, x11, x5
adcs x1, x21, x3
adcs x4, x15, x2
csel x20, x27, x10, hs
extr x16, x12, x28, #63
and x9, x28, #0x7fffffffffffffff
mul x25, x16, x26
adds x17, x8, x25
adcs x14, x22, x13
adcs x11, x7, x6
adc x5, x9, x10
adds x3, x24, x20
adcs x21, x23, x10
adc x2, x1, x10
stp x17, x14, [x0, #192]
stp x11, x5, [x0, #208]
umulh x15, x3, x2
umulh x12, x3, x4
mul x28, x21, x2
mul x16, x3, x4
umulh x8, x21, x4
mul x25, x3, x2
umulh x13, x3, x21
umulh x22, x2, x4
mul x6, x21, x4
umulh x7, x21, x2
mul x9, x2, x4
mul x24, x3, x21
adds x20, x25, x13
adcs x23, x16, x15
adc x1, x12, x10
lsl x17, x24, #1
umulh x14, x3, x3
mul x11, x21, x21
mul x5, x3, x3
adds x25, x23, x28
adcs x13, x1, x6
adc x16, x8, x10
umulh x15, x21, x21
umulh x12, x2, x2
extr x3, x20, x24, #63
mul x28, x2, x2
adds x23, x13, x7
adcs x1, x16, x9
adc x6, x22, x10
umulh x8, x4, x4
extr x21, x25, x20, #63
mul x24, x4, x4
lsr x2, x6, #63
extr x13, x6, x1, #63
extr x7, x1, x23, #63
extr x16, x23, x25, #63
adds x9, x17, x14
adcs x22, x3, x11
adcs x20, x21, x15
adcs x4, x16, x28
adcs x6, x7, x12
adcs x1, x13, x24
adc x25, x2, x8
umulh x23, x27, x25
mul x17, x27, x4
mul x14, x27, x25
mul x11, x27, x1
mul x3, x27, x6
umulh x15, x27, x1
umulh x21, x27, x6
umulh x16, x27, x4
adds x28, x5, x17
adcs x7, x9, x3
adcs x12, x22, x11
adcs x13, x20, x14
adc x24, x23, x10
ldp x8, x2, [x0, #192]
ldp x25, x1, [x0, #208]
ldr x6, [x0, #64]
adds x4, x13, x15
adc x17, x24, x10
mul x5, x6, x2
mul x9, x6, x1
mul x3, x6, x25
mul x11, x6, x8
extr x22, x17, x4, #63
umulh x20, x6, x8
and x14, x4, #0x7fffffffffffffff
umulh x23, x6, x2
mul x13, x22, x26
umulh x15, x6, x25
adds x24, x28, x13
adcs x17, x7, x16
adcs x4, x12, x21
adc x22, x14, x10
umulh x28, x6, x1
adds x13, x5, x20
adcs x16, x3, x23
adcs x7, x9, x15
adc x21, x28, x10
stp x24, x17, [x0, #160]
stp x4, x22, [x0, #176]
ldr x12, [x0, #72]
mul x14, x12, x8
mul x6, x12, x2
mul x5, x12, x25
mul x20, x12, x1
umulh x3, x12, x8
umulh x23, x12, x1
umulh x9, x12, x2
umulh x15, x12, x25
ldr x28, [x0, #80]
adds x17, x13, x14
adcs x24, x16, x6
adcs x4, x7, x5
adcs x22, x21, x20
adc x12, x10, x10
mul x13, x28, x8
mul x14, x28, x1
mul x16, x28, x25
mul x6, x28, x2
umulh x7, x28, x2
umulh x5, x28, x8
adds x20, x24, x3
adcs x21, x4, x9
adcs x24, x22, x15
adc x3, x12, x23
umulh x4, x28, x1
umulh x9, x28, x25
ldr x15, [x0, #88]
adds x22, x20, x13
adcs x23, x21, x6
adcs x12, x24, x16
adcs x28, x3, x14
adc x20, x10, x10
mul x13, x15, x8
umulh x6, x15, x8
mul x21, x15, x25
mul x16, x15, x1
mul x24, x15, x2
umulh x14, x15, x2
adds x3, x23, x5
adcs x8, x12, x7
adcs x2, x28, x9
adc x5, x20, x4
umulh x23, x15, x25
umulh x7, x15, x1
adds x12, x3, x13
adcs x9, x8, x24
adcs x28, x2, x21
adcs x4, x5, x16
adc x20, x10, x10
adds x25, x9, x6
adcs x15, x28, x14
adcs x1, x4, x23
adc x13, x20, x7
umulh x3, x27, x13
mul x24, x27, x15
mul x8, x27, x25
mul x21, x27, x1
mul x2, x27, x13
umulh x16, x27, x1
umulh x5, x27, x25
umulh x6, x27, x15
adds x9, x11, x8
adcs x14, x17, x24
adcs x28, x22, x21
adcs x4, x12, x2
adc x23, x3, x10
adds x20, x4, x16
adc x7, x23, x10
extr x13, x7, x20, #63
and x1, x20, #0x7fffffffffffffff
mul x25, x13, x26
adds x15, x9, x25
adcs x11, x14, x5
adcs x8, x28, x6
adc x17, x1, x10
stp x15, x11, [x0, #192]
stp x8, x17, [x0, #208]
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
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_st_o3(p: *mut u64, n: u64);fn lab_src(p: *mut u64, n: u64);fn lab_sc_o1_19_50_0(p: *mut u64, n: u64);fn lab_sc_o1_19_50_1(p: *mut u64, n: u64);fn lab_sc_o1_19_30_0(p: *mut u64, n: u64);fn lab_sc_o1_19_30_1(p: *mut u64, n: u64);fn lab_sc_o1_19_15_0(p: *mut u64, n: u64);fn lab_sc_o1_19_15_1(p: *mut u64, n: u64);fn lab_sc_o1_21_30_0(p: *mut u64, n: u64);fn lab_sc_o1_21_30_1(p: *mut u64, n: u64);fn lab_sc_o1_21_15_0(p: *mut u64, n: u64);fn lab_sc_o1_21_15_1(p: *mut u64, n: u64);fn lab_sc_o1_22_30_0(p: *mut u64, n: u64);fn lab_sc_o1_22_30_1(p: *mut u64, n: u64);fn lab_sc_o1_22_15_0(p: *mut u64, n: u64);fn lab_sc_o1_22_15_1(p: *mut u64, n: u64);fn lab_sc_o3_19_50_0(p: *mut u64, n: u64);fn lab_sc_o3_19_50_1(p: *mut u64, n: u64);fn lab_sc_o3_19_30_0(p: *mut u64, n: u64);fn lab_sc_o3_19_30_1(p: *mut u64, n: u64);fn lab_sc_o3_19_15_0(p: *mut u64, n: u64);fn lab_sc_o3_19_15_1(p: *mut u64, n: u64);fn lab_sc_o3_21_30_0(p: *mut u64, n: u64);fn lab_sc_o3_21_30_1(p: *mut u64, n: u64);fn lab_sc_o3_21_15_0(p: *mut u64, n: u64);fn lab_sc_o3_21_15_1(p: *mut u64, n: u64);fn lab_sc_o3_22_30_0(p: *mut u64, n: u64);fn lab_sc_o3_22_30_1(p: *mut u64, n: u64);fn lab_sc_o3_22_15_0(p: *mut u64, n: u64);fn lab_sc_o3_22_15_1(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_st_o3"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_st_o3(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_src"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_src(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_50_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_50_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_50_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_50_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_19_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_19_15_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_21_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_21_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_21_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_21_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_21_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_21_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_21_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_21_15_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_22_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_22_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_22_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_22_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_22_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_22_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o1_22_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o1_22_15_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_50_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_50_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_50_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_50_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_19_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_19_15_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_21_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_21_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_21_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_21_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_21_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_21_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_21_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_21_15_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_22_30_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_22_30_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_22_30_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_22_30_1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_22_15_0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_22_15_0(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sc_o3_22_15_1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sc_o3_22_15_1(p, 100) })); g.finish();
}