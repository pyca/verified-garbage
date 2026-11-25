//! Lab.
use criterion::{BenchmarkId, Criterion};
use crate::{BenchDyn, VG};
pub const USES: &[&str] = &["x25519"];
core::arch::global_asm!(r".p2align 6
.globl lab_clk_add100
lab_clk_add100:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
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
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret

.p2align 6
.globl lab_st_o3
lab_st_o3:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
mov x25, x1
mov x26, x1
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
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret

.p2align 6
.globl lab_sq2
lab_sq2:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
mov x25, x1
mov x26, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
ldr q31, [x0, #720]
ldr q28, [x0, #208]
ldr q29, [x0, #256]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v0.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v1.4s, v29.4s, v28.4s
ldr q28, [x0, #224]
ldr q29, [x0, #272]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v2.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v3.4s, v29.4s, v28.4s
ldr q28, [x0, #240]
ldr q29, [x0, #288]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v4.4s, v29.4s, v30.4s
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
ext v7.16b, v2.16b, v2.16b, #8
ext v8.16b, v3.16b, v3.16b, #8
ext v9.16b, v4.16b, v4.16b, #8
add v10.4s, v0.4s, v0.4s
add v11.4s, v1.4s, v1.4s
add v12.4s, v2.4s, v2.4s
add v13.4s, v3.4s, v3.4s
add v14.4s, v4.4s, v4.4s
ldr q31, [x0, #752]
mul v15.4s, v0.4s, v31.4s
mul v16.4s, v1.4s, v31.4s
mul v17.4s, v2.4s, v31.4s
mul v18.4s, v3.4s, v31.4s
mul v19.4s, v4.4s, v31.4s
umull2 v20.2d, v10.4s, v19.4s
umlal2 v20.2d, v11.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
add v20.2d, v20.2d, v20.2d
umlal v20.2d, v0.2s, v0.2s
umlal v20.2d, v11.2s, v19.2s
umlal v20.2d, v12.2s, v18.2s
add v30.4s, v5.4s, v5.4s
umull v25.2d, v30.2s, v0.2s
add v30.4s, v6.4s, v6.4s
umlal v25.2d, v30.2s, v19.2s
umlal2 v25.2d, v30.4s, v19.4s
add v30.4s, v7.4s, v7.4s
umlal v25.2d, v30.2s, v18.2s
umlal2 v25.2d, v30.4s, v18.4s
umull2 v21.2d, v0.4s, v0.4s
umlal2 v21.2d, v11.4s, v19.4s
umlal2 v21.2d, v12.4s, v18.4s
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umlal v21.2d, v12.2s, v19.2s
umlal v21.2d, v3.2s, v18.2s
add v30.4s, v5.4s, v5.4s
umull v26.2d, v30.2s, v1.2s
umlal2 v26.2d, v30.4s, v1.4s
add v30.4s, v7.4s, v7.4s
umlal v26.2d, v30.2s, v19.2s
umlal2 v26.2d, v30.4s, v19.4s
add v30.4s, v8.4s, v8.4s
umlal v26.2d, v30.2s, v18.2s
umull2 v22.2d, v10.4s, v1.4s
umlal2 v22.2d, v12.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
add v22.2d, v22.2d, v22.2d
umlal v22.2d, v10.2s, v2.2s
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
add v30.4s, v5.4s, v5.4s
umull v27.2d, v30.2s, v2.2s
umlal2 v27.2d, v30.4s, v2.4s
add v30.4s, v6.4s, v6.4s
umlal v27.2d, v30.2s, v1.2s
add v30.4s, v8.4s, v8.4s
umlal v27.2d, v30.2s, v19.2s
umlal2 v27.2d, v30.4s, v19.4s
umull2 v23.2d, v10.4s, v2.4s
umlal2 v23.2d, v1.4s, v1.4s
umlal2 v23.2d, v13.4s, v19.4s
add v23.2d, v23.2d, v23.2d
umlal v23.2d, v10.2s, v3.2s
umlal v23.2d, v11.2s, v2.2s
umlal v23.2d, v4.2s, v19.2s
add v30.4s, v5.4s, v5.4s
umull v28.2d, v30.2s, v3.2s
umlal2 v28.2d, v30.4s, v3.4s
add v30.4s, v6.4s, v6.4s
umlal v28.2d, v30.2s, v2.2s
umlal2 v28.2d, v30.4s, v2.4s
add v30.4s, v9.4s, v9.4s
umlal v28.2d, v30.2s, v19.2s
umull2 v24.2d, v10.4s, v3.4s
umlal2 v24.2d, v11.4s, v2.4s
umlal2 v24.2d, v4.4s, v19.4s
add v24.2d, v24.2d, v24.2d
umlal v24.2d, v10.2s, v4.2s
umlal v24.2d, v11.2s, v3.2s
umlal v24.2d, v2.2s, v2.2s
add v30.4s, v5.4s, v5.4s
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
add v30.4s, v6.4s, v6.4s
umlal v29.2d, v30.2s, v3.2s
umlal2 v29.2d, v30.4s, v3.4s
add v30.4s, v7.4s, v7.4s
umlal v29.2d, v30.2s, v2.2s
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v29.2d, #25
and v29.16b, v29.16b, v4.16b
ushr v0.2d, v24.2d, #26
and v24.16b, v24.16b, v3.16b
add v29.2d, v29.2d, v0.2d
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
add v24.2d, v24.2d, v1.2d
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v23.2d, v23.2d, v1.2d
ushr v0.2d, v22.2d, #26
and v22.16b, v22.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v22.2d, v22.2d, v1.2d
ushr v0.2d, v21.2d, #26
and v21.16b, v21.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
and v20.16b, v20.16b, v3.16b
add v25.2d, v25.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v25.2d, v25.2d, #26
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
add v22.2d, v22.2d, v27.2d
shl v28.2d, v28.2d, #26
add v23.2d, v23.2d, v28.2d
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
ldr q5, [x0, #704]
ushr v25.2d, v20.2d, #51
and v20.16b, v20.16b, v5.16b
ushr v26.2d, v21.2d, #51
and v21.16b, v21.16b, v5.16b
ushr v27.2d, v22.2d, #51
and v22.16b, v22.16b, v5.16b
ushr v28.2d, v23.2d, #51
and v23.16b, v23.16b, v5.16b
ushr v29.2d, v24.2d, #51
and v24.16b, v24.16b, v5.16b
add v21.2d, v21.2d, v25.2d
add v22.2d, v22.2d, v26.2d
add v23.2d, v23.2d, v27.2d
add v24.2d, v24.2d, v28.2d
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
shl v2.2d, v29.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
trn1 v0.2d, v20.2d, v21.2d
trn2 v1.2d, v20.2d, v21.2d
str q0, [x0, #400]
str q1, [x0, #448]
trn1 v0.2d, v22.2d, v23.2d
trn2 v1.2d, v22.2d, v23.2d
str q0, [x0, #416]
str q1, [x0, #464]
trn1 v0.2d, v24.2d, v24.2d
trn2 v1.2d, v24.2d, v24.2d
str q0, [x0, #432]
str q1, [x0, #480]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret

.p2align 6
.globl lab_mu2
lab_mu2:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
mov x25, x1
mov x26, x1
mov x2, #12345
movk x2, #54321, lsl #48
mov x3, #777
movk x3, #999, lsl #32
2:
ldr q31, [x0, #720]
ldr q28, [x0, #208]
ldr q29, [x0, #304]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v0.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v1.4s, v29.4s, v28.4s
ldr q28, [x0, #224]
ldr q29, [x0, #320]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v2.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v3.4s, v29.4s, v28.4s
ldr q28, [x0, #240]
ldr q29, [x0, #336]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v4.4s, v29.4s, v30.4s
ldr q28, [x0, #256]
ldr q29, [x0, #352]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v10.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v11.4s, v29.4s, v28.4s
ldr q28, [x0, #272]
ldr q29, [x0, #368]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v12.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v13.4s, v29.4s, v28.4s
ldr q28, [x0, #288]
ldr q29, [x0, #384]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v14.4s, v29.4s, v30.4s
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
ext v7.16b, v2.16b, v2.16b, #8
ext v8.16b, v3.16b, v3.16b, #8
ext v9.16b, v4.16b, v4.16b, #8
ldr q31, [x0, #752]
mul v15.4s, v10.4s, v31.4s
mul v16.4s, v11.4s, v31.4s
mul v17.4s, v12.4s, v31.4s
mul v18.4s, v13.4s, v31.4s
mul v19.4s, v14.4s, v31.4s
umull2 v20.2d, v0.4s, v19.4s
umlal2 v20.2d, v1.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
umlal2 v20.2d, v3.4s, v16.4s
umlal2 v20.2d, v4.4s, v15.4s
add v20.2d, v20.2d, v20.2d
umlal v20.2d, v0.2s, v10.2s
umlal v20.2d, v1.2s, v19.2s
umlal v20.2d, v2.2s, v18.2s
umlal v20.2d, v3.2s, v17.2s
umlal v20.2d, v4.2s, v16.2s
umull v25.2d, v5.2s, v10.2s
umlal2 v25.2d, v5.4s, v10.4s
umlal v25.2d, v6.2s, v19.2s
umlal2 v25.2d, v6.4s, v19.4s
umlal v25.2d, v7.2s, v18.2s
umlal2 v25.2d, v7.4s, v18.4s
umlal v25.2d, v8.2s, v17.2s
umlal2 v25.2d, v8.4s, v17.4s
umlal v25.2d, v9.2s, v16.2s
umlal2 v25.2d, v9.4s, v16.4s
umull2 v21.2d, v0.4s, v10.4s
umlal2 v21.2d, v1.4s, v19.4s
umlal2 v21.2d, v2.4s, v18.4s
umlal2 v21.2d, v3.4s, v17.4s
umlal2 v21.2d, v4.4s, v16.4s
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v0.2s, v11.2s
umlal v21.2d, v1.2s, v10.2s
umlal v21.2d, v2.2s, v19.2s
umlal v21.2d, v3.2s, v18.2s
umlal v21.2d, v4.2s, v17.2s
umull v26.2d, v5.2s, v11.2s
umlal2 v26.2d, v5.4s, v11.4s
umlal v26.2d, v6.2s, v10.2s
umlal2 v26.2d, v6.4s, v10.4s
umlal v26.2d, v7.2s, v19.2s
umlal2 v26.2d, v7.4s, v19.4s
umlal v26.2d, v8.2s, v18.2s
umlal2 v26.2d, v8.4s, v18.4s
umlal v26.2d, v9.2s, v17.2s
umlal2 v26.2d, v9.4s, v17.4s
umull2 v22.2d, v0.4s, v11.4s
umlal2 v22.2d, v1.4s, v10.4s
umlal2 v22.2d, v2.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
umlal2 v22.2d, v4.4s, v17.4s
add v22.2d, v22.2d, v22.2d
umlal v22.2d, v0.2s, v12.2s
umlal v22.2d, v1.2s, v11.2s
umlal v22.2d, v2.2s, v10.2s
umlal v22.2d, v3.2s, v19.2s
umlal v22.2d, v4.2s, v18.2s
umull v27.2d, v5.2s, v12.2s
umlal2 v27.2d, v5.4s, v12.4s
umlal v27.2d, v6.2s, v11.2s
umlal2 v27.2d, v6.4s, v11.4s
umlal v27.2d, v7.2s, v10.2s
umlal2 v27.2d, v7.4s, v10.4s
umlal v27.2d, v8.2s, v19.2s
umlal2 v27.2d, v8.4s, v19.4s
umlal v27.2d, v9.2s, v18.2s
umlal2 v27.2d, v9.4s, v18.4s
umull2 v23.2d, v0.4s, v12.4s
umlal2 v23.2d, v1.4s, v11.4s
umlal2 v23.2d, v2.4s, v10.4s
umlal2 v23.2d, v3.4s, v19.4s
umlal2 v23.2d, v4.4s, v18.4s
add v23.2d, v23.2d, v23.2d
umlal v23.2d, v0.2s, v13.2s
umlal v23.2d, v1.2s, v12.2s
umlal v23.2d, v2.2s, v11.2s
umlal v23.2d, v3.2s, v10.2s
umlal v23.2d, v4.2s, v19.2s
umull v28.2d, v5.2s, v13.2s
umlal2 v28.2d, v5.4s, v13.4s
umlal v28.2d, v6.2s, v12.2s
umlal2 v28.2d, v6.4s, v12.4s
umlal v28.2d, v7.2s, v11.2s
umlal2 v28.2d, v7.4s, v11.4s
umlal v28.2d, v8.2s, v10.2s
umlal2 v28.2d, v8.4s, v10.4s
umlal v28.2d, v9.2s, v19.2s
umlal2 v28.2d, v9.4s, v19.4s
umull2 v24.2d, v0.4s, v13.4s
umlal2 v24.2d, v1.4s, v12.4s
umlal2 v24.2d, v2.4s, v11.4s
umlal2 v24.2d, v3.4s, v10.4s
umlal2 v24.2d, v4.4s, v19.4s
add v24.2d, v24.2d, v24.2d
umlal v24.2d, v0.2s, v14.2s
umlal v24.2d, v1.2s, v13.2s
umlal v24.2d, v2.2s, v12.2s
umlal v24.2d, v3.2s, v11.2s
umlal v24.2d, v4.2s, v10.2s
umull v29.2d, v5.2s, v14.2s
umlal2 v29.2d, v5.4s, v14.4s
umlal v29.2d, v6.2s, v13.2s
umlal2 v29.2d, v6.4s, v13.4s
umlal v29.2d, v7.2s, v12.2s
umlal2 v29.2d, v7.4s, v12.4s
umlal v29.2d, v8.2s, v11.2s
umlal2 v29.2d, v8.4s, v11.4s
umlal v29.2d, v9.2s, v10.2s
umlal2 v29.2d, v9.4s, v10.4s
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v29.2d, #25
and v29.16b, v29.16b, v4.16b
ushr v0.2d, v24.2d, #26
and v24.16b, v24.16b, v3.16b
add v29.2d, v29.2d, v0.2d
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
add v24.2d, v24.2d, v1.2d
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v23.2d, v23.2d, v1.2d
ushr v0.2d, v22.2d, #26
and v22.16b, v22.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v22.2d, v22.2d, v1.2d
ushr v0.2d, v21.2d, #26
and v21.16b, v21.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
and v20.16b, v20.16b, v3.16b
add v25.2d, v25.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v25.2d, v25.2d, #26
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
add v22.2d, v22.2d, v27.2d
shl v28.2d, v28.2d, #26
add v23.2d, v23.2d, v28.2d
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
ldr q5, [x0, #704]
ushr v25.2d, v20.2d, #51
and v20.16b, v20.16b, v5.16b
ushr v26.2d, v21.2d, #51
and v21.16b, v21.16b, v5.16b
ushr v27.2d, v22.2d, #51
and v22.16b, v22.16b, v5.16b
ushr v28.2d, v23.2d, #51
and v23.16b, v23.16b, v5.16b
ushr v29.2d, v24.2d, #51
and v24.16b, v24.16b, v5.16b
add v21.2d, v21.2d, v25.2d
add v22.2d, v22.2d, v26.2d
add v23.2d, v23.2d, v27.2d
add v24.2d, v24.2d, v28.2d
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
shl v2.2d, v29.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
trn1 v0.2d, v20.2d, v21.2d
trn2 v1.2d, v20.2d, v21.2d
str q0, [x0, #16]
str q1, [x0, #64]
trn1 v0.2d, v22.2d, v23.2d
trn2 v1.2d, v22.2d, v23.2d
str q0, [x0, #32]
str q1, [x0, #80]
trn1 v0.2d, v24.2d, v24.2d
trn2 v1.2d, v24.2d, v24.2d
str q0, [x0, #48]
str q1, [x0, #96]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret

.p2align 6
.globl lab_sn1
lab_sn1:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
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
ldr x1, [x0, #16]
ldr x2, [x0, #64]
ldr x3, [x0, #112]
ldr x4, [x0, #160]
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
str x9, [x0, #208]
str x5, [x0, #256]
str x10, [x0, #304]
str x7, [x0, #352]
ldr x1, [x0, #24]
ldr x2, [x0, #72]
ldr x3, [x0, #120]
ldr x4, [x0, #168]
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
str x9, [x0, #216]
str x5, [x0, #264]
str x10, [x0, #312]
str x7, [x0, #360]
ldr x1, [x0, #32]
ldr x2, [x0, #80]
ldr x3, [x0, #128]
ldr x4, [x0, #176]
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
str x9, [x0, #224]
str x5, [x0, #272]
str x10, [x0, #320]
str x7, [x0, #368]
ldr x1, [x0, #40]
ldr x2, [x0, #88]
ldr x3, [x0, #136]
ldr x4, [x0, #184]
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
str x9, [x0, #232]
str x5, [x0, #280]
str x10, [x0, #328]
str x7, [x0, #376]
ldr x1, [x0, #48]
ldr x2, [x0, #96]
ldr x3, [x0, #144]
ldr x4, [x0, #192]
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
str x9, [x0, #240]
str x5, [x0, #288]
str x10, [x0, #336]
str x7, [x0, #384]
ldp x1, x2, [x0, #208]
ldr q31, [x0, #720]
ldp x3, x4, [x0, #224]
ldr q28, [x0, #208]
ldr x5, [x0, #240]
ldr q29, [x0, #256]
mov w22, #19
mul x6, x2, x22
trn1 v30.2d, v28.2d, v29.2d
mul x7, x3, x22
trn2 v28.2d, v28.2d, v29.2d
mul x8, x4, x22
mul x9, x5, x22
and v29.16b, v30.16b, v31.16b
ldr x22, [x0, #352]
ushr v30.2d, v30.2d, #26
mul x10, x22, x1
umulh x11, x22, x1
uzp1 v0.4s, v29.4s, v30.4s
mul x12, x22, x2
and v29.16b, v28.16b, v31.16b
umulh x13, x22, x2
mul x14, x22, x3
ushr v28.2d, v28.2d, #26
umulh x15, x22, x3
uzp1 v1.4s, v29.4s, v28.4s
mul x16, x22, x4
umulh x17, x22, x4
ldr q28, [x0, #224]
mul x20, x22, x5
ldr q29, [x0, #272]
umulh x21, x22, x5
trn1 v30.2d, v28.2d, v29.2d
ldr x22, [x0, #360]
mul x23, x22, x1
trn2 v28.2d, v28.2d, v29.2d
umulh x24, x22, x1
and v29.16b, v30.16b, v31.16b
adds x12, x12, x23
adc x13, x13, x24
ushr v30.2d, v30.2d, #26
mul x23, x22, x2
uzp1 v2.4s, v29.4s, v30.4s
umulh x24, x22, x2
adds x14, x14, x23
and v29.16b, v28.16b, v31.16b
adc x15, x15, x24
ushr v28.2d, v28.2d, #26
mul x23, x22, x3
umulh x24, x22, x3
uzp1 v3.4s, v29.4s, v28.4s
adds x16, x16, x23
ldr q28, [x0, #240]
adc x17, x17, x24
mul x23, x22, x4
ldr q29, [x0, #288]
umulh x24, x22, x4
trn1 v30.2d, v28.2d, v29.2d
adds x20, x20, x23
adc x21, x21, x24
and v29.16b, v30.16b, v31.16b
mul x23, x22, x9
ushr v30.2d, v30.2d, #26
umulh x24, x22, x9
uzp1 v4.4s, v29.4s, v30.4s
adds x10, x10, x23
adc x11, x11, x24
ext v5.16b, v0.16b, v0.16b, #8
ldr x22, [x0, #368]
ext v6.16b, v1.16b, v1.16b, #8
mul x23, x22, x1
umulh x24, x22, x1
ext v7.16b, v2.16b, v2.16b, #8
adds x14, x14, x23
ext v8.16b, v3.16b, v3.16b, #8
adc x15, x15, x24
mul x23, x22, x2
ext v9.16b, v4.16b, v4.16b, #8
umulh x24, x22, x2
add v10.4s, v0.4s, v0.4s
adds x16, x16, x23
adc x17, x17, x24
add v11.4s, v1.4s, v1.4s
mul x23, x22, x3
add v12.4s, v2.4s, v2.4s
umulh x24, x22, x3
adds x20, x20, x23
add v13.4s, v3.4s, v3.4s
adc x21, x21, x24
add v14.4s, v4.4s, v4.4s
mul x23, x22, x8
ldr q31, [x0, #752]
umulh x24, x22, x8
adds x10, x10, x23
mul v15.4s, v0.4s, v31.4s
adc x11, x11, x24
mul v16.4s, v1.4s, v31.4s
mul x23, x22, x9
umulh x24, x22, x9
mul v17.4s, v2.4s, v31.4s
adds x12, x12, x23
mul v18.4s, v3.4s, v31.4s
adc x13, x13, x24
ldr x22, [x0, #376]
mul v19.4s, v4.4s, v31.4s
mul x23, x22, x1
umull2 v20.2d, v10.4s, v19.4s
umulh x24, x22, x1
adds x16, x16, x23
umlal2 v20.2d, v11.4s, v18.4s
adc x17, x17, x24
umlal2 v20.2d, v2.4s, v17.4s
mul x23, x22, x2
umulh x24, x22, x2
add v20.2d, v20.2d, v20.2d
adds x20, x20, x23
umlal v20.2d, v0.2s, v0.2s
adc x21, x21, x24
mul x23, x22, x7
umlal v20.2d, v11.2s, v19.2s
umulh x24, x22, x7
umlal v20.2d, v12.2s, v18.2s
adds x10, x10, x23
add v30.4s, v5.4s, v5.4s
adc x11, x11, x24
mul x23, x22, x8
umull v25.2d, v30.2s, v0.2s
umulh x24, x22, x8
add v30.4s, v6.4s, v6.4s
adds x12, x12, x23
adc x13, x13, x24
umlal v25.2d, v30.2s, v19.2s
mul x23, x22, x9
umlal2 v25.2d, v30.4s, v19.4s
umulh x24, x22, x9
adds x14, x14, x23
add v30.4s, v7.4s, v7.4s
adc x15, x15, x24
umlal v25.2d, v30.2s, v18.2s
ldr x22, [x0, #384]
mul x23, x22, x1
umlal2 v25.2d, v30.4s, v18.4s
umulh x24, x22, x1
umull2 v21.2d, v0.4s, v0.4s
adds x20, x20, x23
adc x21, x21, x24
umlal2 v21.2d, v11.4s, v19.4s
mul x23, x22, x6
umlal2 v21.2d, v12.4s, v18.4s
umulh x24, x22, x6
adds x10, x10, x23
add v21.2d, v21.2d, v21.2d
adc x11, x11, x24
umlal v21.2d, v10.2s, v1.2s
mul x23, x22, x7
umlal v21.2d, v12.2s, v19.2s
umulh x24, x22, x7
adds x12, x12, x23
umlal v21.2d, v3.2s, v18.2s
adc x13, x13, x24
add v30.4s, v5.4s, v5.4s
mul x23, x22, x8
umulh x24, x22, x8
umull v26.2d, v30.2s, v1.2s
adds x14, x14, x23
umlal2 v26.2d, v30.4s, v1.4s
adc x15, x15, x24
mul x23, x22, x9
add v30.4s, v7.4s, v7.4s
umulh x24, x22, x9
umlal v26.2d, v30.2s, v19.2s
adds x16, x16, x23
adc x17, x17, x24
umlal2 v26.2d, v30.4s, v19.4s
mov x1, #0xffff
add v30.4s, v8.4s, v8.4s
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
umlal v26.2d, v30.2s, v18.2s
movk x1, #7, lsl #48
umull2 v22.2d, v10.4s, v1.4s
mov w7, #19
umlal2 v22.2d, v12.4s, v19.4s
extr x2, x11, x10, #51
extr x3, x13, x12, #51
umlal2 v22.2d, v3.4s, v18.4s
extr x4, x15, x14, #51
add v22.2d, v22.2d, v22.2d
extr x5, x17, x16, #51
extr x6, x21, x20, #51
umlal v22.2d, v10.2s, v2.2s
and x10, x10, x1
umlal v22.2d, v1.2s, v1.2s
and x12, x12, x1
and x14, x14, x1
umlal v22.2d, v13.2s, v19.2s
and x16, x16, x1
add v30.4s, v5.4s, v5.4s
and x20, x20, x1
mul x6, x6, x7
umull v27.2d, v30.2s, v2.2s
add x10, x10, x6
umlal2 v27.2d, v30.4s, v2.4s
add x12, x12, x2
add x14, x14, x3
add v30.4s, v6.4s, v6.4s
add x16, x16, x4
umlal v27.2d, v30.2s, v1.2s
add x20, x20, x5
lsr x2, x10, #51
add v30.4s, v8.4s, v8.4s
lsr x3, x12, #51
umlal v27.2d, v30.2s, v19.2s
lsr x4, x14, #51
umlal2 v27.2d, v30.4s, v19.4s
lsr x5, x16, #51
lsr x6, x20, #51
umull2 v23.2d, v10.4s, v2.4s
and x10, x10, x1
umlal2 v23.2d, v1.4s, v1.4s
and x12, x12, x1
and x14, x14, x1
umlal2 v23.2d, v13.4s, v19.4s
and x16, x16, x1
add v23.2d, v23.2d, v23.2d
and x20, x20, x1
mul x6, x6, x7
umlal v23.2d, v10.2s, v3.2s
add x10, x10, x6
umlal v23.2d, v11.2s, v2.2s
add x12, x12, x2
add x14, x14, x3
umlal v23.2d, v4.2s, v19.2s
add x16, x16, x4
add v30.4s, v5.4s, v5.4s
add x20, x20, x5
stp x10, x12, [x0, #352]
umull v28.2d, v30.2s, v3.2s
stp x14, x16, [x0, #368]
umlal2 v28.2d, v30.4s, v3.4s
str x20, [x0, #384]
ldp x1, x2, [x0, #256]
add v30.4s, v6.4s, v6.4s
ldp x3, x4, [x0, #272]
umlal v28.2d, v30.2s, v2.2s
ldr x5, [x0, #288]
umlal2 v28.2d, v30.4s, v2.4s
mov w22, #19
mul x6, x2, x22
add v30.4s, v9.4s, v9.4s
mul x7, x3, x22
umlal v28.2d, v30.2s, v19.2s
mul x8, x4, x22
mul x9, x5, x22
umull2 v24.2d, v10.4s, v3.4s
ldr x22, [x0, #304]
umlal2 v24.2d, v11.4s, v2.4s
mul x10, x22, x1
umulh x11, x22, x1
umlal2 v24.2d, v4.4s, v19.4s
mul x12, x22, x2
add v24.2d, v24.2d, v24.2d
umulh x13, x22, x2
mul x14, x22, x3
umlal v24.2d, v10.2s, v4.2s
umulh x15, x22, x3
umlal v24.2d, v11.2s, v3.2s
mul x16, x22, x4
umulh x17, x22, x4
umlal v24.2d, v2.2s, v2.2s
mul x20, x22, x5
add v30.4s, v5.4s, v5.4s
umulh x21, x22, x5
umull v29.2d, v30.2s, v4.2s
ldr x22, [x0, #312]
mul x23, x22, x1
umlal2 v29.2d, v30.4s, v4.4s
umulh x24, x22, x1
add v30.4s, v6.4s, v6.4s
adds x12, x12, x23
adc x13, x13, x24
umlal v29.2d, v30.2s, v3.2s
mul x23, x22, x2
umlal2 v29.2d, v30.4s, v3.4s
umulh x24, x22, x2
adds x14, x14, x23
add v30.4s, v7.4s, v7.4s
adc x15, x15, x24
umlal v29.2d, v30.2s, v2.2s
mul x23, x22, x3
umulh x24, x22, x3
ldr q3, [x0, #720]
adds x16, x16, x23
ldr q4, [x0, #736]
adc x17, x17, x24
mul x23, x22, x4
ushr v2.2d, v29.2d, #25
umulh x24, x22, x4
and v29.16b, v29.16b, v4.16b
adds x20, x20, x23
adc x21, x21, x24
ushr v0.2d, v24.2d, #26
mul x23, x22, x9
and v24.16b, v24.16b, v3.16b
umulh x24, x22, x9
add v29.2d, v29.2d, v0.2d
adds x10, x10, x23
adc x11, x11, x24
ushr v1.2d, v28.2d, #25
ldr x22, [x0, #320]
and v28.16b, v28.16b, v4.16b
mul x23, x22, x1
umulh x24, x22, x1
add v24.2d, v24.2d, v1.2d
adds x14, x14, x23
ushr v0.2d, v23.2d, #26
adc x15, x15, x24
mul x23, x22, x2
and v23.16b, v23.16b, v3.16b
umulh x24, x22, x2
add v28.2d, v28.2d, v0.2d
adds x16, x16, x23
adc x17, x17, x24
ushr v1.2d, v27.2d, #25
mul x23, x22, x3
and v27.16b, v27.16b, v4.16b
umulh x24, x22, x3
adds x20, x20, x23
add v23.2d, v23.2d, v1.2d
adc x21, x21, x24
ushr v0.2d, v22.2d, #26
mul x23, x22, x8
and v22.16b, v22.16b, v3.16b
umulh x24, x22, x8
adds x10, x10, x23
add v27.2d, v27.2d, v0.2d
adc x11, x11, x24
ushr v1.2d, v26.2d, #25
mul x23, x22, x9
umulh x24, x22, x9
and v26.16b, v26.16b, v4.16b
adds x12, x12, x23
add v22.2d, v22.2d, v1.2d
adc x13, x13, x24
ldr x22, [x0, #328]
ushr v0.2d, v21.2d, #26
mul x23, x22, x1
and v21.16b, v21.16b, v3.16b
umulh x24, x22, x1
adds x16, x16, x23
add v26.2d, v26.2d, v0.2d
adc x17, x17, x24
ushr v1.2d, v25.2d, #25
mul x23, x22, x2
umulh x24, x22, x2
and v25.16b, v25.16b, v4.16b
adds x20, x20, x23
add v21.2d, v21.2d, v1.2d
adc x21, x21, x24
mul x23, x22, x7
ushr v0.2d, v20.2d, #26
umulh x24, x22, x7
and v20.16b, v20.16b, v3.16b
adds x10, x10, x23
add v25.2d, v25.2d, v0.2d
adc x11, x11, x24
mul x23, x22, x8
add v20.2d, v20.2d, v2.2d
umulh x24, x22, x8
shl v0.2d, v2.2d, #1
adds x12, x12, x23
adc x13, x13, x24
shl v2.2d, v2.2d, #4
mul x23, x22, x9
add v20.2d, v20.2d, v0.2d
umulh x24, x22, x9
adds x14, x14, x23
add v20.2d, v20.2d, v2.2d
adc x15, x15, x24
shl v25.2d, v25.2d, #26
ldr x22, [x0, #336]
mul x23, x22, x1
add v20.2d, v20.2d, v25.2d
umulh x24, x22, x1
shl v26.2d, v26.2d, #26
adds x20, x20, x23
adc x21, x21, x24
add v21.2d, v21.2d, v26.2d
mul x23, x22, x6
shl v27.2d, v27.2d, #26
umulh x24, x22, x6
adds x10, x10, x23
add v22.2d, v22.2d, v27.2d
adc x11, x11, x24
shl v28.2d, v28.2d, #26
mul x23, x22, x7
add v23.2d, v23.2d, v28.2d
umulh x24, x22, x7
adds x12, x12, x23
shl v29.2d, v29.2d, #26
adc x13, x13, x24
add v24.2d, v24.2d, v29.2d
mul x23, x22, x8
umulh x24, x22, x8
ldr q5, [x0, #704]
adds x14, x14, x23
ushr v25.2d, v20.2d, #51
adc x15, x15, x24
mul x23, x22, x9
and v20.16b, v20.16b, v5.16b
umulh x24, x22, x9
ushr v26.2d, v21.2d, #51
adds x16, x16, x23
adc x17, x17, x24
and v21.16b, v21.16b, v5.16b
mov x1, #0xffff
ushr v27.2d, v22.2d, #51
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
and v22.16b, v22.16b, v5.16b
movk x1, #7, lsl #48
ushr v28.2d, v23.2d, #51
mov w7, #19
and v23.16b, v23.16b, v5.16b
extr x2, x11, x10, #51
extr x3, x13, x12, #51
ushr v29.2d, v24.2d, #51
extr x4, x15, x14, #51
and v24.16b, v24.16b, v5.16b
extr x5, x17, x16, #51
extr x6, x21, x20, #51
add v21.2d, v21.2d, v25.2d
and x10, x10, x1
add v22.2d, v22.2d, v26.2d
and x12, x12, x1
and x14, x14, x1
add v23.2d, v23.2d, v27.2d
and x16, x16, x1
add v24.2d, v24.2d, v28.2d
and x20, x20, x1
mul x6, x6, x7
add v20.2d, v20.2d, v29.2d
add x10, x10, x6
shl v0.2d, v29.2d, #1
add x12, x12, x2
add x14, x14, x3
shl v2.2d, v29.2d, #4
add x16, x16, x4
add v20.2d, v20.2d, v0.2d
add x20, x20, x5
lsr x2, x10, #51
add v20.2d, v20.2d, v2.2d
lsr x3, x12, #51
trn1 v0.2d, v20.2d, v21.2d
lsr x4, x14, #51
trn2 v1.2d, v20.2d, v21.2d
lsr x5, x16, #51
lsr x6, x20, #51
str q0, [x0, #400]
and x10, x10, x1
str q1, [x0, #448]
and x12, x12, x1
and x14, x14, x1
trn1 v0.2d, v22.2d, v23.2d
and x16, x16, x1
trn2 v1.2d, v22.2d, v23.2d
and x20, x20, x1
mul x6, x6, x7
str q0, [x0, #416]
add x10, x10, x6
str q1, [x0, #464]
add x12, x12, x2
add x14, x14, x3
trn1 v0.2d, v24.2d, v24.2d
add x16, x16, x4
trn2 v1.2d, v24.2d, v24.2d
add x20, x20, x5
stp x10, x12, [x0, #304]
str q0, [x0, #432]
stp x14, x16, [x0, #320]
str q1, [x0, #480]
str x20, [x0, #336]
ldp x1, x2, [x0, #400]
ldp x3, x4, [x0, #416]
ldr x5, [x0, #432]
ldp x6, x7, [x0, #448]
ldp x8, x9, [x0, #464]
ldr x10, [x0, #480]
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
movk x24, #0xf, lsl #48
sub x23, x24, #36
sub x6, x1, x6
add x6, x6, x23
sub x7, x2, x7
add x7, x7, x24
sub x8, x3, x8
add x8, x8, x24
sub x9, x4, x9
add x9, x9, x24
sub x10, x5, x10
add x10, x10, x24
str x6, [x0, #608]
str x7, [x0, #616]
str x8, [x0, #624]
str x9, [x0, #632]
str x10, [x0, #640]
mov w16, #0xdb41
movk w16, #1, lsl #16
mov x17, #0xffff
movk x17, #0xffff, lsl #16
movk x17, #0xffff, lsl #32
movk x17, #7, lsl #48
umulh x11, x6, x16
umulh x12, x7, x16
umulh x13, x8, x16
umulh x14, x9, x16
umulh x15, x10, x16
mul x6, x6, x16
mul x7, x7, x16
mul x8, x8, x16
mul x9, x9, x16
mul x10, x10, x16
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
str x1, [x0, #656]
str x2, [x0, #664]
str x3, [x0, #672]
str x4, [x0, #680]
str x5, [x0, #688]
ldp x1, x2, [x0, #352]
ldr q31, [x0, #720]
ldp x3, x4, [x0, #368]
ldr q28, [x0, #400]
ldr x5, [x0, #384]
ldr q29, [x0, #608]
ldp x6, x7, [x0, #304]
ldp x8, x9, [x0, #320]
trn1 v30.2d, v28.2d, v29.2d
ldr x10, [x0, #336]
trn2 v28.2d, v28.2d, v29.2d
add x1, x1, x6
add x2, x2, x7
and v29.16b, v30.16b, v31.16b
add x3, x3, x8
ushr v30.2d, v30.2d, #26
add x4, x4, x9
add x5, x5, x10
uzp1 v0.4s, v29.4s, v30.4s
mov w22, #19
and v29.16b, v28.16b, v31.16b
add x6, x1, x1
add x7, x2, x2
ushr v28.2d, v28.2d, #26
mul x8, x4, x22
uzp1 v1.4s, v29.4s, v28.4s
mul x9, x5, x22
add x24, x9, x9
ldr q28, [x0, #416]
mul x10, x1, x1
ldr q29, [x0, #624]
umulh x11, x1, x1
mul x12, x6, x2
trn1 v30.2d, v28.2d, v29.2d
umulh x13, x6, x2
trn2 v28.2d, v28.2d, v29.2d
mul x14, x6, x3
umulh x15, x6, x3
and v29.16b, v30.16b, v31.16b
mul x16, x6, x4
ushr v30.2d, v30.2d, #26
umulh x17, x6, x4
mul x20, x6, x5
uzp1 v2.4s, v29.4s, v30.4s
umulh x21, x6, x5
and v29.16b, v28.16b, v31.16b
mul x22, x2, x24
umulh x23, x2, x24
ushr v28.2d, v28.2d, #26
adds x10, x10, x22
uzp1 v3.4s, v29.4s, v28.4s
adc x11, x11, x23
mul x22, x2, x2
ldr q28, [x0, #432]
umulh x23, x2, x2
ldr q29, [x0, #640]
adds x14, x14, x22
adc x15, x15, x23
trn1 v30.2d, v28.2d, v29.2d
mul x22, x7, x3
and v29.16b, v30.16b, v31.16b
umulh x23, x7, x3
adds x16, x16, x22
ushr v30.2d, v30.2d, #26
adc x17, x17, x23
uzp1 v4.4s, v29.4s, v30.4s
mul x22, x7, x4
umulh x23, x7, x4
ldr q28, [x0, #448]
adds x20, x20, x22
ldr q29, [x0, #656]
adc x21, x21, x23
mul x22, x3, x24
trn1 v30.2d, v28.2d, v29.2d
umulh x23, x3, x24
trn2 v28.2d, v28.2d, v29.2d
adds x12, x12, x22
adc x13, x13, x23
and v29.16b, v30.16b, v31.16b
mul x22, x3, x3
ushr v30.2d, v30.2d, #26
umulh x23, x3, x3
adds x20, x20, x22
uzp1 v10.4s, v29.4s, v30.4s
adc x21, x21, x23
and v29.16b, v28.16b, v31.16b
mul x22, x4, x24
umulh x23, x4, x24
ushr v28.2d, v28.2d, #26
adds x14, x14, x22
uzp1 v11.4s, v29.4s, v28.4s
adc x15, x15, x23
mul x22, x5, x9
ldr q28, [x0, #464]
umulh x23, x5, x9
ldr q29, [x0, #672]
adds x16, x16, x22
adc x17, x17, x23
trn1 v30.2d, v28.2d, v29.2d
mul x22, x4, x8
trn2 v28.2d, v28.2d, v29.2d
umulh x23, x4, x8
adds x12, x12, x22
and v29.16b, v30.16b, v31.16b
adc x13, x13, x23
ushr v30.2d, v30.2d, #26
add x8, x8, x8
mul x22, x8, x3
uzp1 v12.4s, v29.4s, v30.4s
umulh x23, x8, x3
and v29.16b, v28.16b, v31.16b
adds x10, x10, x22
adc x11, x11, x23
ushr v28.2d, v28.2d, #26
mov x1, #0xffff
uzp1 v13.4s, v29.4s, v28.4s
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
ldr q28, [x0, #480]
movk x1, #7, lsl #48
ldr q29, [x0, #688]
mov w7, #19
extr x2, x11, x10, #51
trn1 v30.2d, v28.2d, v29.2d
extr x3, x13, x12, #51
and v29.16b, v30.16b, v31.16b
extr x4, x15, x14, #51
extr x5, x17, x16, #51
ushr v30.2d, v30.2d, #26
extr x6, x21, x20, #51
uzp1 v14.4s, v29.4s, v30.4s
and x10, x10, x1
and x12, x12, x1
ext v5.16b, v0.16b, v0.16b, #8
and x14, x14, x1
ext v6.16b, v1.16b, v1.16b, #8
and x16, x16, x1
and x20, x20, x1
ext v7.16b, v2.16b, v2.16b, #8
mul x6, x6, x7
ext v8.16b, v3.16b, v3.16b, #8
add x10, x10, x6
add x12, x12, x2
ext v9.16b, v4.16b, v4.16b, #8
add x14, x14, x3
ldr q31, [x0, #752]
add x16, x16, x4
add x20, x20, x5
mul v15.4s, v10.4s, v31.4s
lsr x2, x10, #51
mul v16.4s, v11.4s, v31.4s
lsr x3, x12, #51
lsr x4, x14, #51
mul v17.4s, v12.4s, v31.4s
lsr x5, x16, #51
mul v18.4s, v13.4s, v31.4s
lsr x6, x20, #51
and x10, x10, x1
mul v19.4s, v14.4s, v31.4s
and x12, x12, x1
umull2 v20.2d, v0.4s, v19.4s
and x14, x14, x1
and x16, x16, x1
umlal2 v20.2d, v1.4s, v18.4s
and x20, x20, x1
umlal2 v20.2d, v2.4s, v17.4s
mul x6, x6, x7
add x10, x10, x6
umlal2 v20.2d, v3.4s, v16.4s
add x12, x12, x2
umlal2 v20.2d, v4.4s, v15.4s
add x14, x14, x3
add x16, x16, x4
add v20.2d, v20.2d, v20.2d
add x20, x20, x5
umlal v20.2d, v0.2s, v10.2s
stp x10, x12, [x0, #112]
stp x14, x16, [x0, #128]
umlal v20.2d, v1.2s, v19.2s
str x20, [x0, #144]
umlal v20.2d, v2.2s, v18.2s
ldp x1, x2, [x0, #352]
ldp x3, x4, [x0, #368]
umlal v20.2d, v3.2s, v17.2s
ldr x5, [x0, #384]
umlal v20.2d, v4.2s, v16.2s
ldp x6, x7, [x0, #304]
ldp x8, x9, [x0, #320]
umull v25.2d, v5.2s, v10.2s
ldr x10, [x0, #336]
umlal2 v25.2d, v5.4s, v10.4s
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
umlal v25.2d, v6.2s, v19.2s
movk x24, #0xffff, lsl #32
umlal2 v25.2d, v6.4s, v19.4s
movk x24, #0xf, lsl #48
sub x23, x24, #36
umlal v25.2d, v7.2s, v18.2s
add x1, x1, x23
umlal2 v25.2d, v7.4s, v18.4s
sub x1, x1, x6
add x2, x2, x24
umlal v25.2d, v8.2s, v17.2s
sub x2, x2, x7
umlal2 v25.2d, v8.4s, v17.4s
add x3, x3, x24
umlal v25.2d, v9.2s, v16.2s
sub x3, x3, x8
add x4, x4, x24
umlal2 v25.2d, v9.4s, v16.4s
sub x4, x4, x9
umull2 v21.2d, v0.4s, v10.4s
add x5, x5, x24
sub x5, x5, x10
umlal2 v21.2d, v1.4s, v19.4s
mov w22, #19
umlal2 v21.2d, v2.4s, v18.4s
add x6, x1, x1
add x7, x2, x2
umlal2 v21.2d, v3.4s, v17.4s
mul x8, x4, x22
umlal2 v21.2d, v4.4s, v16.4s
mul x9, x5, x22
add x24, x9, x9
add v21.2d, v21.2d, v21.2d
mul x10, x1, x1
umlal v21.2d, v0.2s, v11.2s
umulh x11, x1, x1
mul x12, x6, x2
umlal v21.2d, v1.2s, v10.2s
umulh x13, x6, x2
umlal v21.2d, v2.2s, v19.2s
mul x14, x6, x3
umulh x15, x6, x3
umlal v21.2d, v3.2s, v18.2s
mul x16, x6, x4
umlal v21.2d, v4.2s, v17.2s
umulh x17, x6, x4
mul x20, x6, x5
umull v26.2d, v5.2s, v11.2s
umulh x21, x6, x5
umlal2 v26.2d, v5.4s, v11.4s
mul x22, x2, x24
umulh x23, x2, x24
umlal v26.2d, v6.2s, v10.2s
adds x10, x10, x22
umlal2 v26.2d, v6.4s, v10.4s
adc x11, x11, x23
mul x22, x2, x2
umlal v26.2d, v7.2s, v19.2s
umulh x23, x2, x2
umlal2 v26.2d, v7.4s, v19.4s
adds x14, x14, x22
adc x15, x15, x23
umlal v26.2d, v8.2s, v18.2s
mul x22, x7, x3
umlal2 v26.2d, v8.4s, v18.4s
umulh x23, x7, x3
adds x16, x16, x22
umlal v26.2d, v9.2s, v17.2s
adc x17, x17, x23
umlal2 v26.2d, v9.4s, v17.4s
mul x22, x7, x4
umulh x23, x7, x4
umull2 v22.2d, v0.4s, v11.4s
adds x20, x20, x22
umlal2 v22.2d, v1.4s, v10.4s
adc x21, x21, x23
mul x22, x3, x24
umlal2 v22.2d, v2.4s, v19.4s
umulh x23, x3, x24
umlal2 v22.2d, v3.4s, v18.4s
adds x12, x12, x22
adc x13, x13, x23
umlal2 v22.2d, v4.4s, v17.4s
mul x22, x3, x3
add v22.2d, v22.2d, v22.2d
umulh x23, x3, x3
adds x20, x20, x22
umlal v22.2d, v0.2s, v12.2s
adc x21, x21, x23
umlal v22.2d, v1.2s, v11.2s
mul x22, x4, x24
umulh x23, x4, x24
umlal v22.2d, v2.2s, v10.2s
adds x14, x14, x22
umlal v22.2d, v3.2s, v19.2s
adc x15, x15, x23
mul x22, x5, x9
umlal v22.2d, v4.2s, v18.2s
umulh x23, x5, x9
umull v27.2d, v5.2s, v12.2s
adds x16, x16, x22
adc x17, x17, x23
umlal2 v27.2d, v5.4s, v12.4s
mul x22, x4, x8
umlal v27.2d, v6.2s, v11.2s
umulh x23, x4, x8
adds x12, x12, x22
umlal2 v27.2d, v6.4s, v11.4s
adc x13, x13, x23
umlal v27.2d, v7.2s, v10.2s
add x8, x8, x8
mul x22, x8, x3
umlal2 v27.2d, v7.4s, v10.4s
umulh x23, x8, x3
umlal v27.2d, v8.2s, v19.2s
adds x10, x10, x22
adc x11, x11, x23
umlal2 v27.2d, v8.4s, v19.4s
mov x1, #0xffff
umlal v27.2d, v9.2s, v18.2s
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
umlal2 v27.2d, v9.4s, v18.4s
movk x1, #7, lsl #48
umull2 v23.2d, v0.4s, v12.4s
mov w7, #19
extr x2, x11, x10, #51
umlal2 v23.2d, v1.4s, v11.4s
extr x3, x13, x12, #51
umlal2 v23.2d, v2.4s, v10.4s
extr x4, x15, x14, #51
extr x5, x17, x16, #51
umlal2 v23.2d, v3.4s, v19.4s
extr x6, x21, x20, #51
umlal2 v23.2d, v4.4s, v18.4s
and x10, x10, x1
and x12, x12, x1
add v23.2d, v23.2d, v23.2d
and x14, x14, x1
umlal v23.2d, v0.2s, v13.2s
and x16, x16, x1
and x20, x20, x1
umlal v23.2d, v1.2s, v12.2s
mul x6, x6, x7
umlal v23.2d, v2.2s, v11.2s
add x10, x10, x6
add x12, x12, x2
umlal v23.2d, v3.2s, v10.2s
add x14, x14, x3
umlal v23.2d, v4.2s, v19.2s
add x16, x16, x4
add x20, x20, x5
umull v28.2d, v5.2s, v13.2s
lsr x2, x10, #51
umlal2 v28.2d, v5.4s, v13.4s
lsr x3, x12, #51
lsr x4, x14, #51
umlal v28.2d, v6.2s, v12.2s
lsr x5, x16, #51
umlal2 v28.2d, v6.4s, v12.4s
lsr x6, x20, #51
and x10, x10, x1
umlal v28.2d, v7.2s, v11.2s
and x12, x12, x1
umlal2 v28.2d, v7.4s, v11.4s
and x14, x14, x1
and x16, x16, x1
umlal v28.2d, v8.2s, v10.2s
and x20, x20, x1
umlal2 v28.2d, v8.4s, v10.4s
mul x6, x6, x7
add x10, x10, x6
umlal v28.2d, v9.2s, v19.2s
add x12, x12, x2
umlal2 v28.2d, v9.4s, v19.4s
add x14, x14, x3
add x16, x16, x4
umull2 v24.2d, v0.4s, v13.4s
add x20, x20, x5
umlal2 v24.2d, v1.4s, v12.4s
stp x10, x12, [x0, #160]
stp x14, x16, [x0, #176]
umlal2 v24.2d, v2.4s, v11.4s
str x20, [x0, #192]
umlal2 v24.2d, v3.4s, v10.4s
ldp x1, x2, [x0, #160]
ldp x3, x4, [x0, #176]
umlal2 v24.2d, v4.4s, v19.4s
ldr x5, [x0, #192]
add v24.2d, v24.2d, v24.2d
mov w22, #19
mul x6, x2, x22
umlal v24.2d, v0.2s, v14.2s
mul x7, x3, x22
umlal v24.2d, v1.2s, v13.2s
mul x8, x4, x22
mul x9, x5, x22
umlal v24.2d, v2.2s, v12.2s
ldr x22, [x0, #560]
umlal v24.2d, v3.2s, v11.2s
mul x10, x22, x1
umulh x11, x22, x1
umlal v24.2d, v4.2s, v10.2s
mul x12, x22, x2
umull v29.2d, v5.2s, v14.2s
umulh x13, x22, x2
mul x14, x22, x3
umlal2 v29.2d, v5.4s, v14.4s
umulh x15, x22, x3
umlal v29.2d, v6.2s, v13.2s
mul x16, x22, x4
umulh x17, x22, x4
umlal2 v29.2d, v6.4s, v13.4s
mul x20, x22, x5
umlal v29.2d, v7.2s, v12.2s
umulh x21, x22, x5
ldr x22, [x0, #568]
umlal2 v29.2d, v7.4s, v12.4s
mul x23, x22, x1
umlal v29.2d, v8.2s, v11.2s
umulh x24, x22, x1
umlal2 v29.2d, v8.4s, v11.4s
adds x12, x12, x23
adc x13, x13, x24
umlal v29.2d, v9.2s, v10.2s
mul x23, x22, x2
umlal2 v29.2d, v9.4s, v10.4s
umulh x24, x22, x2
adds x14, x14, x23
ldr q3, [x0, #720]
adc x15, x15, x24
ldr q4, [x0, #736]
mul x23, x22, x3
umulh x24, x22, x3
ushr v2.2d, v29.2d, #25
adds x16, x16, x23
and v29.16b, v29.16b, v4.16b
adc x17, x17, x24
mul x23, x22, x4
ushr v0.2d, v24.2d, #26
umulh x24, x22, x4
and v24.16b, v24.16b, v3.16b
adds x20, x20, x23
adc x21, x21, x24
add v29.2d, v29.2d, v0.2d
mul x23, x22, x9
ushr v1.2d, v28.2d, #25
umulh x24, x22, x9
adds x10, x10, x23
and v28.16b, v28.16b, v4.16b
adc x11, x11, x24
add v24.2d, v24.2d, v1.2d
ldr x22, [x0, #576]
mul x23, x22, x1
ushr v0.2d, v23.2d, #26
umulh x24, x22, x1
and v23.16b, v23.16b, v3.16b
adds x14, x14, x23
adc x15, x15, x24
add v28.2d, v28.2d, v0.2d
mul x23, x22, x2
ushr v1.2d, v27.2d, #25
umulh x24, x22, x2
adds x16, x16, x23
and v27.16b, v27.16b, v4.16b
adc x17, x17, x24
add v23.2d, v23.2d, v1.2d
mul x23, x22, x3
umulh x24, x22, x3
ushr v0.2d, v22.2d, #26
adds x20, x20, x23
and v22.16b, v22.16b, v3.16b
adc x21, x21, x24
mul x23, x22, x8
add v27.2d, v27.2d, v0.2d
umulh x24, x22, x8
ushr v1.2d, v26.2d, #25
adds x10, x10, x23
adc x11, x11, x24
and v26.16b, v26.16b, v4.16b
mul x23, x22, x9
add v22.2d, v22.2d, v1.2d
umulh x24, x22, x9
adds x12, x12, x23
ushr v0.2d, v21.2d, #26
adc x13, x13, x24
and v21.16b, v21.16b, v3.16b
ldr x22, [x0, #584]
mul x23, x22, x1
add v26.2d, v26.2d, v0.2d
umulh x24, x22, x1
ushr v1.2d, v25.2d, #25
adds x16, x16, x23
adc x17, x17, x24
and v25.16b, v25.16b, v4.16b
mul x23, x22, x2
add v21.2d, v21.2d, v1.2d
umulh x24, x22, x2
adds x20, x20, x23
ushr v0.2d, v20.2d, #26
adc x21, x21, x24
and v20.16b, v20.16b, v3.16b
mul x23, x22, x7
umulh x24, x22, x7
add v25.2d, v25.2d, v0.2d
adds x10, x10, x23
add v20.2d, v20.2d, v2.2d
adc x11, x11, x24
mul x23, x22, x8
shl v0.2d, v2.2d, #1
umulh x24, x22, x8
shl v2.2d, v2.2d, #4
adds x12, x12, x23
adc x13, x13, x24
add v20.2d, v20.2d, v0.2d
mul x23, x22, x9
add v20.2d, v20.2d, v2.2d
umulh x24, x22, x9
adds x14, x14, x23
shl v25.2d, v25.2d, #26
adc x15, x15, x24
add v20.2d, v20.2d, v25.2d
ldr x22, [x0, #592]
mul x23, x22, x1
shl v26.2d, v26.2d, #26
umulh x24, x22, x1
add v21.2d, v21.2d, v26.2d
adds x20, x20, x23
adc x21, x21, x24
shl v27.2d, v27.2d, #26
mul x23, x22, x6
add v22.2d, v22.2d, v27.2d
umulh x24, x22, x6
adds x10, x10, x23
shl v28.2d, v28.2d, #26
adc x11, x11, x24
add v23.2d, v23.2d, v28.2d
mul x23, x22, x7
umulh x24, x22, x7
shl v29.2d, v29.2d, #26
adds x12, x12, x23
add v24.2d, v24.2d, v29.2d
adc x13, x13, x24
mul x23, x22, x8
ldr q5, [x0, #704]
umulh x24, x22, x8
ushr v25.2d, v20.2d, #51
adds x14, x14, x23
adc x15, x15, x24
and v20.16b, v20.16b, v5.16b
mul x23, x22, x9
ushr v26.2d, v21.2d, #51
umulh x24, x22, x9
adds x16, x16, x23
and v21.16b, v21.16b, v5.16b
adc x17, x17, x24
ushr v27.2d, v22.2d, #51
mov x1, #0xffff
movk x1, #0xffff, lsl #16
and v22.16b, v22.16b, v5.16b
movk x1, #0xffff, lsl #32
ushr v28.2d, v23.2d, #51
movk x1, #7, lsl #48
mov w7, #19
and v23.16b, v23.16b, v5.16b
extr x2, x11, x10, #51
ushr v29.2d, v24.2d, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
and v24.16b, v24.16b, v5.16b
extr x5, x17, x16, #51
add v21.2d, v21.2d, v25.2d
extr x6, x21, x20, #51
and x10, x10, x1
add v22.2d, v22.2d, v26.2d
and x12, x12, x1
add v23.2d, v23.2d, v27.2d
and x14, x14, x1
and x16, x16, x1
add v24.2d, v24.2d, v28.2d
and x20, x20, x1
add v20.2d, v20.2d, v29.2d
mul x6, x6, x7
add x10, x10, x6
shl v0.2d, v29.2d, #1
add x12, x12, x2
shl v2.2d, v29.2d, #4
add x14, x14, x3
add x16, x16, x4
add v20.2d, v20.2d, v0.2d
add x20, x20, x5
add v20.2d, v20.2d, v2.2d
lsr x2, x10, #51
lsr x3, x12, #51
trn1 v0.2d, v20.2d, v21.2d
lsr x4, x14, #51
trn2 v1.2d, v20.2d, v21.2d
lsr x5, x16, #51
lsr x6, x20, #51
str q0, [x0, #16]
and x10, x10, x1
str q1, [x0, #64]
and x12, x12, x1
and x14, x14, x1
trn1 v0.2d, v22.2d, v23.2d
and x16, x16, x1
trn2 v1.2d, v22.2d, v23.2d
and x20, x20, x1
mul x6, x6, x7
str q0, [x0, #32]
add x10, x10, x6
str q1, [x0, #80]
add x12, x12, x2
add x14, x14, x3
trn1 v0.2d, v24.2d, v24.2d
add x16, x16, x4
trn2 v1.2d, v24.2d, v24.2d
add x20, x20, x5
stp x10, x12, [x0, #160]
str q0, [x0, #48]
stp x14, x16, [x0, #176]
str q1, [x0, #96]
str x20, [x0, #192]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret

.p2align 6
.globl lab_sn0
lab_sn0:
stp x19, x20, [sp, #-144]!
stp x21, x22, [sp, #16]
stp x23, x24, [sp, #32]
stp x25, x26, [sp, #48]
stp d8, d9, [sp, #64]
stp d10, d11, [sp, #80]
stp d12, d13, [sp, #96]
stp d14, d15, [sp, #112]
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
ldr x1, [x0, #16]
ldr x2, [x0, #64]
ldr x3, [x0, #112]
ldr x4, [x0, #160]
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
str x9, [x0, #208]
str x5, [x0, #256]
str x10, [x0, #304]
str x7, [x0, #352]
ldr x1, [x0, #24]
ldr x2, [x0, #72]
ldr x3, [x0, #120]
ldr x4, [x0, #168]
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
str x9, [x0, #216]
str x5, [x0, #264]
str x10, [x0, #312]
str x7, [x0, #360]
ldr x1, [x0, #32]
ldr x2, [x0, #80]
ldr x3, [x0, #128]
ldr x4, [x0, #176]
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
str x9, [x0, #224]
str x5, [x0, #272]
str x10, [x0, #320]
str x7, [x0, #368]
ldr x1, [x0, #40]
ldr x2, [x0, #88]
ldr x3, [x0, #136]
ldr x4, [x0, #184]
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
str x9, [x0, #232]
str x5, [x0, #280]
str x10, [x0, #328]
str x7, [x0, #376]
ldr x1, [x0, #48]
ldr x2, [x0, #96]
ldr x3, [x0, #144]
ldr x4, [x0, #192]
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
str x9, [x0, #240]
str x5, [x0, #288]
str x10, [x0, #336]
str x7, [x0, #384]
ldp x1, x2, [x0, #208]
ldp x3, x4, [x0, #224]
ldr x5, [x0, #240]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #352]
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
ldr x22, [x0, #360]
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
ldr x22, [x0, #368]
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
ldr x22, [x0, #376]
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
ldr x22, [x0, #384]
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
stp x10, x12, [x0, #352]
stp x14, x16, [x0, #368]
str x20, [x0, #384]
ldp x1, x2, [x0, #256]
ldp x3, x4, [x0, #272]
ldr x5, [x0, #288]
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
stp x10, x12, [x0, #304]
stp x14, x16, [x0, #320]
str x20, [x0, #336]
ldr q31, [x0, #720]
ldr q28, [x0, #208]
ldr q29, [x0, #256]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v0.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v1.4s, v29.4s, v28.4s
ldr q28, [x0, #224]
ldr q29, [x0, #272]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v2.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v3.4s, v29.4s, v28.4s
ldr q28, [x0, #240]
ldr q29, [x0, #288]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v4.4s, v29.4s, v30.4s
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
ext v7.16b, v2.16b, v2.16b, #8
ext v8.16b, v3.16b, v3.16b, #8
ext v9.16b, v4.16b, v4.16b, #8
add v10.4s, v0.4s, v0.4s
add v11.4s, v1.4s, v1.4s
add v12.4s, v2.4s, v2.4s
add v13.4s, v3.4s, v3.4s
add v14.4s, v4.4s, v4.4s
ldr q31, [x0, #752]
mul v15.4s, v0.4s, v31.4s
mul v16.4s, v1.4s, v31.4s
mul v17.4s, v2.4s, v31.4s
mul v18.4s, v3.4s, v31.4s
mul v19.4s, v4.4s, v31.4s
umull2 v20.2d, v10.4s, v19.4s
umlal2 v20.2d, v11.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
add v20.2d, v20.2d, v20.2d
umlal v20.2d, v0.2s, v0.2s
umlal v20.2d, v11.2s, v19.2s
umlal v20.2d, v12.2s, v18.2s
add v30.4s, v5.4s, v5.4s
umull v25.2d, v30.2s, v0.2s
add v30.4s, v6.4s, v6.4s
umlal v25.2d, v30.2s, v19.2s
umlal2 v25.2d, v30.4s, v19.4s
add v30.4s, v7.4s, v7.4s
umlal v25.2d, v30.2s, v18.2s
umlal2 v25.2d, v30.4s, v18.4s
umull2 v21.2d, v0.4s, v0.4s
umlal2 v21.2d, v11.4s, v19.4s
umlal2 v21.2d, v12.4s, v18.4s
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umlal v21.2d, v12.2s, v19.2s
umlal v21.2d, v3.2s, v18.2s
add v30.4s, v5.4s, v5.4s
umull v26.2d, v30.2s, v1.2s
umlal2 v26.2d, v30.4s, v1.4s
add v30.4s, v7.4s, v7.4s
umlal v26.2d, v30.2s, v19.2s
umlal2 v26.2d, v30.4s, v19.4s
add v30.4s, v8.4s, v8.4s
umlal v26.2d, v30.2s, v18.2s
umull2 v22.2d, v10.4s, v1.4s
umlal2 v22.2d, v12.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
add v22.2d, v22.2d, v22.2d
umlal v22.2d, v10.2s, v2.2s
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
add v30.4s, v5.4s, v5.4s
umull v27.2d, v30.2s, v2.2s
umlal2 v27.2d, v30.4s, v2.4s
add v30.4s, v6.4s, v6.4s
umlal v27.2d, v30.2s, v1.2s
add v30.4s, v8.4s, v8.4s
umlal v27.2d, v30.2s, v19.2s
umlal2 v27.2d, v30.4s, v19.4s
umull2 v23.2d, v10.4s, v2.4s
umlal2 v23.2d, v1.4s, v1.4s
umlal2 v23.2d, v13.4s, v19.4s
add v23.2d, v23.2d, v23.2d
umlal v23.2d, v10.2s, v3.2s
umlal v23.2d, v11.2s, v2.2s
umlal v23.2d, v4.2s, v19.2s
add v30.4s, v5.4s, v5.4s
umull v28.2d, v30.2s, v3.2s
umlal2 v28.2d, v30.4s, v3.4s
add v30.4s, v6.4s, v6.4s
umlal v28.2d, v30.2s, v2.2s
umlal2 v28.2d, v30.4s, v2.4s
add v30.4s, v9.4s, v9.4s
umlal v28.2d, v30.2s, v19.2s
umull2 v24.2d, v10.4s, v3.4s
umlal2 v24.2d, v11.4s, v2.4s
umlal2 v24.2d, v4.4s, v19.4s
add v24.2d, v24.2d, v24.2d
umlal v24.2d, v10.2s, v4.2s
umlal v24.2d, v11.2s, v3.2s
umlal v24.2d, v2.2s, v2.2s
add v30.4s, v5.4s, v5.4s
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
add v30.4s, v6.4s, v6.4s
umlal v29.2d, v30.2s, v3.2s
umlal2 v29.2d, v30.4s, v3.4s
add v30.4s, v7.4s, v7.4s
umlal v29.2d, v30.2s, v2.2s
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v29.2d, #25
and v29.16b, v29.16b, v4.16b
ushr v0.2d, v24.2d, #26
and v24.16b, v24.16b, v3.16b
add v29.2d, v29.2d, v0.2d
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
add v24.2d, v24.2d, v1.2d
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v23.2d, v23.2d, v1.2d
ushr v0.2d, v22.2d, #26
and v22.16b, v22.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v22.2d, v22.2d, v1.2d
ushr v0.2d, v21.2d, #26
and v21.16b, v21.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
and v20.16b, v20.16b, v3.16b
add v25.2d, v25.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v25.2d, v25.2d, #26
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
add v22.2d, v22.2d, v27.2d
shl v28.2d, v28.2d, #26
add v23.2d, v23.2d, v28.2d
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
ldr q5, [x0, #704]
ushr v25.2d, v20.2d, #51
and v20.16b, v20.16b, v5.16b
ushr v26.2d, v21.2d, #51
and v21.16b, v21.16b, v5.16b
ushr v27.2d, v22.2d, #51
and v22.16b, v22.16b, v5.16b
ushr v28.2d, v23.2d, #51
and v23.16b, v23.16b, v5.16b
ushr v29.2d, v24.2d, #51
and v24.16b, v24.16b, v5.16b
add v21.2d, v21.2d, v25.2d
add v22.2d, v22.2d, v26.2d
add v23.2d, v23.2d, v27.2d
add v24.2d, v24.2d, v28.2d
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
shl v2.2d, v29.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
trn1 v0.2d, v20.2d, v21.2d
trn2 v1.2d, v20.2d, v21.2d
str q0, [x0, #400]
str q1, [x0, #448]
trn1 v0.2d, v22.2d, v23.2d
trn2 v1.2d, v22.2d, v23.2d
str q0, [x0, #416]
str q1, [x0, #464]
trn1 v0.2d, v24.2d, v24.2d
trn2 v1.2d, v24.2d, v24.2d
str q0, [x0, #432]
str q1, [x0, #480]
ldp x1, x2, [x0, #400]
ldp x3, x4, [x0, #416]
ldr x5, [x0, #432]
ldp x6, x7, [x0, #448]
ldp x8, x9, [x0, #464]
ldr x10, [x0, #480]
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
movk x24, #0xf, lsl #48
sub x23, x24, #36
sub x6, x1, x6
add x6, x6, x23
sub x7, x2, x7
add x7, x7, x24
sub x8, x3, x8
add x8, x8, x24
sub x9, x4, x9
add x9, x9, x24
sub x10, x5, x10
add x10, x10, x24
str x6, [x0, #608]
str x7, [x0, #616]
str x8, [x0, #624]
str x9, [x0, #632]
str x10, [x0, #640]
mov w16, #0xdb41
movk w16, #1, lsl #16
mov x17, #0xffff
movk x17, #0xffff, lsl #16
movk x17, #0xffff, lsl #32
movk x17, #7, lsl #48
umulh x11, x6, x16
umulh x12, x7, x16
umulh x13, x8, x16
umulh x14, x9, x16
umulh x15, x10, x16
mul x6, x6, x16
mul x7, x7, x16
mul x8, x8, x16
mul x9, x9, x16
mul x10, x10, x16
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
str x1, [x0, #656]
str x2, [x0, #664]
str x3, [x0, #672]
str x4, [x0, #680]
str x5, [x0, #688]
ldp x1, x2, [x0, #352]
ldp x3, x4, [x0, #368]
ldr x5, [x0, #384]
ldp x6, x7, [x0, #304]
ldp x8, x9, [x0, #320]
ldr x10, [x0, #336]
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
stp x10, x12, [x0, #112]
stp x14, x16, [x0, #128]
str x20, [x0, #144]
ldp x1, x2, [x0, #352]
ldp x3, x4, [x0, #368]
ldr x5, [x0, #384]
ldp x6, x7, [x0, #304]
ldp x8, x9, [x0, #320]
ldr x10, [x0, #336]
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
stp x10, x12, [x0, #160]
stp x14, x16, [x0, #176]
str x20, [x0, #192]
ldp x1, x2, [x0, #160]
ldp x3, x4, [x0, #176]
ldr x5, [x0, #192]
mov w22, #19
mul x6, x2, x22
mul x7, x3, x22
mul x8, x4, x22
mul x9, x5, x22
ldr x22, [x0, #560]
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
ldr x22, [x0, #568]
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
ldr x22, [x0, #576]
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
ldr x22, [x0, #584]
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
ldr x22, [x0, #592]
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
stp x10, x12, [x0, #160]
stp x14, x16, [x0, #176]
str x20, [x0, #192]
ldr q31, [x0, #720]
ldr q28, [x0, #400]
ldr q29, [x0, #608]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v0.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v1.4s, v29.4s, v28.4s
ldr q28, [x0, #416]
ldr q29, [x0, #624]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v2.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v3.4s, v29.4s, v28.4s
ldr q28, [x0, #432]
ldr q29, [x0, #640]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v4.4s, v29.4s, v30.4s
ldr q28, [x0, #448]
ldr q29, [x0, #656]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v10.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v11.4s, v29.4s, v28.4s
ldr q28, [x0, #464]
ldr q29, [x0, #672]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v12.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v13.4s, v29.4s, v28.4s
ldr q28, [x0, #480]
ldr q29, [x0, #688]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v14.4s, v29.4s, v30.4s
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
ext v7.16b, v2.16b, v2.16b, #8
ext v8.16b, v3.16b, v3.16b, #8
ext v9.16b, v4.16b, v4.16b, #8
ldr q31, [x0, #752]
mul v15.4s, v10.4s, v31.4s
mul v16.4s, v11.4s, v31.4s
mul v17.4s, v12.4s, v31.4s
mul v18.4s, v13.4s, v31.4s
mul v19.4s, v14.4s, v31.4s
umull2 v20.2d, v0.4s, v19.4s
umlal2 v20.2d, v1.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
umlal2 v20.2d, v3.4s, v16.4s
umlal2 v20.2d, v4.4s, v15.4s
add v20.2d, v20.2d, v20.2d
umlal v20.2d, v0.2s, v10.2s
umlal v20.2d, v1.2s, v19.2s
umlal v20.2d, v2.2s, v18.2s
umlal v20.2d, v3.2s, v17.2s
umlal v20.2d, v4.2s, v16.2s
umull v25.2d, v5.2s, v10.2s
umlal2 v25.2d, v5.4s, v10.4s
umlal v25.2d, v6.2s, v19.2s
umlal2 v25.2d, v6.4s, v19.4s
umlal v25.2d, v7.2s, v18.2s
umlal2 v25.2d, v7.4s, v18.4s
umlal v25.2d, v8.2s, v17.2s
umlal2 v25.2d, v8.4s, v17.4s
umlal v25.2d, v9.2s, v16.2s
umlal2 v25.2d, v9.4s, v16.4s
umull2 v21.2d, v0.4s, v10.4s
umlal2 v21.2d, v1.4s, v19.4s
umlal2 v21.2d, v2.4s, v18.4s
umlal2 v21.2d, v3.4s, v17.4s
umlal2 v21.2d, v4.4s, v16.4s
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v0.2s, v11.2s
umlal v21.2d, v1.2s, v10.2s
umlal v21.2d, v2.2s, v19.2s
umlal v21.2d, v3.2s, v18.2s
umlal v21.2d, v4.2s, v17.2s
umull v26.2d, v5.2s, v11.2s
umlal2 v26.2d, v5.4s, v11.4s
umlal v26.2d, v6.2s, v10.2s
umlal2 v26.2d, v6.4s, v10.4s
umlal v26.2d, v7.2s, v19.2s
umlal2 v26.2d, v7.4s, v19.4s
umlal v26.2d, v8.2s, v18.2s
umlal2 v26.2d, v8.4s, v18.4s
umlal v26.2d, v9.2s, v17.2s
umlal2 v26.2d, v9.4s, v17.4s
umull2 v22.2d, v0.4s, v11.4s
umlal2 v22.2d, v1.4s, v10.4s
umlal2 v22.2d, v2.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
umlal2 v22.2d, v4.4s, v17.4s
add v22.2d, v22.2d, v22.2d
umlal v22.2d, v0.2s, v12.2s
umlal v22.2d, v1.2s, v11.2s
umlal v22.2d, v2.2s, v10.2s
umlal v22.2d, v3.2s, v19.2s
umlal v22.2d, v4.2s, v18.2s
umull v27.2d, v5.2s, v12.2s
umlal2 v27.2d, v5.4s, v12.4s
umlal v27.2d, v6.2s, v11.2s
umlal2 v27.2d, v6.4s, v11.4s
umlal v27.2d, v7.2s, v10.2s
umlal2 v27.2d, v7.4s, v10.4s
umlal v27.2d, v8.2s, v19.2s
umlal2 v27.2d, v8.4s, v19.4s
umlal v27.2d, v9.2s, v18.2s
umlal2 v27.2d, v9.4s, v18.4s
umull2 v23.2d, v0.4s, v12.4s
umlal2 v23.2d, v1.4s, v11.4s
umlal2 v23.2d, v2.4s, v10.4s
umlal2 v23.2d, v3.4s, v19.4s
umlal2 v23.2d, v4.4s, v18.4s
add v23.2d, v23.2d, v23.2d
umlal v23.2d, v0.2s, v13.2s
umlal v23.2d, v1.2s, v12.2s
umlal v23.2d, v2.2s, v11.2s
umlal v23.2d, v3.2s, v10.2s
umlal v23.2d, v4.2s, v19.2s
umull v28.2d, v5.2s, v13.2s
umlal2 v28.2d, v5.4s, v13.4s
umlal v28.2d, v6.2s, v12.2s
umlal2 v28.2d, v6.4s, v12.4s
umlal v28.2d, v7.2s, v11.2s
umlal2 v28.2d, v7.4s, v11.4s
umlal v28.2d, v8.2s, v10.2s
umlal2 v28.2d, v8.4s, v10.4s
umlal v28.2d, v9.2s, v19.2s
umlal2 v28.2d, v9.4s, v19.4s
umull2 v24.2d, v0.4s, v13.4s
umlal2 v24.2d, v1.4s, v12.4s
umlal2 v24.2d, v2.4s, v11.4s
umlal2 v24.2d, v3.4s, v10.4s
umlal2 v24.2d, v4.4s, v19.4s
add v24.2d, v24.2d, v24.2d
umlal v24.2d, v0.2s, v14.2s
umlal v24.2d, v1.2s, v13.2s
umlal v24.2d, v2.2s, v12.2s
umlal v24.2d, v3.2s, v11.2s
umlal v24.2d, v4.2s, v10.2s
umull v29.2d, v5.2s, v14.2s
umlal2 v29.2d, v5.4s, v14.4s
umlal v29.2d, v6.2s, v13.2s
umlal2 v29.2d, v6.4s, v13.4s
umlal v29.2d, v7.2s, v12.2s
umlal2 v29.2d, v7.4s, v12.4s
umlal v29.2d, v8.2s, v11.2s
umlal2 v29.2d, v8.4s, v11.4s
umlal v29.2d, v9.2s, v10.2s
umlal2 v29.2d, v9.4s, v10.4s
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v29.2d, #25
and v29.16b, v29.16b, v4.16b
ushr v0.2d, v24.2d, #26
and v24.16b, v24.16b, v3.16b
add v29.2d, v29.2d, v0.2d
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
add v24.2d, v24.2d, v1.2d
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v23.2d, v23.2d, v1.2d
ushr v0.2d, v22.2d, #26
and v22.16b, v22.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v22.2d, v22.2d, v1.2d
ushr v0.2d, v21.2d, #26
and v21.16b, v21.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
and v20.16b, v20.16b, v3.16b
add v25.2d, v25.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
shl v25.2d, v25.2d, #26
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
add v22.2d, v22.2d, v27.2d
shl v28.2d, v28.2d, #26
add v23.2d, v23.2d, v28.2d
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
ldr q5, [x0, #704]
ushr v25.2d, v20.2d, #51
and v20.16b, v20.16b, v5.16b
ushr v26.2d, v21.2d, #51
and v21.16b, v21.16b, v5.16b
ushr v27.2d, v22.2d, #51
and v22.16b, v22.16b, v5.16b
ushr v28.2d, v23.2d, #51
and v23.16b, v23.16b, v5.16b
ushr v29.2d, v24.2d, #51
and v24.16b, v24.16b, v5.16b
add v21.2d, v21.2d, v25.2d
add v22.2d, v22.2d, v26.2d
add v23.2d, v23.2d, v27.2d
add v24.2d, v24.2d, v28.2d
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
shl v2.2d, v29.2d, #4
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
trn1 v0.2d, v20.2d, v21.2d
trn2 v1.2d, v20.2d, v21.2d
str q0, [x0, #16]
str q1, [x0, #64]
trn1 v0.2d, v22.2d, v23.2d
trn2 v1.2d, v22.2d, v23.2d
str q0, [x0, #32]
str q1, [x0, #80]
trn1 v0.2d, v24.2d, v24.2d
trn2 v1.2d, v24.2d, v24.2d
str q0, [x0, #48]
str q1, [x0, #96]
sub x25, x25, #1
cbnz x25, 2b
ldp d8, d9, [sp, #64]
ldp d10, d11, [sp, #80]
ldp d12, d13, [sp, #96]
ldp d14, d15, [sp, #112]
ldp x25, x26, [sp, #48]
ldp x23, x24, [sp, #32]
ldp x21, x22, [sp, #16]
ldp x19, x20, [sp], #144
ret
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_st_o3(p: *mut u64, n: u64);fn lab_sq2(p: *mut u64, n: u64);fn lab_mu2(p: *mut u64, n: u64);fn lab_sn1(p: *mut u64, n: u64);fn lab_sn0(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_st_o3"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_st_o3(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sq2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sq2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mu2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mu2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn0"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn0(p, 100) })); g.finish();
}