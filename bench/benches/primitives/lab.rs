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
.globl lab_sn5
lab_sn5:
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
ldp x1, x9, [x0, #16]
ldp x2, x10, [x0, #64]
ldp x3, x11, [x0, #112]
ldp x4, x12, [x0, #160]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x1, x5, x6
add x5, x5, x23
sub x5, x5, x6
add x2, x7, x8
add x7, x7, x23
sub x7, x7, x8
csel x13, x11, x9, ne
csel x14, x12, x10, ne
csel x15, x9, x11, ne
csel x16, x10, x12, ne
add x9, x13, x14
add x13, x13, x24
sub x13, x13, x14
add x10, x15, x16
add x15, x15, x24
sub x15, x15, x16
stp x1, x9, [x0, #208]
stp x5, x13, [x0, #256]
stp x2, x10, [x0, #304]
stp x7, x15, [x0, #352]
ldp x1, x9, [x0, #32]
ldp x2, x10, [x0, #80]
ldp x3, x11, [x0, #128]
ldp x4, x12, [x0, #176]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x1, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x2, x7, x8
add x7, x7, x24
sub x7, x7, x8
csel x13, x11, x9, ne
csel x14, x12, x10, ne
csel x15, x9, x11, ne
csel x16, x10, x12, ne
add x9, x13, x14
add x13, x13, x24
sub x13, x13, x14
add x10, x15, x16
add x15, x15, x24
sub x15, x15, x16
stp x1, x9, [x0, #224]
stp x5, x13, [x0, #272]
stp x2, x10, [x0, #320]
stp x7, x15, [x0, #368]
ldr x1, [x0, #48]
ldr x2, [x0, #96]
ldr x3, [x0, #144]
ldr x4, [x0, #192]
csel x5, x3, x1, ne
csel x6, x4, x2, ne
csel x7, x1, x3, ne
csel x8, x2, x4, ne
add x1, x5, x6
add x5, x5, x24
sub x5, x5, x6
add x2, x7, x8
add x7, x7, x24
sub x7, x7, x8
stp x1, x22, [x0, #240]
stp x5, x22, [x0, #288]
stp x2, x22, [x0, #336]
stp x7, x22, [x0, #384]
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
ldr q31, [x0, #720]
ldp x3, x4, [x0, #416]
ldr q30, [x0, #784]
ldr x5, [x0, #432]
ldp x6, x7, [x0, #448]
ldr q29, [x0, #800]
ldp x8, x9, [x0, #464]
ldr x10, [x0, #480]
ldr q20, [x0, #352]
mov x24, #0xfffe
ldr q21, [x0, #304]
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
add v22.2d, v20.2d, v21.2d
movk x24, #0xf, lsl #48
sub x23, x24, #36
add v20.2d, v20.2d, v30.2d
sub x6, x1, x6
add x6, x6, x23
sub v20.2d, v20.2d, v21.2d
sub x7, x2, x7
trn1 v23.2d, v22.2d, v20.2d
add x7, x7, x24
sub x8, x3, x8
trn2 v24.2d, v22.2d, v20.2d
add x8, x8, x24
sub x9, x4, x9
and v25.16b, v23.16b, v31.16b
add x9, x9, x24
ushr v23.2d, v23.2d, #26
sub x10, x5, x10
add x10, x10, x24
uzp1 v0.4s, v25.4s, v23.4s
str x6, [x0, #256]
str x7, [x0, #264]
and v25.16b, v24.16b, v31.16b
str x8, [x0, #272]
str x9, [x0, #280]
ushr v24.2d, v24.2d, #26
str x10, [x0, #288]
uzp1 v1.4s, v25.4s, v24.4s
mov w16, #0xdb41
movk w16, #1, lsl #16
ldr q20, [x0, #368]
mov x17, #0xffff
movk x17, #0xffff, lsl #16
ldr q21, [x0, #320]
movk x17, #0xffff, lsl #32
add v22.2d, v20.2d, v21.2d
movk x17, #7, lsl #48
umulh x11, x6, x16
add v20.2d, v20.2d, v29.2d
umulh x12, x7, x16
umulh x13, x8, x16
sub v20.2d, v20.2d, v21.2d
umulh x14, x9, x16
umulh x15, x10, x16
trn1 v23.2d, v22.2d, v20.2d
mul x6, x6, x16
trn2 v24.2d, v22.2d, v20.2d
mul x7, x7, x16
mul x8, x8, x16
and v25.16b, v23.16b, v31.16b
mul x9, x9, x16
mul x10, x10, x16
ushr v23.2d, v23.2d, #26
extr x11, x11, x6, #51
uzp1 v2.4s, v25.4s, v23.4s
extr x12, x12, x7, #51
extr x13, x13, x8, #51
and v25.16b, v24.16b, v31.16b
extr x14, x14, x9, #51
extr x15, x15, x10, #51
ushr v24.2d, v24.2d, #26
and x6, x6, x17
and x7, x7, x17
uzp1 v3.4s, v25.4s, v24.4s
and x8, x8, x17
ldr q20, [x0, #384]
and x9, x9, x17
and x10, x10, x17
ldr q21, [x0, #336]
mov w16, #19
mul x15, x15, x16
add v22.2d, v20.2d, v21.2d
add x1, x1, x6
add v20.2d, v20.2d, v29.2d
add x2, x2, x7
add x3, x3, x8
sub v20.2d, v20.2d, v21.2d
add x4, x4, x9
add x5, x5, x10
trn1 v23.2d, v22.2d, v20.2d
add x1, x1, x15
add x2, x2, x11
and v25.16b, v23.16b, v31.16b
add x3, x3, x12
ushr v23.2d, v23.2d, #26
add x4, x4, x13
add x5, x5, x14
uzp1 v4.4s, v25.4s, v23.4s
str x1, [x0, #208]
str x2, [x0, #216]
ext v5.16b, v0.16b, v0.16b, #8
str x3, [x0, #224]
ext v6.16b, v1.16b, v1.16b, #8
str x4, [x0, #232]
str x5, [x0, #240]
ext v7.16b, v2.16b, v2.16b, #8
ldp x1, x2, [x0, #448]
ldp x3, x4, [x0, #464]
ext v8.16b, v3.16b, v3.16b, #8
ldr x5, [x0, #480]
mov w22, #19
ext v9.16b, v4.16b, v4.16b, #8
mul x6, x2, x22
add v10.4s, v0.4s, v0.4s
mul x7, x3, x22
mul x8, x4, x22
add v11.4s, v1.4s, v1.4s
mul x9, x5, x22
ldr x22, [x0, #400]
add v12.4s, v2.4s, v2.4s
mul x10, x22, x1
add v13.4s, v3.4s, v3.4s
umulh x11, x22, x1
mul x12, x22, x2
add v14.4s, v4.4s, v4.4s
umulh x13, x22, x2
mul x14, x22, x3
ldr q31, [x0, #752]
umulh x15, x22, x3
mul x16, x22, x4
mul v15.4s, v0.4s, v31.4s
umulh x17, x22, x4
mul v16.4s, v1.4s, v31.4s
mul x20, x22, x5
umulh x21, x22, x5
mul v17.4s, v2.4s, v31.4s
ldr x22, [x0, #408]
mul x23, x22, x1
mul v18.4s, v3.4s, v31.4s
umulh x24, x22, x1
mul v19.4s, v4.4s, v31.4s
adds x12, x12, x23
adc x13, x13, x24
umull2 v20.2d, v10.4s, v19.4s
mul x23, x22, x2
umulh x24, x22, x2
umlal2 v20.2d, v11.4s, v18.4s
adds x14, x14, x23
adc x15, x15, x24
umlal2 v20.2d, v2.4s, v17.4s
mul x23, x22, x3
add v20.2d, v20.2d, v20.2d
umulh x24, x22, x3
adds x16, x16, x23
umlal v20.2d, v0.2s, v0.2s
adc x17, x17, x24
mul x23, x22, x4
umlal v20.2d, v11.2s, v19.2s
umulh x24, x22, x4
umlal v20.2d, v12.2s, v18.2s
adds x20, x20, x23
adc x21, x21, x24
add v30.4s, v5.4s, v5.4s
mul x23, x22, x9
umulh x24, x22, x9
umull v25.2d, v30.2s, v0.2s
adds x10, x10, x23
adc x11, x11, x24
add v30.4s, v6.4s, v6.4s
ldr x22, [x0, #416]
umlal v25.2d, v30.2s, v19.2s
mul x23, x22, x1
umulh x24, x22, x1
umlal2 v25.2d, v30.4s, v19.4s
adds x14, x14, x23
adc x15, x15, x24
add v30.4s, v7.4s, v7.4s
mul x23, x22, x2
umlal v25.2d, v30.2s, v18.2s
umulh x24, x22, x2
adds x16, x16, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x17, x17, x24
mul x23, x22, x3
umull2 v21.2d, v0.4s, v0.4s
umulh x24, x22, x3
adds x20, x20, x23
umlal2 v21.2d, v11.4s, v19.4s
adc x21, x21, x24
umlal2 v21.2d, v12.4s, v18.4s
mul x23, x22, x8
umulh x24, x22, x8
add v21.2d, v21.2d, v21.2d
adds x10, x10, x23
adc x11, x11, x24
umlal v21.2d, v10.2s, v1.2s
mul x23, x22, x9
umlal v21.2d, v12.2s, v19.2s
umulh x24, x22, x9
adds x12, x12, x23
umlal v21.2d, v3.2s, v18.2s
adc x13, x13, x24
ldr x22, [x0, #424]
add v30.4s, v5.4s, v5.4s
mul x23, x22, x1
umulh x24, x22, x1
umull v26.2d, v30.2s, v1.2s
adds x16, x16, x23
umlal2 v26.2d, v30.4s, v1.4s
adc x17, x17, x24
mul x23, x22, x2
add v30.4s, v7.4s, v7.4s
umulh x24, x22, x2
adds x20, x20, x23
umlal v26.2d, v30.2s, v19.2s
adc x21, x21, x24
umlal2 v26.2d, v30.4s, v19.4s
mul x23, x22, x7
umulh x24, x22, x7
add v30.4s, v8.4s, v8.4s
adds x10, x10, x23
adc x11, x11, x24
umlal v26.2d, v30.2s, v18.2s
mul x23, x22, x8
umulh x24, x22, x8
umull2 v22.2d, v10.4s, v1.4s
adds x12, x12, x23
umlal2 v22.2d, v12.4s, v19.4s
adc x13, x13, x24
mul x23, x22, x9
umlal2 v22.2d, v3.4s, v18.4s
umulh x24, x22, x9
adds x14, x14, x23
add v22.2d, v22.2d, v22.2d
adc x15, x15, x24
umlal v22.2d, v10.2s, v2.2s
ldr x22, [x0, #432]
mul x23, x22, x1
umlal v22.2d, v1.2s, v1.2s
umulh x24, x22, x1
adds x20, x20, x23
umlal v22.2d, v13.2s, v19.2s
adc x21, x21, x24
mul x23, x22, x6
add v30.4s, v5.4s, v5.4s
umulh x24, x22, x6
umull v27.2d, v30.2s, v2.2s
adds x10, x10, x23
adc x11, x11, x24
umlal2 v27.2d, v30.4s, v2.4s
mul x23, x22, x7
umulh x24, x22, x7
add v30.4s, v6.4s, v6.4s
adds x12, x12, x23
umlal v27.2d, v30.2s, v1.2s
adc x13, x13, x24
mul x23, x22, x8
add v30.4s, v8.4s, v8.4s
umulh x24, x22, x8
adds x14, x14, x23
umlal v27.2d, v30.2s, v19.2s
adc x15, x15, x24
mul x23, x22, x9
umlal2 v27.2d, v30.4s, v19.4s
umulh x24, x22, x9
umull2 v23.2d, v10.4s, v2.4s
adds x16, x16, x23
adc x17, x17, x24
umlal2 v23.2d, v1.4s, v1.4s
mov x1, #0xffff
movk x1, #0xffff, lsl #16
umlal2 v23.2d, v13.4s, v19.4s
movk x1, #0xffff, lsl #32
add v23.2d, v23.2d, v23.2d
movk x1, #7, lsl #48
mov w7, #19
umlal v23.2d, v10.2s, v3.2s
extr x2, x11, x10, #51
extr x3, x13, x12, #51
umlal v23.2d, v11.2s, v2.2s
extr x4, x15, x14, #51
extr x5, x17, x16, #51
umlal v23.2d, v4.2s, v19.2s
extr x6, x21, x20, #51
add v30.4s, v5.4s, v5.4s
and x10, x10, x1
and x12, x12, x1
umull v28.2d, v30.2s, v3.2s
and x14, x14, x1
and x16, x16, x1
umlal2 v28.2d, v30.4s, v3.4s
and x20, x20, x1
add v30.4s, v6.4s, v6.4s
mul x6, x6, x7
add x10, x10, x6
umlal v28.2d, v30.2s, v2.2s
add x12, x12, x2
add x14, x14, x3
umlal2 v28.2d, v30.4s, v2.4s
add x16, x16, x4
add x20, x20, x5
add v30.4s, v9.4s, v9.4s
lsr x2, x10, #51
umlal v28.2d, v30.2s, v19.2s
lsr x3, x12, #51
lsr x4, x14, #51
umull2 v24.2d, v10.4s, v3.4s
lsr x5, x16, #51
lsr x6, x20, #51
umlal2 v24.2d, v11.4s, v2.4s
and x10, x10, x1
umlal2 v24.2d, v4.4s, v19.4s
and x12, x12, x1
and x14, x14, x1
add v24.2d, v24.2d, v24.2d
and x16, x16, x1
and x20, x20, x1
umlal v24.2d, v10.2s, v4.2s
mul x6, x6, x7
add x10, x10, x6
umlal v24.2d, v11.2s, v3.2s
add x12, x12, x2
umlal v24.2d, v2.2s, v2.2s
add x14, x14, x3
add x16, x16, x4
add v30.4s, v5.4s, v5.4s
add x20, x20, x5
stp x10, x12, [x0, #16]
umull v29.2d, v30.2s, v4.2s
stp x14, x16, [x0, #32]
umlal2 v29.2d, v30.4s, v4.4s
str x20, [x0, #48]
ldp x1, x2, [x0, #208]
add v30.4s, v6.4s, v6.4s
ldp x3, x4, [x0, #224]
ldr x5, [x0, #240]
umlal v29.2d, v30.2s, v3.2s
mov w22, #19
mul x6, x2, x22
umlal2 v29.2d, v30.4s, v3.4s
mul x7, x3, x22
add v30.4s, v7.4s, v7.4s
mul x8, x4, x22
mul x9, x5, x22
umlal v29.2d, v30.2s, v2.2s
ldr x22, [x0, #256]
mul x10, x22, x1
ldr q3, [x0, #720]
umulh x11, x22, x1
ldr q4, [x0, #736]
mul x12, x22, x2
umulh x13, x22, x2
ushr v2.2d, v29.2d, #25
mul x14, x22, x3
umulh x15, x22, x3
and v29.16b, v29.16b, v4.16b
mul x16, x22, x4
umulh x17, x22, x4
ushr v0.2d, v24.2d, #26
mul x20, x22, x5
and v24.16b, v24.16b, v3.16b
umulh x21, x22, x5
ldr x22, [x0, #264]
add v29.2d, v29.2d, v0.2d
mul x23, x22, x1
umulh x24, x22, x1
ushr v1.2d, v28.2d, #25
adds x12, x12, x23
and v28.16b, v28.16b, v4.16b
adc x13, x13, x24
mul x23, x22, x2
add v24.2d, v24.2d, v1.2d
umulh x24, x22, x2
adds x14, x14, x23
ushr v0.2d, v23.2d, #26
adc x15, x15, x24
mul x23, x22, x3
and v23.16b, v23.16b, v3.16b
umulh x24, x22, x3
add v28.2d, v28.2d, v0.2d
adds x16, x16, x23
adc x17, x17, x24
ushr v1.2d, v27.2d, #25
mul x23, x22, x4
umulh x24, x22, x4
and v27.16b, v27.16b, v4.16b
adds x20, x20, x23
add v23.2d, v23.2d, v1.2d
adc x21, x21, x24
mul x23, x22, x9
ushr v0.2d, v22.2d, #26
umulh x24, x22, x9
adds x10, x10, x23
and v22.16b, v22.16b, v3.16b
adc x11, x11, x24
ldr x22, [x0, #272]
add v27.2d, v27.2d, v0.2d
mul x23, x22, x1
ushr v1.2d, v26.2d, #25
umulh x24, x22, x1
adds x14, x14, x23
and v26.16b, v26.16b, v4.16b
adc x15, x15, x24
mul x23, x22, x2
add v22.2d, v22.2d, v1.2d
umulh x24, x22, x2
ushr v0.2d, v21.2d, #26
adds x16, x16, x23
adc x17, x17, x24
and v21.16b, v21.16b, v3.16b
mul x23, x22, x3
umulh x24, x22, x3
add v26.2d, v26.2d, v0.2d
adds x20, x20, x23
adc x21, x21, x24
ushr v1.2d, v25.2d, #25
mul x23, x22, x8
and v25.16b, v25.16b, v4.16b
umulh x24, x22, x8
adds x10, x10, x23
add v21.2d, v21.2d, v1.2d
adc x11, x11, x24
mul x23, x22, x9
ushr v0.2d, v20.2d, #26
umulh x24, x22, x9
and v20.16b, v20.16b, v3.16b
adds x12, x12, x23
adc x13, x13, x24
add v25.2d, v25.2d, v0.2d
ldr x22, [x0, #280]
mul x23, x22, x1
add v20.2d, v20.2d, v2.2d
umulh x24, x22, x1
adds x16, x16, x23
shl v0.2d, v2.2d, #1
adc x17, x17, x24
shl v2.2d, v2.2d, #4
mul x23, x22, x2
umulh x24, x22, x2
add v20.2d, v20.2d, v0.2d
adds x20, x20, x23
adc x21, x21, x24
add v20.2d, v20.2d, v2.2d
mul x23, x22, x7
shl v25.2d, v25.2d, #26
umulh x24, x22, x7
adds x10, x10, x23
add v20.2d, v20.2d, v25.2d
adc x11, x11, x24
mul x23, x22, x8
shl v26.2d, v26.2d, #26
umulh x24, x22, x8
adds x12, x12, x23
add v21.2d, v21.2d, v26.2d
adc x13, x13, x24
shl v27.2d, v27.2d, #26
mul x23, x22, x9
umulh x24, x22, x9
add v22.2d, v22.2d, v27.2d
adds x14, x14, x23
adc x15, x15, x24
shl v28.2d, v28.2d, #26
ldr x22, [x0, #288]
add v23.2d, v23.2d, v28.2d
mul x23, x22, x1
umulh x24, x22, x1
shl v29.2d, v29.2d, #26
adds x20, x20, x23
adc x21, x21, x24
add v24.2d, v24.2d, v29.2d
mul x23, x22, x6
umulh x24, x22, x6
ldr q5, [x0, #704]
adds x10, x10, x23
ushr v25.2d, v20.2d, #51
adc x11, x11, x24
mul x23, x22, x7
and v20.16b, v20.16b, v5.16b
umulh x24, x22, x7
adds x12, x12, x23
ushr v26.2d, v21.2d, #51
adc x13, x13, x24
and v21.16b, v21.16b, v5.16b
mul x23, x22, x8
umulh x24, x22, x8
ushr v27.2d, v22.2d, #51
adds x14, x14, x23
adc x15, x15, x24
and v22.16b, v22.16b, v5.16b
mul x23, x22, x9
umulh x24, x22, x9
ushr v28.2d, v23.2d, #51
adds x16, x16, x23
and v23.16b, v23.16b, v5.16b
adc x17, x17, x24
mov x1, #0xffff
ushr v29.2d, v24.2d, #51
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
and v24.16b, v24.16b, v5.16b
movk x1, #7, lsl #48
add v21.2d, v21.2d, v25.2d
mov w7, #19
extr x2, x11, x10, #51
add v22.2d, v22.2d, v26.2d
extr x3, x13, x12, #51
extr x4, x15, x14, #51
add v23.2d, v23.2d, v27.2d
extr x5, x17, x16, #51
extr x6, x21, x20, #51
add v24.2d, v24.2d, v28.2d
and x10, x10, x1
add v20.2d, v20.2d, v29.2d
and x12, x12, x1
and x14, x14, x1
shl v0.2d, v29.2d, #1
and x16, x16, x1
and x20, x20, x1
shl v2.2d, v29.2d, #4
mul x6, x6, x7
add v20.2d, v20.2d, v0.2d
add x10, x10, x6
add x12, x12, x2
add v20.2d, v20.2d, v2.2d
add x14, x14, x3
add x16, x16, x4
trn1 v0.2d, v20.2d, v21.2d
add x20, x20, x5
lsr x2, x10, #51
trn2 v1.2d, v20.2d, v21.2d
lsr x3, x12, #51
str q0, [x0, #112]
lsr x4, x14, #51
lsr x5, x16, #51
str q1, [x0, #160]
lsr x6, x20, #51
and x10, x10, x1
trn1 v0.2d, v22.2d, v23.2d
and x12, x12, x1
trn2 v1.2d, v22.2d, v23.2d
and x14, x14, x1
and x16, x16, x1
str q0, [x0, #128]
and x20, x20, x1
mul x6, x6, x7
str q1, [x0, #176]
add x10, x10, x6
add x12, x12, x2
trn1 v0.2d, v24.2d, v24.2d
add x14, x14, x3
trn2 v1.2d, v24.2d, v24.2d
add x16, x16, x4
add x20, x20, x5
str q0, [x0, #144]
stp x10, x12, [x0, #64]
stp x14, x16, [x0, #80]
str q1, [x0, #192]
str x20, [x0, #96]
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
.globl lab_h1
lab_h1:
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
ldr q31, [x0, #720]
ldr q30, [x0, #736]
ldp x14, x15, [x0, #240]
ldr q20, [x0, #224]
ldr x3, [x0, #320]
ldr q21, [x0, #256]
mul x4, x3, x12
ldr q22, [x0, #240]
mul x5, x3, x13
ldr q23, [x0, #272]
mul x6, x3, x14
trn1 v24.2d, v20.2d, v21.2d
mul x7, x3, x15
trn2 v25.2d, v20.2d, v21.2d
umulh x2, x3, x12
trn1 v26.2d, v22.2d, v23.2d
umulh x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
umulh x9, x3, x14
and v20.16b, v24.16b, v31.16b
umulh x16, x3, x15
ushr v21.2d, v24.2d, #26
adds x5, x5, x2
and v21.16b, v21.16b, v30.16b
adcs x6, x6, x8
uzp1 v0.4s, v20.4s, v21.4s
adcs x7, x7, x9
shl v20.2d, v25.2d, #13
adc x21, x16, x10
sri v20.2d, v24.2d, #51
ldr x3, [x0, #328]
and v20.16b, v20.16b, v31.16b
ushr v21.2d, v25.2d, #13
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
uzp1 v1.4s, v20.4s, v21.4s
mul x9, x3, x14
ushr v20.2d, v25.2d, #38
mul x16, x3, x15
and v21.16b, v26.16b, v30.16b
adds x5, x5, x2
uzp1 v2.4s, v20.4s, v21.4s
adcs x6, x6, x8
ushr v20.2d, v26.2d, #25
adcs x7, x7, x9
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x16
shl v21.2d, v27.2d, #13
adc x22, x10, x10
sri v21.2d, v26.2d, #51
umulh x2, x3, x12
and v21.16b, v21.16b, v30.16b
umulh x8, x3, x13
uzp1 v3.4s, v20.4s, v21.4s
umulh x9, x3, x14
ushr v20.2d, v27.2d, #12
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
ushr v21.2d, v27.2d, #38
adcs x7, x7, x8
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x9
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
adc x22, x22, x16
ext v7.16b, v2.16b, v2.16b, #8
ldr x3, [x0, #336]
ext v8.16b, v3.16b, v3.16b, #8
mul x2, x3, x12
ext v9.16b, v4.16b, v4.16b, #8
mul x8, x3, x13
add v10.4s, v0.4s, v0.4s
mul x9, x3, x14
add v11.4s, v1.4s, v1.4s
mul x16, x3, x15
add v12.4s, v2.4s, v2.4s
adds x6, x6, x2
add v13.4s, v3.4s, v3.4s
adcs x7, x7, x8
add v14.4s, v4.4s, v4.4s
adcs x21, x21, x9
ldr q31, [x0, #752]
adcs x22, x22, x16
mul v15.4s, v0.4s, v31.4s
adc x23, x10, x10
mul v16.4s, v1.4s, v31.4s
umulh x2, x3, x12
mul v17.4s, v2.4s, v31.4s
umulh x8, x3, x13
mul v18.4s, v3.4s, v31.4s
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x7, x7, x2
umlal2 v20.2d, v11.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
adcs x21, x21, x8
add v20.2d, v20.2d, v20.2d
adcs x22, x22, x9
umlal v20.2d, v0.2s, v0.2s
adc x23, x23, x16
umlal v20.2d, v11.2s, v19.2s
ldr x3, [x0, #344]
umlal v20.2d, v12.2s, v18.2s
mul x2, x3, x12
add v30.4s, v5.4s, v5.4s
mul x8, x3, x13
umull v25.2d, v30.2s, v0.2s
mul x9, x3, x14
add v30.4s, v6.4s, v6.4s
mul x16, x3, x15
umlal v25.2d, v30.2s, v19.2s
adds x7, x7, x2
umlal2 v25.2d, v30.4s, v19.4s
adcs x21, x21, x8
add v30.4s, v7.4s, v7.4s
adcs x22, x22, x9
umlal v25.2d, v30.2s, v18.2s
adcs x23, x23, x16
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x10, x10
umull2 v21.2d, v0.4s, v0.4s
umulh x2, x3, x12
umlal2 v21.2d, v11.4s, v19.4s
umulh x8, x3, x13
umlal2 v21.2d, v12.4s, v18.4s
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umulh x16, x3, x15
umlal v21.2d, v12.2s, v19.2s
adds x21, x21, x2
umlal v21.2d, v3.2s, v18.2s
adcs x22, x22, x8
add v30.4s, v5.4s, v5.4s
adcs x23, x23, x9
umull v26.2d, v30.2s, v1.2s
adc x24, x24, x16
umlal2 v26.2d, v30.4s, v1.4s
mov w11, #38
add v30.4s, v7.4s, v7.4s
mul x2, x11, x21
umlal v26.2d, v30.2s, v19.2s
mul x8, x11, x22
umlal2 v26.2d, v30.4s, v19.4s
mul x9, x11, x23
add v30.4s, v8.4s, v8.4s
mul x16, x11, x24
umlal v26.2d, v30.2s, v18.2s
umulh x21, x11, x21
umull2 v22.2d, v10.4s, v1.4s
umulh x22, x11, x22
umlal2 v22.2d, v12.4s, v19.4s
umulh x23, x11, x23
umlal2 v22.2d, v3.4s, v18.4s
umulh x24, x11, x24
add v22.2d, v22.2d, v22.2d
adds x4, x4, x2
umlal v22.2d, v10.2s, v2.2s
adcs x5, x5, x8
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
adcs x6, x6, x9
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x16
umull v27.2d, v30.2s, v2.2s
adc x24, x24, x10
umlal2 v27.2d, v30.4s, v2.4s
adds x7, x7, x23
add v30.4s, v6.4s, v6.4s
adc x24, x24, x10
umlal v27.2d, v30.2s, v1.2s
mov w11, #19
add v30.4s, v8.4s, v8.4s
extr x17, x24, x7, #63
umlal v27.2d, v30.2s, v19.2s
and x7, x7, #0x7fffffffffffffff
umlal2 v27.2d, v30.4s, v19.4s
mul x17, x17, x11
umull2 v23.2d, v10.4s, v2.4s
adds x4, x4, x17
umlal2 v23.2d, v1.4s, v1.4s
adcs x5, x5, x21
umlal2 v23.2d, v13.4s, v19.4s
adcs x6, x6, x22
add v23.2d, v23.2d, v23.2d
adc x7, x7, x10
umlal v23.2d, v10.2s, v3.2s
stp x4, x5, [x0, #448]
umlal v23.2d, v11.2s, v2.2s
stp x6, x7, [x0, #464]
umlal v23.2d, v4.2s, v19.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
umull v28.2d, v30.2s, v3.2s
ldp x14, x15, [x0, #272]
umlal2 v28.2d, v30.4s, v3.4s
ldr x3, [x0, #288]
add v30.4s, v6.4s, v6.4s
mul x4, x3, x12
umlal v28.2d, v30.2s, v2.2s
mul x5, x3, x13
umlal2 v28.2d, v30.4s, v2.4s
mul x6, x3, x14
add v30.4s, v9.4s, v9.4s
mul x7, x3, x15
umlal v28.2d, v30.2s, v19.2s
umulh x2, x3, x12
umull2 v24.2d, v10.4s, v3.4s
umulh x8, x3, x13
umlal2 v24.2d, v11.4s, v2.4s
umulh x9, x3, x14
umlal2 v24.2d, v4.4s, v19.4s
umulh x16, x3, x15
add v24.2d, v24.2d, v24.2d
adds x5, x5, x2
umlal v24.2d, v10.2s, v4.2s
adcs x6, x6, x8
umlal v24.2d, v11.2s, v3.2s
adcs x7, x7, x9
umlal v24.2d, v2.2s, v2.2s
adc x21, x16, x10
add v30.4s, v5.4s, v5.4s
ldr x3, [x0, #296]
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
mul x2, x3, x12
add v30.4s, v6.4s, v6.4s
mul x8, x3, x13
umlal v29.2d, v30.2s, v3.2s
mul x9, x3, x14
umlal2 v29.2d, v30.4s, v3.4s
mul x16, x3, x15
add v30.4s, v7.4s, v7.4s
adds x5, x5, x2
umlal v29.2d, v30.2s, v2.2s
adcs x6, x6, x8
ldr q3, [x0, #720]
adcs x7, x7, x9
ldr q4, [x0, #736]
adcs x21, x21, x16
ushr v2.2d, v29.2d, #25
adc x22, x10, x10
and v29.16b, v29.16b, v4.16b
umulh x2, x3, x12
ushr v0.2d, v24.2d, #26
umulh x8, x3, x13
and v24.16b, v24.16b, v3.16b
umulh x9, x3, x14
add v29.2d, v29.2d, v0.2d
umulh x16, x3, x15
ushr v1.2d, v28.2d, #25
adds x6, x6, x2
and v28.16b, v28.16b, v4.16b
adcs x7, x7, x8
add v24.2d, v24.2d, v1.2d
adcs x21, x21, x9
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
adc x22, x22, x16
add v28.2d, v28.2d, v0.2d
ldr x3, [x0, #304]
ushr v1.2d, v27.2d, #25
mul x2, x3, x12
and v27.16b, v27.16b, v4.16b
mul x8, x3, x13
add v23.2d, v23.2d, v1.2d
mul x9, x3, x14
ushr v0.2d, v22.2d, #26
mul x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x6, x6, x2
add v27.2d, v27.2d, v0.2d
adcs x7, x7, x8
ushr v1.2d, v26.2d, #25
adcs x21, x21, x9
and v26.16b, v26.16b, v4.16b
adcs x22, x22, x16
add v22.2d, v22.2d, v1.2d
adc x23, x10, x10
ushr v0.2d, v21.2d, #26
umulh x2, x3, x12
and v21.16b, v21.16b, v3.16b
umulh x8, x3, x13
add v26.2d, v26.2d, v0.2d
umulh x9, x3, x14
ushr v1.2d, v25.2d, #25
umulh x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
adcs x21, x21, x8
and v20.16b, v20.16b, v3.16b
adcs x22, x22, x9
add v25.2d, v25.2d, v0.2d
adc x23, x23, x16
add v20.2d, v20.2d, v2.2d
ldr x3, [x0, #312]
shl v0.2d, v2.2d, #1
mul x2, x3, x12
shl v2.2d, v2.2d, #4
mul x8, x3, x13
add v20.2d, v20.2d, v0.2d
mul x9, x3, x14
add v20.2d, v20.2d, v2.2d
mul x16, x3, x15
shl v25.2d, v25.2d, #26
adds x7, x7, x2
add v20.2d, v20.2d, v25.2d
adcs x21, x21, x8
shl v26.2d, v26.2d, #26
adcs x22, x22, x9
add v21.2d, v21.2d, v26.2d
adcs x23, x23, x16
shl v27.2d, v27.2d, #26
adc x24, x10, x10
add v22.2d, v22.2d, v27.2d
umulh x2, x3, x12
shl v28.2d, v28.2d, #26
umulh x8, x3, x13
add v23.2d, v23.2d, v28.2d
umulh x9, x3, x14
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
umulh x16, x3, x15
ldr q5, [x0, #704]
adds x21, x21, x2
ushr v25.2d, v20.2d, #51
adcs x22, x22, x8
and v20.16b, v20.16b, v5.16b
adcs x23, x23, x9
ushr v26.2d, v21.2d, #51
adc x24, x24, x16
and v21.16b, v21.16b, v5.16b
mov w11, #38
ushr v27.2d, v22.2d, #51
mul x2, x11, x21
and v22.16b, v22.16b, v5.16b
mul x8, x11, x22
ushr v28.2d, v23.2d, #51
mul x9, x11, x23
and v23.16b, v23.16b, v5.16b
mul x16, x11, x24
ushr v29.2d, v24.2d, #51
umulh x21, x11, x21
and v24.16b, v24.16b, v5.16b
umulh x22, x11, x22
add v21.2d, v21.2d, v25.2d
umulh x23, x11, x23
add v22.2d, v22.2d, v26.2d
umulh x24, x11, x24
add v23.2d, v23.2d, v27.2d
adds x4, x4, x2
add v24.2d, v24.2d, v28.2d
adcs x5, x5, x8
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
adcs x6, x6, x9
shl v2.2d, v29.2d, #4
adcs x7, x7, x16
add v20.2d, v20.2d, v0.2d
adc x24, x24, x10
add v20.2d, v20.2d, v2.2d
adds x7, x7, x23
trn1 v0.2d, v20.2d, v21.2d
adc x24, x24, x10
trn2 v1.2d, v20.2d, v21.2d
mov w11, #19
str q0, [x0, #1024]
extr x17, x24, x7, #63
str q1, [x0, #1072]
and x7, x7, #0x7fffffffffffffff
trn1 v0.2d, v22.2d, v23.2d
mul x17, x17, x11
trn2 v1.2d, v22.2d, v23.2d
adds x4, x4, x17
str q0, [x0, #1040]
adcs x5, x5, x21
str q1, [x0, #1088]
adcs x6, x6, x22
trn1 v0.2d, v24.2d, v24.2d
adc x7, x7, x10
trn2 v1.2d, v24.2d, v24.2d
stp x4, x5, [x0, #480]
str q0, [x0, #1056]
stp x6, x7, [x0, #496]
str q1, [x0, #1104]
ldr x2, [x0, #1024]
ldr x3, [x0, #1032]
ldr x8, [x0, #1040]
ldr x9, [x0, #1048]
ldr x16, [x0, #1056]
lsl x17, x3, #51
adds x4, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x5, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x6, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x7, x9, x17
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
ldr x2, [x0, #1072]
ldr x3, [x0, #1080]
ldr x8, [x0, #1088]
ldr x9, [x0, #1096]
ldr x16, [x0, #1104]
lsl x17, x3, #51
adds x21, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x22, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x23, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x24, x9, x17
stp x21, x22, [x0, #384]
stp x23, x24, [x0, #400]
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
.globl lab_h1b
lab_h1b:
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
ldr q31, [x0, #720]
ldr q30, [x0, #736]
ldp x14, x15, [x0, #240]
ldr q20, [x0, #224]
ldr x3, [x0, #320]
ldr q21, [x0, #256]
mul x4, x3, x12
ldr q22, [x0, #240]
mul x5, x3, x13
ldr q23, [x0, #272]
mul x6, x3, x14
trn1 v24.2d, v20.2d, v21.2d
mul x7, x3, x15
trn2 v25.2d, v20.2d, v21.2d
umulh x2, x3, x12
trn1 v26.2d, v22.2d, v23.2d
umulh x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
umulh x9, x3, x14
and v20.16b, v24.16b, v31.16b
umulh x16, x3, x15
ushr v21.2d, v24.2d, #26
adds x5, x5, x2
and v21.16b, v21.16b, v30.16b
adcs x6, x6, x8
uzp1 v0.4s, v20.4s, v21.4s
adcs x7, x7, x9
shl v20.2d, v25.2d, #13
adc x21, x16, x10
sri v20.2d, v24.2d, #51
ldr x3, [x0, #328]
and v20.16b, v20.16b, v31.16b
ushr v21.2d, v25.2d, #13
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
uzp1 v1.4s, v20.4s, v21.4s
mul x9, x3, x14
ushr v20.2d, v25.2d, #38
mul x16, x3, x15
and v21.16b, v26.16b, v30.16b
adds x5, x5, x2
uzp1 v2.4s, v20.4s, v21.4s
adcs x6, x6, x8
ushr v20.2d, v26.2d, #25
adcs x7, x7, x9
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x16
shl v21.2d, v27.2d, #13
adc x22, x10, x10
sri v21.2d, v26.2d, #51
umulh x2, x3, x12
and v21.16b, v21.16b, v30.16b
umulh x8, x3, x13
uzp1 v3.4s, v20.4s, v21.4s
umulh x9, x3, x14
ushr v20.2d, v27.2d, #12
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
ushr v21.2d, v27.2d, #38
adcs x7, x7, x8
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x9
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
adc x22, x22, x16
ext v7.16b, v2.16b, v2.16b, #8
ldr x3, [x0, #336]
ext v8.16b, v3.16b, v3.16b, #8
mul x2, x3, x12
ext v9.16b, v4.16b, v4.16b, #8
mul x8, x3, x13
add v10.4s, v0.4s, v0.4s
mul x9, x3, x14
add v11.4s, v1.4s, v1.4s
mul x16, x3, x15
add v12.4s, v2.4s, v2.4s
adds x6, x6, x2
add v13.4s, v3.4s, v3.4s
adcs x7, x7, x8
add v14.4s, v4.4s, v4.4s
adcs x21, x21, x9
ldr q31, [x0, #752]
adcs x22, x22, x16
mul v15.4s, v0.4s, v31.4s
adc x23, x10, x10
mul v16.4s, v1.4s, v31.4s
umulh x2, x3, x12
mul v17.4s, v2.4s, v31.4s
umulh x8, x3, x13
mul v18.4s, v3.4s, v31.4s
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x7, x7, x2
umlal2 v20.2d, v11.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
adcs x21, x21, x8
add v20.2d, v20.2d, v20.2d
adcs x22, x22, x9
umlal v20.2d, v0.2s, v0.2s
adc x23, x23, x16
umlal v20.2d, v11.2s, v19.2s
ldr x3, [x0, #344]
umlal v20.2d, v12.2s, v18.2s
mul x2, x3, x12
add v30.4s, v5.4s, v5.4s
mul x8, x3, x13
umull v25.2d, v30.2s, v0.2s
mul x9, x3, x14
add v30.4s, v6.4s, v6.4s
mul x16, x3, x15
umlal v25.2d, v30.2s, v19.2s
adds x7, x7, x2
umlal2 v25.2d, v30.4s, v19.4s
adcs x21, x21, x8
add v30.4s, v7.4s, v7.4s
adcs x22, x22, x9
umlal v25.2d, v30.2s, v18.2s
adcs x23, x23, x16
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x10, x10
umull2 v21.2d, v0.4s, v0.4s
umulh x2, x3, x12
umlal2 v21.2d, v11.4s, v19.4s
umulh x8, x3, x13
umlal2 v21.2d, v12.4s, v18.4s
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umulh x16, x3, x15
umlal v21.2d, v12.2s, v19.2s
adds x21, x21, x2
umlal v21.2d, v3.2s, v18.2s
adcs x22, x22, x8
add v30.4s, v5.4s, v5.4s
adcs x23, x23, x9
umull v26.2d, v30.2s, v1.2s
adc x24, x24, x16
umlal2 v26.2d, v30.4s, v1.4s
mov w11, #38
add v30.4s, v7.4s, v7.4s
mul x2, x11, x21
umlal v26.2d, v30.2s, v19.2s
mul x8, x11, x22
umlal2 v26.2d, v30.4s, v19.4s
mul x9, x11, x23
add v30.4s, v8.4s, v8.4s
mul x16, x11, x24
umlal v26.2d, v30.2s, v18.2s
umulh x21, x11, x21
umull2 v22.2d, v10.4s, v1.4s
umulh x22, x11, x22
umlal2 v22.2d, v12.4s, v19.4s
umulh x23, x11, x23
umlal2 v22.2d, v3.4s, v18.4s
umulh x24, x11, x24
add v22.2d, v22.2d, v22.2d
adds x4, x4, x2
umlal v22.2d, v10.2s, v2.2s
adcs x5, x5, x8
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
adcs x6, x6, x9
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x16
umull v27.2d, v30.2s, v2.2s
adc x24, x24, x10
umlal2 v27.2d, v30.4s, v2.4s
adds x7, x7, x23
add v30.4s, v6.4s, v6.4s
adc x24, x24, x10
umlal v27.2d, v30.2s, v1.2s
mov w11, #19
add v30.4s, v8.4s, v8.4s
extr x17, x24, x7, #63
umlal v27.2d, v30.2s, v19.2s
and x7, x7, #0x7fffffffffffffff
umlal2 v27.2d, v30.4s, v19.4s
mul x17, x17, x11
umull2 v23.2d, v10.4s, v2.4s
adds x4, x4, x17
umlal2 v23.2d, v1.4s, v1.4s
adcs x5, x5, x21
umlal2 v23.2d, v13.4s, v19.4s
adcs x6, x6, x22
add v23.2d, v23.2d, v23.2d
adc x7, x7, x10
umlal v23.2d, v10.2s, v3.2s
stp x4, x5, [x0, #448]
umlal v23.2d, v11.2s, v2.2s
stp x6, x7, [x0, #464]
umlal v23.2d, v4.2s, v19.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
umull v28.2d, v30.2s, v3.2s
ldp x14, x15, [x0, #272]
umlal2 v28.2d, v30.4s, v3.4s
ldr x3, [x0, #288]
add v30.4s, v6.4s, v6.4s
mul x4, x3, x12
umlal v28.2d, v30.2s, v2.2s
mul x5, x3, x13
umlal2 v28.2d, v30.4s, v2.4s
mul x6, x3, x14
add v30.4s, v9.4s, v9.4s
mul x7, x3, x15
umlal v28.2d, v30.2s, v19.2s
umulh x2, x3, x12
umull2 v24.2d, v10.4s, v3.4s
umulh x8, x3, x13
umlal2 v24.2d, v11.4s, v2.4s
umulh x9, x3, x14
umlal2 v24.2d, v4.4s, v19.4s
umulh x16, x3, x15
add v24.2d, v24.2d, v24.2d
adds x5, x5, x2
umlal v24.2d, v10.2s, v4.2s
adcs x6, x6, x8
umlal v24.2d, v11.2s, v3.2s
adcs x7, x7, x9
umlal v24.2d, v2.2s, v2.2s
adc x21, x16, x10
add v30.4s, v5.4s, v5.4s
ldr x3, [x0, #296]
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
mul x2, x3, x12
add v30.4s, v6.4s, v6.4s
mul x8, x3, x13
umlal v29.2d, v30.2s, v3.2s
mul x9, x3, x14
umlal2 v29.2d, v30.4s, v3.4s
mul x16, x3, x15
add v30.4s, v7.4s, v7.4s
adds x5, x5, x2
umlal v29.2d, v30.2s, v2.2s
adcs x6, x6, x8
ldr q3, [x0, #720]
adcs x7, x7, x9
ldr q4, [x0, #736]
adcs x21, x21, x16
ushr v2.2d, v29.2d, #25
adc x22, x10, x10
and v29.16b, v29.16b, v4.16b
umulh x2, x3, x12
ushr v0.2d, v24.2d, #26
umulh x8, x3, x13
and v24.16b, v24.16b, v3.16b
umulh x9, x3, x14
add v29.2d, v29.2d, v0.2d
umulh x16, x3, x15
ushr v1.2d, v28.2d, #25
adds x6, x6, x2
and v28.16b, v28.16b, v4.16b
adcs x7, x7, x8
add v24.2d, v24.2d, v1.2d
adcs x21, x21, x9
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
adc x22, x22, x16
add v28.2d, v28.2d, v0.2d
ldr x3, [x0, #304]
ushr v1.2d, v27.2d, #25
mul x2, x3, x12
and v27.16b, v27.16b, v4.16b
mul x8, x3, x13
add v23.2d, v23.2d, v1.2d
mul x9, x3, x14
ushr v0.2d, v22.2d, #26
mul x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x6, x6, x2
add v27.2d, v27.2d, v0.2d
adcs x7, x7, x8
ushr v1.2d, v26.2d, #25
adcs x21, x21, x9
and v26.16b, v26.16b, v4.16b
adcs x22, x22, x16
add v22.2d, v22.2d, v1.2d
adc x23, x10, x10
ushr v0.2d, v21.2d, #26
umulh x2, x3, x12
and v21.16b, v21.16b, v3.16b
umulh x8, x3, x13
add v26.2d, v26.2d, v0.2d
umulh x9, x3, x14
ushr v1.2d, v25.2d, #25
umulh x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
adcs x21, x21, x8
and v20.16b, v20.16b, v3.16b
adcs x22, x22, x9
add v25.2d, v25.2d, v0.2d
adc x23, x23, x16
add v20.2d, v20.2d, v2.2d
ldr x3, [x0, #312]
shl v0.2d, v2.2d, #1
mul x2, x3, x12
shl v2.2d, v2.2d, #4
mul x8, x3, x13
add v20.2d, v20.2d, v0.2d
mul x9, x3, x14
add v20.2d, v20.2d, v2.2d
mul x16, x3, x15
shl v25.2d, v25.2d, #26
adds x7, x7, x2
add v20.2d, v20.2d, v25.2d
adcs x21, x21, x8
shl v26.2d, v26.2d, #26
adcs x22, x22, x9
add v21.2d, v21.2d, v26.2d
adcs x23, x23, x16
shl v27.2d, v27.2d, #26
adc x24, x10, x10
add v22.2d, v22.2d, v27.2d
umulh x2, x3, x12
shl v28.2d, v28.2d, #26
umulh x8, x3, x13
add v23.2d, v23.2d, v28.2d
umulh x9, x3, x14
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
umulh x16, x3, x15
ldr q5, [x0, #704]
adds x21, x21, x2
ushr v25.2d, v20.2d, #51
adcs x22, x22, x8
and v20.16b, v20.16b, v5.16b
adcs x23, x23, x9
ushr v26.2d, v21.2d, #51
adc x24, x24, x16
and v21.16b, v21.16b, v5.16b
mov w11, #38
ushr v27.2d, v22.2d, #51
mul x2, x11, x21
and v22.16b, v22.16b, v5.16b
mul x8, x11, x22
ushr v28.2d, v23.2d, #51
mul x9, x11, x23
and v23.16b, v23.16b, v5.16b
mul x16, x11, x24
ushr v29.2d, v24.2d, #51
umulh x21, x11, x21
and v24.16b, v24.16b, v5.16b
umulh x22, x11, x22
add v21.2d, v21.2d, v25.2d
umulh x23, x11, x23
add v22.2d, v22.2d, v26.2d
umulh x24, x11, x24
add v23.2d, v23.2d, v27.2d
adds x4, x4, x2
add v24.2d, v24.2d, v28.2d
adcs x5, x5, x8
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
adcs x6, x6, x9
shl v2.2d, v29.2d, #4
adcs x7, x7, x16
add v20.2d, v20.2d, v0.2d
adc x24, x24, x10
add v20.2d, v20.2d, v2.2d
adds x7, x7, x23
trn1 v0.2d, v20.2d, v21.2d
adc x24, x24, x10
trn2 v1.2d, v20.2d, v21.2d
mov w11, #19
str q0, [x0, #1024]
extr x17, x24, x7, #63
str q1, [x0, #1072]
and x7, x7, #0x7fffffffffffffff
trn1 v0.2d, v22.2d, v23.2d
mul x17, x17, x11
trn2 v1.2d, v22.2d, v23.2d
adds x4, x4, x17
str q0, [x0, #1040]
adcs x5, x5, x21
str q1, [x0, #1088]
adcs x6, x6, x22
trn1 v0.2d, v24.2d, v24.2d
adc x7, x7, x10
trn2 v1.2d, v24.2d, v24.2d
stp x4, x5, [x0, #480]
str q0, [x0, #1056]
stp x6, x7, [x0, #496]
str q1, [x0, #1104]
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
ldr x2, [x0, #1024]
ldr x3, [x0, #1032]
ldr x8, [x0, #1040]
ldr x9, [x0, #1048]
ldr x16, [x0, #1056]
lsl x17, x3, #51
adds x4, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x5, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x6, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x7, x9, x17
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
ldr x2, [x0, #1072]
ldr x3, [x0, #1080]
ldr x8, [x0, #1088]
ldr x9, [x0, #1096]
ldr x16, [x0, #1104]
lsl x17, x3, #51
adds x21, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x22, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x23, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x24, x9, x17
stp x21, x22, [x0, #384]
stp x23, x24, [x0, #400]
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
.globl lab_h2
lab_h2:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
mul x5, x3, x13
ldr q21, [x0, #256]
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
umulh x8, x3, x13
trn1 v24.2d, v20.2d, v21.2d
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
adcs x6, x6, x8
trn2 v27.2d, v22.2d, v23.2d
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
adds x5, x5, x2
sri v20.2d, v24.2d, #51
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
adc x22, x10, x10
and v21.16b, v21.16b, v30.16b
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
ushr v20.2d, v25.2d, #38
umulh x16, x3, x15
and v21.16b, v26.16b, v30.16b
adds x6, x6, x2
uzp1 v2.4s, v20.4s, v21.4s
adcs x7, x7, x8
adcs x21, x21, x9
ushr v20.2d, v26.2d, #25
adc x22, x22, x16
and v20.16b, v20.16b, v31.16b
ldr x3, [x0, #336]
shl v21.2d, v27.2d, #13
mul x2, x3, x12
mul x8, x3, x13
sri v21.2d, v26.2d, #51
mul x9, x3, x14
and v21.16b, v21.16b, v30.16b
mul x16, x3, x15
uzp1 v3.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v27.2d, #12
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x16
ushr v21.2d, v27.2d, #38
adc x23, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
ext v5.16b, v0.16b, v0.16b, #8
umulh x9, x3, x14
ext v6.16b, v1.16b, v1.16b, #8
umulh x16, x3, x15
adds x7, x7, x2
ext v7.16b, v2.16b, v2.16b, #8
adcs x21, x21, x8
ext v8.16b, v3.16b, v3.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
ext v9.16b, v4.16b, v4.16b, #8
ldr x3, [x0, #344]
add v10.4s, v0.4s, v0.4s
mul x2, x3, x12
add v11.4s, v1.4s, v1.4s
mul x8, x3, x13
mul x9, x3, x14
add v12.4s, v2.4s, v2.4s
mul x16, x3, x15
add v13.4s, v3.4s, v3.4s
adds x7, x7, x2
add v14.4s, v4.4s, v4.4s
adcs x21, x21, x8
adcs x22, x22, x9
ldr q31, [x0, #752]
adcs x23, x23, x16
mul v15.4s, v0.4s, v31.4s
adc x24, x10, x10
mul v16.4s, v1.4s, v31.4s
umulh x2, x3, x12
umulh x8, x3, x13
mul v17.4s, v2.4s, v31.4s
umulh x9, x3, x14
mul v18.4s, v3.4s, v31.4s
umulh x16, x3, x15
mul v19.4s, v4.4s, v31.4s
adds x21, x21, x2
adcs x22, x22, x8
umull2 v20.2d, v10.4s, v19.4s
adcs x23, x23, x9
umlal2 v20.2d, v11.4s, v18.4s
adc x24, x24, x16
umlal2 v20.2d, v2.4s, v17.4s
mov w11, #38
mul x2, x11, x21
add v20.2d, v20.2d, v20.2d
mul x8, x11, x22
umlal v20.2d, v0.2s, v0.2s
mul x9, x11, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x11, x24
umulh x21, x11, x21
umlal v20.2d, v12.2s, v18.2s
umulh x22, x11, x22
add v30.4s, v5.4s, v5.4s
umulh x23, x11, x23
umulh x24, x11, x24
umull v25.2d, v30.2s, v0.2s
adds x4, x4, x2
add v30.4s, v6.4s, v6.4s
adcs x5, x5, x8
umlal v25.2d, v30.2s, v19.2s
adcs x6, x6, x9
adcs x7, x7, x16
umlal2 v25.2d, v30.4s, v19.4s
adc x24, x24, x10
add v30.4s, v7.4s, v7.4s
adds x7, x7, x23
umlal v25.2d, v30.2s, v18.2s
adc x24, x24, x10
mov w11, #19
umlal2 v25.2d, v30.4s, v18.4s
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x11
adds x4, x4, x17
umlal2 v21.2d, v12.4s, v18.4s
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
stp x4, x5, [x0, #448]
umlal v21.2d, v12.2s, v19.2s
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umull v26.2d, v30.2s, v1.2s
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
mul x6, x3, x14
add v30.4s, v7.4s, v7.4s
mul x7, x3, x15
umlal v26.2d, v30.2s, v19.2s
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v30.4s, v8.4s, v8.4s
umulh x16, x3, x15
umlal v26.2d, v30.2s, v18.2s
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
adcs x7, x7, x9
umlal2 v22.2d, v12.4s, v19.4s
adc x21, x16, x10
umlal2 v22.2d, v3.4s, v18.4s
ldr x3, [x0, #296]
add v22.2d, v22.2d, v22.2d
mul x2, x3, x12
mul x8, x3, x13
umlal v22.2d, v10.2s, v2.2s
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
umlal v22.2d, v13.2s, v19.2s
adds x5, x5, x2
adcs x6, x6, x8
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x9
umull v27.2d, v30.2s, v2.2s
adcs x21, x21, x16
umlal2 v27.2d, v30.4s, v2.4s
adc x22, x10, x10
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umlal v27.2d, v30.2s, v1.2s
umulh x9, x3, x14
add v30.4s, v8.4s, v8.4s
umulh x16, x3, x15
adds x6, x6, x2
umlal v27.2d, v30.2s, v19.2s
adcs x7, x7, x8
umlal2 v27.2d, v30.4s, v19.4s
adcs x21, x21, x9
adc x22, x22, x16
umull2 v23.2d, v10.4s, v2.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v1.4s, v1.4s
mul x2, x3, x12
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x3, x13
mul x9, x3, x14
add v23.2d, v23.2d, v23.2d
mul x16, x3, x15
umlal v23.2d, v10.2s, v3.2s
adds x6, x6, x2
umlal v23.2d, v11.2s, v2.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v23.2d, v4.2s, v19.2s
adcs x22, x22, x16
add v30.4s, v5.4s, v5.4s
adc x23, x10, x10
umull v28.2d, v30.2s, v3.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal2 v28.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v28.2d, v30.2s, v2.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v28.2d, v30.4s, v2.4s
adcs x22, x22, x9
add v30.4s, v9.4s, v9.4s
adc x23, x23, x16
umlal v28.2d, v30.2s, v19.2s
ldr x3, [x0, #312]
mul x2, x3, x12
umull2 v24.2d, v10.4s, v3.4s
mul x8, x3, x13
umlal2 v24.2d, v11.4s, v2.4s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v24.2d, v4.4s, v19.4s
adds x7, x7, x2
add v24.2d, v24.2d, v24.2d
adcs x21, x21, x8
umlal v24.2d, v10.2s, v4.2s
adcs x22, x22, x9
adcs x23, x23, x16
umlal v24.2d, v11.2s, v3.2s
adc x24, x10, x10
umlal v24.2d, v2.2s, v2.2s
umulh x2, x3, x12
add v30.4s, v5.4s, v5.4s
umulh x8, x3, x13
umulh x9, x3, x14
umull v29.2d, v30.2s, v4.2s
umulh x16, x3, x15
umlal2 v29.2d, v30.4s, v4.4s
adds x21, x21, x2
add v30.4s, v6.4s, v6.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal v29.2d, v30.2s, v3.2s
adc x24, x24, x16
umlal2 v29.2d, v30.4s, v3.4s
mov w11, #38
add v30.4s, v7.4s, v7.4s
mul x2, x11, x21
mul x8, x11, x22
umlal v29.2d, v30.2s, v2.2s
mul x9, x11, x23
ldr q3, [x0, #720]
mul x16, x11, x24
ldr q4, [x0, #736]
umulh x21, x11, x21
umulh x22, x11, x22
ushr v2.2d, v29.2d, #25
umulh x23, x11, x23
and v29.16b, v29.16b, v4.16b
umulh x24, x11, x24
ushr v0.2d, v24.2d, #26
adds x4, x4, x2
adcs x5, x5, x8
and v24.16b, v24.16b, v3.16b
adcs x6, x6, x9
add v29.2d, v29.2d, v0.2d
adcs x7, x7, x16
adc x24, x24, x10
ushr v1.2d, v28.2d, #25
adds x7, x7, x23
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
add v24.2d, v24.2d, v1.2d
mov w11, #19
extr x17, x24, x7, #63
ushr v0.2d, v23.2d, #26
and x7, x7, #0x7fffffffffffffff
and v23.16b, v23.16b, v3.16b
mul x17, x17, x11
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
adcs x5, x5, x21
ushr v1.2d, v27.2d, #25
adcs x6, x6, x22
and v27.16b, v27.16b, v4.16b
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
ushr v0.2d, v22.2d, #26
ldp x4, x5, [x0, #448]
and v22.16b, v22.16b, v3.16b
ldp x6, x7, [x0, #464]
add v27.2d, v27.2d, v0.2d
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
ushr v1.2d, v26.2d, #25
subs x12, x4, x21
and v26.16b, v26.16b, v4.16b
sbcs x13, x5, x22
add v22.2d, v22.2d, v1.2d
mov w2, #38
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x2, hs
subs x12, x12, x3
add v26.2d, v26.2d, v0.2d
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
mul x5, x12, x13
add v21.2d, v21.2d, v1.2d
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
umulh x8, x12, x14
add v25.2d, v25.2d, v0.2d
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
umulh x3, x13, x14
shl v2.2d, v2.2d, #4
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
adds x6, x6, x2
shl v25.2d, v25.2d, #26
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
adcs x21, x21, x17
add v21.2d, v21.2d, v26.2d
adc x22, x11, x10
shl v27.2d, v27.2d, #26
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
adc x23, x23, x10
shl v28.2d, v28.2d, #26
lsr x24, x23, #63
add v23.2d, v23.2d, v28.2d
extr x23, x23, x22, #63
extr x22, x22, x21, #63
shl v29.2d, v29.2d, #26
extr x21, x21, x7, #63
add v24.2d, v24.2d, v29.2d
extr x7, x7, x6, #63
ldr q5, [x0, #704]
extr x6, x6, x5, #63
lsl x5, x5, #1
ushr v25.2d, v20.2d, #51
mul x4, x12, x12
and v20.16b, v20.16b, v5.16b
umulh x2, x12, x12
ushr v26.2d, v21.2d, #51
mul x8, x13, x13
umulh x9, x13, x13
and v21.16b, v21.16b, v5.16b
mul x16, x14, x14
ushr v27.2d, v22.2d, #51
umulh x17, x14, x14
and v22.16b, v22.16b, v5.16b
mul x3, x15, x15
umulh x11, x15, x15
ushr v28.2d, v23.2d, #51
adds x5, x5, x2
and v23.16b, v23.16b, v5.16b
adcs x6, x6, x8
ushr v29.2d, v24.2d, #51
adcs x7, x7, x9
adcs x21, x21, x16
and v24.16b, v24.16b, v5.16b
adcs x22, x22, x17
add v21.2d, v21.2d, v25.2d
adcs x23, x23, x3
add v22.2d, v22.2d, v26.2d
adc x24, x24, x11
mov w11, #38
add v23.2d, v23.2d, v27.2d
mul x2, x11, x21
add v24.2d, v24.2d, v28.2d
mul x8, x11, x22
mul x9, x11, x23
add v20.2d, v20.2d, v29.2d
mul x16, x11, x24
shl v0.2d, v29.2d, #1
umulh x21, x11, x21
shl v2.2d, v29.2d, #4
umulh x22, x11, x22
umulh x23, x11, x23
add v20.2d, v20.2d, v0.2d
umulh x24, x11, x24
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
adcs x6, x6, x9
trn2 v1.2d, v20.2d, v21.2d
adcs x7, x7, x16
str q0, [x0, #1024]
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
adc x24, x24, x10
trn1 v0.2d, v22.2d, v23.2d
mov w11, #19
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
str q0, [x0, #1040]
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
trn2 v1.2d, v24.2d, v24.2d
adcs x6, x6, x22
adc x7, x7, x10
str q0, [x0, #1056]
stp x4, x5, [x0, #192]
str q1, [x0, #1104]
stp x6, x7, [x0, #208]
ldr x2, [x0, #1024]
ldr x3, [x0, #1032]
ldr x8, [x0, #1040]
ldr x9, [x0, #1048]
ldr x16, [x0, #1056]
lsl x17, x3, #51
adds x4, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x5, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x6, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x7, x9, x17
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
ldr x2, [x0, #1072]
ldr x3, [x0, #1080]
ldr x8, [x0, #1088]
ldr x9, [x0, #1096]
ldr x16, [x0, #1104]
lsl x17, x3, #51
adds x21, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x22, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x23, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x24, x9, x17
stp x21, x22, [x0, #384]
stp x23, x24, [x0, #400]
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
.globl lab_h3
lab_h3:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
mul x4, x3, x12
ldr q20, [x0, #224]
mul x5, x3, x13
mul x6, x3, x14
ldr q21, [x0, #256]
mul x7, x3, x15
umulh x2, x3, x12
ldr q22, [x0, #240]
umulh x8, x3, x13
ldr q23, [x0, #272]
umulh x9, x3, x14
umulh x16, x3, x15
trn1 v24.2d, v20.2d, v21.2d
adds x5, x5, x2
adcs x6, x6, x8
trn2 v25.2d, v20.2d, v21.2d
adcs x7, x7, x9
adc x21, x16, x10
trn1 v26.2d, v22.2d, v23.2d
ldr x3, [x0, #328]
trn2 v27.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
and v20.16b, v24.16b, v31.16b
mul x9, x3, x14
mul x16, x3, x15
ushr v21.2d, v24.2d, #26
adds x5, x5, x2
adcs x6, x6, x8
and v21.16b, v21.16b, v30.16b
adcs x7, x7, x9
uzp1 v0.4s, v20.4s, v21.4s
adcs x21, x21, x16
adc x22, x10, x10
shl v20.2d, v25.2d, #13
umulh x2, x3, x12
umulh x8, x3, x13
sri v20.2d, v24.2d, #51
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
ushr v21.2d, v25.2d, #13
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v21.16b, v30.16b
adc x22, x22, x16
ldr x3, [x0, #336]
uzp1 v1.4s, v20.4s, v21.4s
mul x2, x3, x12
mul x8, x3, x13
ushr v20.2d, v25.2d, #38
mul x9, x3, x14
and v21.16b, v26.16b, v30.16b
mul x16, x3, x15
adds x6, x6, x2
uzp1 v2.4s, v20.4s, v21.4s
adcs x7, x7, x8
adcs x21, x21, x9
ushr v20.2d, v26.2d, #25
adcs x22, x22, x16
adc x23, x10, x10
and v20.16b, v20.16b, v31.16b
umulh x2, x3, x12
shl v21.2d, v27.2d, #13
umulh x8, x3, x13
umulh x9, x3, x14
sri v21.2d, v26.2d, #51
umulh x16, x3, x15
adds x7, x7, x2
and v21.16b, v21.16b, v30.16b
adcs x21, x21, x8
adcs x22, x22, x9
uzp1 v3.4s, v20.4s, v21.4s
adc x23, x23, x16
ushr v20.2d, v27.2d, #12
ldr x3, [x0, #344]
mul x2, x3, x12
and v20.16b, v20.16b, v31.16b
mul x8, x3, x13
mul x9, x3, x14
ushr v21.2d, v27.2d, #38
mul x16, x3, x15
adds x7, x7, x2
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x8
ext v5.16b, v0.16b, v0.16b, #8
adcs x22, x22, x9
adcs x23, x23, x16
ext v6.16b, v1.16b, v1.16b, #8
adc x24, x10, x10
umulh x2, x3, x12
ext v7.16b, v2.16b, v2.16b, #8
umulh x8, x3, x13
umulh x9, x3, x14
ext v8.16b, v3.16b, v3.16b, #8
umulh x16, x3, x15
adds x21, x21, x2
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x8
add v10.4s, v0.4s, v0.4s
adcs x23, x23, x9
adc x24, x24, x16
add v11.4s, v1.4s, v1.4s
mov w11, #38
mul x2, x11, x21
add v12.4s, v2.4s, v2.4s
mul x8, x11, x22
mul x9, x11, x23
add v13.4s, v3.4s, v3.4s
mul x16, x11, x24
add v14.4s, v4.4s, v4.4s
umulh x21, x11, x21
umulh x22, x11, x22
ldr q31, [x0, #752]
umulh x23, x11, x23
umulh x24, x11, x24
mul v15.4s, v0.4s, v31.4s
adds x4, x4, x2
adcs x5, x5, x8
mul v16.4s, v1.4s, v31.4s
adcs x6, x6, x9
mul v17.4s, v2.4s, v31.4s
adcs x7, x7, x16
adc x24, x24, x10
mul v18.4s, v3.4s, v31.4s
adds x7, x7, x23
adc x24, x24, x10
mul v19.4s, v4.4s, v31.4s
mov w11, #19
extr x17, x24, x7, #63
umull2 v20.2d, v10.4s, v19.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v20.2d, v11.4s, v18.4s
mul x17, x17, x11
adds x4, x4, x17
umlal2 v20.2d, v2.4s, v17.4s
adcs x5, x5, x21
adcs x6, x6, x22
add v20.2d, v20.2d, v20.2d
adc x7, x7, x10
stp x4, x5, [x0, #448]
umlal v20.2d, v0.2s, v0.2s
stp x6, x7, [x0, #464]
umlal v20.2d, v11.2s, v19.2s
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
umlal v20.2d, v12.2s, v18.2s
ldr x3, [x0, #288]
mul x4, x3, x12
add v30.4s, v5.4s, v5.4s
mul x5, x3, x13
mul x6, x3, x14
umull v25.2d, v30.2s, v0.2s
mul x7, x3, x15
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v25.2d, v30.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v25.2d, v30.4s, v19.4s
adds x5, x5, x2
adcs x6, x6, x8
add v30.4s, v7.4s, v7.4s
adcs x7, x7, x9
umlal v25.2d, v30.2s, v18.2s
adc x21, x16, x10
ldr x3, [x0, #296]
umlal2 v25.2d, v30.4s, v18.4s
mul x2, x3, x12
mul x8, x3, x13
umull2 v21.2d, v0.4s, v0.4s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v21.2d, v11.4s, v19.4s
adds x5, x5, x2
umlal2 v21.2d, v12.4s, v18.4s
adcs x6, x6, x8
adcs x7, x7, x9
add v21.2d, v21.2d, v21.2d
adcs x21, x21, x16
adc x22, x10, x10
umlal v21.2d, v10.2s, v1.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v21.2d, v12.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v21.2d, v3.2s, v18.2s
adds x6, x6, x2
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x8
adcs x21, x21, x9
umull v26.2d, v30.2s, v1.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal2 v26.2d, v30.4s, v1.4s
mul x2, x3, x12
mul x8, x3, x13
add v30.4s, v7.4s, v7.4s
mul x9, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x16, x3, x15
adds x6, x6, x2
umlal2 v26.2d, v30.4s, v19.4s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v8.4s, v8.4s
adcs x22, x22, x16
adc x23, x10, x10
umlal v26.2d, v30.2s, v18.2s
umulh x2, x3, x12
umull2 v22.2d, v10.4s, v1.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal2 v22.2d, v12.4s, v19.4s
umulh x16, x3, x15
adds x7, x7, x2
umlal2 v22.2d, v3.4s, v18.4s
adcs x21, x21, x8
adcs x22, x22, x9
add v22.2d, v22.2d, v22.2d
adc x23, x23, x16
umlal v22.2d, v10.2s, v2.2s
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v1.2s, v1.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x7, x7, x2
add v30.4s, v5.4s, v5.4s
adcs x21, x21, x8
umull v27.2d, v30.2s, v2.2s
adcs x22, x22, x9
adcs x23, x23, x16
umlal2 v27.2d, v30.4s, v2.4s
adc x24, x10, x10
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v27.2d, v30.2s, v1.2s
umulh x16, x3, x15
add v30.4s, v8.4s, v8.4s
adds x21, x21, x2
adcs x22, x22, x8
umlal v27.2d, v30.2s, v19.2s
adcs x23, x23, x9
adc x24, x24, x16
umlal2 v27.2d, v30.4s, v19.4s
mov w11, #38
mul x2, x11, x21
umull2 v23.2d, v10.4s, v2.4s
mul x8, x11, x22
umlal2 v23.2d, v1.4s, v1.4s
mul x9, x11, x23
mul x16, x11, x24
umlal2 v23.2d, v13.4s, v19.4s
umulh x21, x11, x21
umulh x22, x11, x22
add v23.2d, v23.2d, v23.2d
umulh x23, x11, x23
umulh x24, x11, x24
umlal v23.2d, v10.2s, v3.2s
adds x4, x4, x2
umlal v23.2d, v11.2s, v2.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x16
adc x24, x24, x10
add v30.4s, v5.4s, v5.4s
adds x7, x7, x23
adc x24, x24, x10
umull v28.2d, v30.2s, v3.2s
mov w11, #19
extr x17, x24, x7, #63
umlal2 v28.2d, v30.4s, v3.4s
and x7, x7, #0x7fffffffffffffff
add v30.4s, v6.4s, v6.4s
mul x17, x17, x11
adds x4, x4, x17
umlal v28.2d, v30.2s, v2.2s
adcs x5, x5, x21
adcs x6, x6, x22
umlal2 v28.2d, v30.4s, v2.4s
adc x7, x7, x10
stp x4, x5, [x0, #480]
add v30.4s, v9.4s, v9.4s
stp x6, x7, [x0, #496]
umlal v28.2d, v30.2s, v19.2s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
umull2 v24.2d, v10.4s, v3.4s
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
umlal2 v24.2d, v11.4s, v2.4s
subs x12, x4, x21
sbcs x13, x5, x22
umlal2 v24.2d, v4.4s, v19.4s
mov w2, #38
add v24.2d, v24.2d, v24.2d
sbcs x14, x6, x23
sbcs x15, x7, x24
umlal v24.2d, v10.2s, v4.2s
csel x3, x10, x2, hs
subs x12, x12, x3
umlal v24.2d, v11.2s, v3.2s
sbcs x13, x13, x10
sbcs x14, x14, x10
umlal v24.2d, v2.2s, v2.2s
sbc x15, x15, x10
add v30.4s, v5.4s, v5.4s
mul x5, x12, x13
mul x6, x12, x14
umull v29.2d, v30.2s, v4.2s
mul x7, x12, x15
umulh x2, x12, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x8, x12, x14
umulh x9, x12, x15
add v30.4s, v6.4s, v6.4s
mul x16, x13, x14
umlal v29.2d, v30.2s, v3.2s
mul x17, x13, x15
umulh x3, x13, x14
umlal2 v29.2d, v30.4s, v3.4s
umulh x11, x13, x15
mul x20, x14, x15
add v30.4s, v7.4s, v7.4s
umulh x23, x14, x15
adds x6, x6, x2
umlal v29.2d, v30.2s, v2.2s
adcs x7, x7, x8
ldr q3, [x0, #720]
adc x21, x9, x10
adds x7, x7, x16
ldr q4, [x0, #736]
adcs x21, x21, x17
adc x22, x11, x10
ushr v2.2d, v29.2d, #25
adds x21, x21, x3
adcs x22, x22, x20
and v29.16b, v29.16b, v4.16b
adc x23, x23, x10
ushr v0.2d, v24.2d, #26
lsr x24, x23, #63
extr x23, x23, x22, #63
and v24.16b, v24.16b, v3.16b
extr x22, x22, x21, #63
extr x21, x21, x7, #63
add v29.2d, v29.2d, v0.2d
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v1.2d, v28.2d, #25
lsl x5, x5, #1
and v28.16b, v28.16b, v4.16b
mul x4, x12, x12
umulh x2, x12, x12
add v24.2d, v24.2d, v1.2d
mul x8, x13, x13
umulh x9, x13, x13
ushr v0.2d, v23.2d, #26
mul x16, x14, x14
umulh x17, x14, x14
and v23.16b, v23.16b, v3.16b
mul x3, x15, x15
umulh x11, x15, x15
add v28.2d, v28.2d, v0.2d
adds x5, x5, x2
ushr v1.2d, v27.2d, #25
adcs x6, x6, x8
adcs x7, x7, x9
and v27.16b, v27.16b, v4.16b
adcs x21, x21, x16
adcs x22, x22, x17
add v23.2d, v23.2d, v1.2d
adcs x23, x23, x3
adc x24, x24, x11
ushr v0.2d, v22.2d, #26
mov w11, #38
and v22.16b, v22.16b, v3.16b
mul x2, x11, x21
mul x8, x11, x22
add v27.2d, v27.2d, v0.2d
mul x9, x11, x23
mul x16, x11, x24
ushr v1.2d, v26.2d, #25
umulh x21, x11, x21
umulh x22, x11, x22
and v26.16b, v26.16b, v4.16b
umulh x23, x11, x23
add v22.2d, v22.2d, v1.2d
umulh x24, x11, x24
adds x4, x4, x2
ushr v0.2d, v21.2d, #26
adcs x5, x5, x8
adcs x6, x6, x9
and v21.16b, v21.16b, v3.16b
adcs x7, x7, x16
adc x24, x24, x10
add v26.2d, v26.2d, v0.2d
adds x7, x7, x23
ushr v1.2d, v25.2d, #25
adc x24, x24, x10
mov w11, #19
and v25.16b, v25.16b, v4.16b
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
add v21.2d, v21.2d, v1.2d
mul x17, x17, x11
adds x4, x4, x17
ushr v0.2d, v20.2d, #26
adcs x5, x5, x21
and v20.16b, v20.16b, v3.16b
adcs x6, x6, x22
adc x7, x7, x10
add v25.2d, v25.2d, v0.2d
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
add v20.2d, v20.2d, v2.2d
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
shl v0.2d, v2.2d, #1
ldp x21, x22, [x0, #480]
shl v2.2d, v2.2d, #4
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v20.2d, v20.2d, v0.2d
adcs x13, x5, x22
mov w2, #38
add v20.2d, v20.2d, v2.2d
adcs x14, x6, x23
adcs x15, x7, x24
shl v25.2d, v25.2d, #26
csel x3, x2, x10, hs
add v20.2d, v20.2d, v25.2d
adds x12, x12, x3
adcs x13, x13, x10
shl v26.2d, v26.2d, #26
adc x14, x14, x10
mul x5, x12, x13
add v21.2d, v21.2d, v26.2d
mul x6, x12, x14
mul x7, x12, x15
shl v27.2d, v27.2d, #26
umulh x2, x12, x13
add v22.2d, v22.2d, v27.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v28.2d, v28.2d, #26
mul x16, x13, x14
mul x17, x13, x15
add v23.2d, v23.2d, v28.2d
umulh x3, x13, x14
umulh x11, x13, x15
shl v29.2d, v29.2d, #26
mul x20, x14, x15
umulh x23, x14, x15
add v24.2d, v24.2d, v29.2d
adds x6, x6, x2
ldr q5, [x0, #704]
adcs x7, x7, x8
adc x21, x9, x10
ushr v25.2d, v20.2d, #51
adds x7, x7, x16
adcs x21, x21, x17
and v20.16b, v20.16b, v5.16b
adc x22, x11, x10
adds x21, x21, x3
ushr v26.2d, v21.2d, #51
adcs x22, x22, x20
and v21.16b, v21.16b, v5.16b
adc x23, x23, x10
lsr x24, x23, #63
ushr v27.2d, v22.2d, #51
extr x23, x23, x22, #63
extr x22, x22, x21, #63
and v22.16b, v22.16b, v5.16b
extr x21, x21, x7, #63
extr x7, x7, x6, #63
ushr v28.2d, v23.2d, #51
extr x6, x6, x5, #63
and v23.16b, v23.16b, v5.16b
lsl x5, x5, #1
mul x4, x12, x12
ushr v29.2d, v24.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v24.16b, v24.16b, v5.16b
umulh x9, x13, x13
mul x16, x14, x14
add v21.2d, v21.2d, v25.2d
umulh x17, x14, x14
add v22.2d, v22.2d, v26.2d
mul x3, x15, x15
umulh x11, x15, x15
add v23.2d, v23.2d, v27.2d
adds x5, x5, x2
adcs x6, x6, x8
add v24.2d, v24.2d, v28.2d
adcs x7, x7, x9
adcs x21, x21, x16
add v20.2d, v20.2d, v29.2d
adcs x22, x22, x17
shl v0.2d, v29.2d, #1
adcs x23, x23, x3
adc x24, x24, x11
shl v2.2d, v29.2d, #4
mov w11, #38
mul x2, x11, x21
add v20.2d, v20.2d, v0.2d
mul x8, x11, x22
mul x9, x11, x23
add v20.2d, v20.2d, v2.2d
mul x16, x11, x24
trn1 v0.2d, v20.2d, v21.2d
umulh x21, x11, x21
umulh x22, x11, x22
trn2 v1.2d, v20.2d, v21.2d
umulh x23, x11, x23
umulh x24, x11, x24
str q0, [x0, #1024]
adds x4, x4, x2
adcs x5, x5, x8
str q1, [x0, #1072]
adcs x6, x6, x9
trn1 v0.2d, v22.2d, v23.2d
adcs x7, x7, x16
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x23
adc x24, x24, x10
str q0, [x0, #1040]
mov w11, #19
extr x17, x24, x7, #63
str q1, [x0, #1088]
and x7, x7, #0x7fffffffffffffff
trn1 v0.2d, v24.2d, v24.2d
mul x17, x17, x11
adds x4, x4, x17
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
str q0, [x0, #1056]
adc x7, x7, x10
stp x4, x5, [x0, #160]
str q1, [x0, #1104]
stp x6, x7, [x0, #176]
ldr x2, [x0, #1024]
ldr x3, [x0, #1032]
ldr x8, [x0, #1040]
ldr x9, [x0, #1048]
ldr x16, [x0, #1056]
lsl x17, x3, #51
adds x4, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x5, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x6, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x7, x9, x17
stp x4, x5, [x0, #352]
stp x6, x7, [x0, #368]
ldr x2, [x0, #1072]
ldr x3, [x0, #1080]
ldr x8, [x0, #1088]
ldr x9, [x0, #1096]
ldr x16, [x0, #1104]
lsl x17, x3, #51
adds x21, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x22, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x23, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x24, x9, x17
stp x21, x22, [x0, #384]
stp x23, x24, [x0, #400]
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
.globl lab_h4
lab_h4:
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
ldr q31, [x0, #720]
ldr q30, [x0, #736]
ldp x14, x15, [x0, #240]
ldr q20, [x0, #224]
ldr x3, [x0, #320]
ldr q21, [x0, #256]
mul x4, x3, x12
ldr q22, [x0, #240]
mul x5, x3, x13
ldr q23, [x0, #272]
mul x6, x3, x14
trn1 v24.2d, v20.2d, v21.2d
mul x7, x3, x15
trn2 v25.2d, v20.2d, v21.2d
umulh x2, x3, x12
trn1 v26.2d, v22.2d, v23.2d
umulh x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
umulh x9, x3, x14
and v20.16b, v24.16b, v31.16b
umulh x16, x3, x15
ushr v21.2d, v24.2d, #26
adds x5, x5, x2
and v21.16b, v21.16b, v30.16b
adcs x6, x6, x8
uzp1 v0.4s, v20.4s, v21.4s
adcs x7, x7, x9
shl v20.2d, v25.2d, #13
adc x21, x16, x10
sri v20.2d, v24.2d, #51
ldr x3, [x0, #328]
and v20.16b, v20.16b, v31.16b
ushr v21.2d, v25.2d, #13
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
uzp1 v1.4s, v20.4s, v21.4s
mul x9, x3, x14
ushr v20.2d, v25.2d, #38
mul x16, x3, x15
and v21.16b, v26.16b, v30.16b
adds x5, x5, x2
uzp1 v2.4s, v20.4s, v21.4s
adcs x6, x6, x8
ushr v20.2d, v26.2d, #25
adcs x7, x7, x9
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x16
shl v21.2d, v27.2d, #13
adc x22, x10, x10
sri v21.2d, v26.2d, #51
umulh x2, x3, x12
and v21.16b, v21.16b, v30.16b
umulh x8, x3, x13
uzp1 v3.4s, v20.4s, v21.4s
umulh x9, x3, x14
ushr v20.2d, v27.2d, #12
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
ushr v21.2d, v27.2d, #38
adcs x7, x7, x8
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x9
ext v5.16b, v0.16b, v0.16b, #8
ext v6.16b, v1.16b, v1.16b, #8
adc x22, x22, x16
ext v7.16b, v2.16b, v2.16b, #8
ldr x3, [x0, #336]
ext v8.16b, v3.16b, v3.16b, #8
mul x2, x3, x12
ext v9.16b, v4.16b, v4.16b, #8
mul x8, x3, x13
add v10.4s, v0.4s, v0.4s
mul x9, x3, x14
add v11.4s, v1.4s, v1.4s
mul x16, x3, x15
add v12.4s, v2.4s, v2.4s
adds x6, x6, x2
add v13.4s, v3.4s, v3.4s
adcs x7, x7, x8
add v14.4s, v4.4s, v4.4s
adcs x21, x21, x9
ldr q31, [x0, #752]
adcs x22, x22, x16
mul v15.4s, v0.4s, v31.4s
adc x23, x10, x10
mul v16.4s, v1.4s, v31.4s
umulh x2, x3, x12
mul v17.4s, v2.4s, v31.4s
umulh x8, x3, x13
mul v18.4s, v3.4s, v31.4s
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x7, x7, x2
umlal2 v20.2d, v11.4s, v18.4s
umlal2 v20.2d, v2.4s, v17.4s
adcs x21, x21, x8
add v20.2d, v20.2d, v20.2d
adcs x22, x22, x9
umlal v20.2d, v0.2s, v0.2s
adc x23, x23, x16
umlal v20.2d, v11.2s, v19.2s
ldr x3, [x0, #344]
umlal v20.2d, v12.2s, v18.2s
mul x2, x3, x12
add v30.4s, v5.4s, v5.4s
mul x8, x3, x13
umull v25.2d, v30.2s, v0.2s
mul x9, x3, x14
add v30.4s, v6.4s, v6.4s
mul x16, x3, x15
umlal v25.2d, v30.2s, v19.2s
adds x7, x7, x2
umlal2 v25.2d, v30.4s, v19.4s
adcs x21, x21, x8
add v30.4s, v7.4s, v7.4s
adcs x22, x22, x9
umlal v25.2d, v30.2s, v18.2s
adcs x23, x23, x16
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x10, x10
umull2 v21.2d, v0.4s, v0.4s
umulh x2, x3, x12
umlal2 v21.2d, v11.4s, v19.4s
umulh x8, x3, x13
umlal2 v21.2d, v12.4s, v18.4s
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umulh x16, x3, x15
umlal v21.2d, v12.2s, v19.2s
adds x21, x21, x2
umlal v21.2d, v3.2s, v18.2s
adcs x22, x22, x8
add v30.4s, v5.4s, v5.4s
adcs x23, x23, x9
umull v26.2d, v30.2s, v1.2s
adc x24, x24, x16
umlal2 v26.2d, v30.4s, v1.4s
mov w11, #38
add v30.4s, v7.4s, v7.4s
mul x2, x11, x21
umlal v26.2d, v30.2s, v19.2s
mul x8, x11, x22
umlal2 v26.2d, v30.4s, v19.4s
mul x9, x11, x23
add v30.4s, v8.4s, v8.4s
mul x16, x11, x24
umlal v26.2d, v30.2s, v18.2s
umulh x21, x11, x21
umull2 v22.2d, v10.4s, v1.4s
umulh x22, x11, x22
umlal2 v22.2d, v12.4s, v19.4s
umulh x23, x11, x23
umlal2 v22.2d, v3.4s, v18.4s
umulh x24, x11, x24
add v22.2d, v22.2d, v22.2d
adds x4, x4, x2
umlal v22.2d, v10.2s, v2.2s
adcs x5, x5, x8
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
adcs x6, x6, x9
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x16
umull v27.2d, v30.2s, v2.2s
adc x24, x24, x10
umlal2 v27.2d, v30.4s, v2.4s
adds x7, x7, x23
add v30.4s, v6.4s, v6.4s
adc x24, x24, x10
umlal v27.2d, v30.2s, v1.2s
mov w11, #19
add v30.4s, v8.4s, v8.4s
extr x17, x24, x7, #63
umlal v27.2d, v30.2s, v19.2s
and x7, x7, #0x7fffffffffffffff
umlal2 v27.2d, v30.4s, v19.4s
mul x17, x17, x11
umull2 v23.2d, v10.4s, v2.4s
adds x4, x4, x17
umlal2 v23.2d, v1.4s, v1.4s
adcs x5, x5, x21
umlal2 v23.2d, v13.4s, v19.4s
adcs x6, x6, x22
add v23.2d, v23.2d, v23.2d
adc x7, x7, x10
umlal v23.2d, v10.2s, v3.2s
stp x4, x5, [x0, #448]
umlal v23.2d, v11.2s, v2.2s
stp x6, x7, [x0, #464]
umlal v23.2d, v4.2s, v19.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
umull v28.2d, v30.2s, v3.2s
ldp x14, x15, [x0, #272]
umlal2 v28.2d, v30.4s, v3.4s
ldr x3, [x0, #288]
add v30.4s, v6.4s, v6.4s
mul x4, x3, x12
umlal v28.2d, v30.2s, v2.2s
mul x5, x3, x13
umlal2 v28.2d, v30.4s, v2.4s
mul x6, x3, x14
add v30.4s, v9.4s, v9.4s
mul x7, x3, x15
umlal v28.2d, v30.2s, v19.2s
umulh x2, x3, x12
umull2 v24.2d, v10.4s, v3.4s
umulh x8, x3, x13
umlal2 v24.2d, v11.4s, v2.4s
umulh x9, x3, x14
umlal2 v24.2d, v4.4s, v19.4s
umulh x16, x3, x15
add v24.2d, v24.2d, v24.2d
adds x5, x5, x2
umlal v24.2d, v10.2s, v4.2s
adcs x6, x6, x8
umlal v24.2d, v11.2s, v3.2s
adcs x7, x7, x9
umlal v24.2d, v2.2s, v2.2s
adc x21, x16, x10
add v30.4s, v5.4s, v5.4s
ldr x3, [x0, #296]
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
mul x2, x3, x12
add v30.4s, v6.4s, v6.4s
mul x8, x3, x13
umlal v29.2d, v30.2s, v3.2s
mul x9, x3, x14
umlal2 v29.2d, v30.4s, v3.4s
mul x16, x3, x15
add v30.4s, v7.4s, v7.4s
adds x5, x5, x2
umlal v29.2d, v30.2s, v2.2s
adcs x6, x6, x8
ldr q3, [x0, #720]
adcs x7, x7, x9
ldr q4, [x0, #736]
adcs x21, x21, x16
ushr v2.2d, v29.2d, #25
adc x22, x10, x10
and v29.16b, v29.16b, v4.16b
umulh x2, x3, x12
ushr v0.2d, v24.2d, #26
umulh x8, x3, x13
and v24.16b, v24.16b, v3.16b
umulh x9, x3, x14
add v29.2d, v29.2d, v0.2d
umulh x16, x3, x15
ushr v1.2d, v28.2d, #25
adds x6, x6, x2
and v28.16b, v28.16b, v4.16b
adcs x7, x7, x8
add v24.2d, v24.2d, v1.2d
adcs x21, x21, x9
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
adc x22, x22, x16
add v28.2d, v28.2d, v0.2d
ldr x3, [x0, #304]
ushr v1.2d, v27.2d, #25
mul x2, x3, x12
and v27.16b, v27.16b, v4.16b
mul x8, x3, x13
add v23.2d, v23.2d, v1.2d
mul x9, x3, x14
ushr v0.2d, v22.2d, #26
mul x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x6, x6, x2
add v27.2d, v27.2d, v0.2d
adcs x7, x7, x8
ushr v1.2d, v26.2d, #25
adcs x21, x21, x9
and v26.16b, v26.16b, v4.16b
adcs x22, x22, x16
add v22.2d, v22.2d, v1.2d
adc x23, x10, x10
ushr v0.2d, v21.2d, #26
umulh x2, x3, x12
and v21.16b, v21.16b, v3.16b
umulh x8, x3, x13
add v26.2d, v26.2d, v0.2d
umulh x9, x3, x14
ushr v1.2d, v25.2d, #25
umulh x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
ushr v0.2d, v20.2d, #26
adcs x21, x21, x8
and v20.16b, v20.16b, v3.16b
adcs x22, x22, x9
add v25.2d, v25.2d, v0.2d
adc x23, x23, x16
add v20.2d, v20.2d, v2.2d
ldr x3, [x0, #312]
shl v0.2d, v2.2d, #1
mul x2, x3, x12
shl v2.2d, v2.2d, #4
mul x8, x3, x13
add v20.2d, v20.2d, v0.2d
mul x9, x3, x14
add v20.2d, v20.2d, v2.2d
mul x16, x3, x15
shl v25.2d, v25.2d, #26
adds x7, x7, x2
add v20.2d, v20.2d, v25.2d
adcs x21, x21, x8
shl v26.2d, v26.2d, #26
adcs x22, x22, x9
add v21.2d, v21.2d, v26.2d
adcs x23, x23, x16
shl v27.2d, v27.2d, #26
adc x24, x10, x10
add v22.2d, v22.2d, v27.2d
umulh x2, x3, x12
shl v28.2d, v28.2d, #26
umulh x8, x3, x13
add v23.2d, v23.2d, v28.2d
umulh x9, x3, x14
shl v29.2d, v29.2d, #26
add v24.2d, v24.2d, v29.2d
umulh x16, x3, x15
ldr q5, [x0, #704]
adds x21, x21, x2
ushr v25.2d, v20.2d, #51
adcs x22, x22, x8
and v20.16b, v20.16b, v5.16b
adcs x23, x23, x9
ushr v26.2d, v21.2d, #51
adc x24, x24, x16
and v21.16b, v21.16b, v5.16b
mov w11, #38
ushr v27.2d, v22.2d, #51
mul x2, x11, x21
and v22.16b, v22.16b, v5.16b
mul x8, x11, x22
ushr v28.2d, v23.2d, #51
mul x9, x11, x23
and v23.16b, v23.16b, v5.16b
mul x16, x11, x24
ushr v29.2d, v24.2d, #51
umulh x21, x11, x21
and v24.16b, v24.16b, v5.16b
umulh x22, x11, x22
add v21.2d, v21.2d, v25.2d
umulh x23, x11, x23
add v22.2d, v22.2d, v26.2d
umulh x24, x11, x24
add v23.2d, v23.2d, v27.2d
adds x4, x4, x2
add v24.2d, v24.2d, v28.2d
adcs x5, x5, x8
add v20.2d, v20.2d, v29.2d
shl v0.2d, v29.2d, #1
adcs x6, x6, x9
shl v2.2d, v29.2d, #4
adcs x7, x7, x16
add v20.2d, v20.2d, v0.2d
adc x24, x24, x10
add v20.2d, v20.2d, v2.2d
adds x7, x7, x23
trn1 v0.2d, v20.2d, v21.2d
adc x24, x24, x10
trn2 v1.2d, v20.2d, v21.2d
mov w11, #19
str q0, [x0, #1024]
extr x17, x24, x7, #63
str q1, [x0, #1072]
and x7, x7, #0x7fffffffffffffff
trn1 v0.2d, v22.2d, v23.2d
mul x17, x17, x11
trn2 v1.2d, v22.2d, v23.2d
adds x4, x4, x17
str q0, [x0, #1040]
adcs x5, x5, x21
str q1, [x0, #1088]
adcs x6, x6, x22
trn1 v0.2d, v24.2d, v24.2d
adc x7, x7, x10
trn2 v1.2d, v24.2d, v24.2d
stp x4, x5, [x0, #480]
str q0, [x0, #1056]
stp x6, x7, [x0, #496]
str q1, [x0, #1104]
ldr x2, [x0, #1024]
ldr x3, [x0, #1032]
ldr q31, [x0, #720]
ldr x8, [x0, #1040]
ldr x9, [x0, #1048]
ldr q30, [x0, #736]
ldr x16, [x0, #1056]
ldr q20, [x0, #448]
lsl x17, x3, #51
ldr q21, [x0, #480]
adds x4, x2, x17
ldr q22, [x0, #464]
lsr x3, x3, #13
ldr q23, [x0, #496]
lsl x17, x8, #38
trn1 v24.2d, v20.2d, v21.2d
adcs x5, x3, x17
trn2 v25.2d, v20.2d, v21.2d
lsr x8, x8, #26
lsl x17, x9, #25
trn1 v26.2d, v22.2d, v23.2d
adcs x6, x8, x17
trn2 v27.2d, v22.2d, v23.2d
lsr x9, x9, #39
and v20.16b, v24.16b, v31.16b
lsl x17, x16, #12
ushr v21.2d, v24.2d, #26
adc x7, x9, x17
and v21.16b, v21.16b, v30.16b
stp x4, x5, [x0, #352]
uzp1 v0.4s, v20.4s, v21.4s
stp x6, x7, [x0, #368]
shl v20.2d, v25.2d, #13
ldr x2, [x0, #1072]
ldr x3, [x0, #1080]
sri v20.2d, v24.2d, #51
ldr x8, [x0, #1088]
ldr x9, [x0, #1096]
ldr x16, [x0, #1104]
and v20.16b, v20.16b, v31.16b
lsl x17, x3, #51
ushr v21.2d, v25.2d, #13
adds x21, x2, x17
and v21.16b, v21.16b, v30.16b
lsr x3, x3, #13
uzp1 v1.4s, v20.4s, v21.4s
lsl x17, x8, #38
ushr v20.2d, v25.2d, #38
adcs x22, x3, x17
and v21.16b, v26.16b, v30.16b
lsr x8, x8, #26
uzp1 v2.4s, v20.4s, v21.4s
lsl x17, x9, #25
ushr v20.2d, v26.2d, #25
adcs x23, x8, x17
lsr x9, x9, #39
and v20.16b, v20.16b, v31.16b
lsl x17, x16, #12
shl v21.2d, v27.2d, #13
adc x24, x9, x17
sri v21.2d, v26.2d, #51
stp x21, x22, [x0, #384]
and v21.16b, v21.16b, v30.16b
stp x23, x24, [x0, #400]
uzp1 v3.4s, v20.4s, v21.4s
subs x12, x4, x21
ushr v20.2d, v27.2d, #12
sbcs x13, x5, x22
and v20.16b, v20.16b, v31.16b
mov w2, #38
ushr v21.2d, v27.2d, #38
sbcs x14, x6, x23
sbcs x15, x7, x24
uzp1 v4.4s, v20.4s, v21.4s
csel x3, x10, x2, hs
ldr q28, [x0, #816]
subs x12, x12, x3
ldr q29, [x0, #832]
sbcs x13, x13, x10
trn1 v20.4s, v0.4s, v0.4s
sbcs x14, x14, x10
trn2 v21.4s, v0.4s, v0.4s
sbc x15, x15, x10
add v22.4s, v20.4s, v21.4s
stp x12, x13, [x0, #416]
add v20.4s, v20.4s, v28.4s
stp x14, x15, [x0, #432]
ldp x12, x13, [x0, #384]
sub v20.4s, v20.4s, v21.4s
ldp x14, x15, [x0, #400]
trn1 v0.4s, v22.4s, v20.4s
ldr x3, [x0, #352]
trn1 v20.4s, v1.4s, v1.4s
mul x4, x3, x12
trn2 v21.4s, v1.4s, v1.4s
mul x5, x3, x13
add v22.4s, v20.4s, v21.4s
mul x6, x3, x14
add v20.4s, v20.4s, v29.4s
mul x7, x3, x15
sub v20.4s, v20.4s, v21.4s
umulh x2, x3, x12
trn1 v1.4s, v22.4s, v20.4s
umulh x8, x3, x13
umulh x9, x3, x14
trn1 v20.4s, v2.4s, v2.4s
umulh x16, x3, x15
trn2 v21.4s, v2.4s, v2.4s
adds x5, x5, x2
add v22.4s, v20.4s, v21.4s
adcs x6, x6, x8
add v20.4s, v20.4s, v29.4s
adcs x7, x7, x9
sub v20.4s, v20.4s, v21.4s
adc x21, x16, x10
trn1 v2.4s, v22.4s, v20.4s
ldr x3, [x0, #360]
trn1 v20.4s, v3.4s, v3.4s
mul x2, x3, x12
trn2 v21.4s, v3.4s, v3.4s
mul x8, x3, x13
mul x9, x3, x14
add v22.4s, v20.4s, v21.4s
mul x16, x3, x15
add v20.4s, v20.4s, v29.4s
adds x5, x5, x2
sub v20.4s, v20.4s, v21.4s
adcs x6, x6, x8
trn1 v3.4s, v22.4s, v20.4s
adcs x7, x7, x9
trn1 v20.4s, v4.4s, v4.4s
adcs x21, x21, x16
trn2 v21.4s, v4.4s, v4.4s
adc x22, x10, x10
add v22.4s, v20.4s, v21.4s
umulh x2, x3, x12
add v20.4s, v20.4s, v29.4s
umulh x8, x3, x13
umulh x9, x3, x14
sub v20.4s, v20.4s, v21.4s
umulh x16, x3, x15
trn1 v4.4s, v22.4s, v20.4s
adds x6, x6, x2
ext v5.16b, v0.16b, v0.16b, #8
adcs x7, x7, x8
ext v6.16b, v1.16b, v1.16b, #8
adcs x21, x21, x9
ext v7.16b, v2.16b, v2.16b, #8
adc x22, x22, x16
ext v8.16b, v3.16b, v3.16b, #8
ldr x3, [x0, #368]
ext v9.16b, v4.16b, v4.16b, #8
mul x2, x3, x12
add v10.4s, v0.4s, v0.4s
mul x8, x3, x13
mul x9, x3, x14
add v11.4s, v1.4s, v1.4s
mul x16, x3, x15
add v12.4s, v2.4s, v2.4s
adds x6, x6, x2
add v13.4s, v3.4s, v3.4s
adcs x7, x7, x8
add v14.4s, v4.4s, v4.4s
adcs x21, x21, x9
ldr q31, [x0, #752]
adcs x22, x22, x16
mul v15.4s, v0.4s, v31.4s
adc x23, x10, x10
mul v16.4s, v1.4s, v31.4s
umulh x2, x3, x12
umulh x8, x3, x13
mul v17.4s, v2.4s, v31.4s
umulh x9, x3, x14
mul v18.4s, v3.4s, v31.4s
umulh x16, x3, x15
mul v19.4s, v4.4s, v31.4s
adds x7, x7, x2
umull2 v20.2d, v10.4s, v19.4s
adcs x21, x21, x8
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x23, x23, x16
add v20.2d, v20.2d, v20.2d
ldr x3, [x0, #376]
umlal v20.2d, v0.2s, v0.2s
mul x2, x3, x12
mul x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
mul x9, x3, x14
umlal v20.2d, v12.2s, v18.2s
mul x16, x3, x15
add v30.4s, v5.4s, v5.4s
adds x7, x7, x2
umull v25.2d, v30.2s, v0.2s
adcs x21, x21, x8
add v30.4s, v6.4s, v6.4s
adcs x22, x22, x9
umlal v25.2d, v30.2s, v19.2s
adcs x23, x23, x16
umlal2 v25.2d, v30.4s, v19.4s
adc x24, x10, x10
add v30.4s, v7.4s, v7.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v25.2d, v30.2s, v18.2s
umulh x9, x3, x14
umlal2 v25.2d, v30.4s, v18.4s
umulh x16, x3, x15
umull2 v21.2d, v0.4s, v0.4s
adds x21, x21, x2
umlal2 v21.2d, v11.4s, v19.4s
adcs x22, x22, x8
umlal2 v21.2d, v12.4s, v18.4s
adcs x23, x23, x9
add v21.2d, v21.2d, v21.2d
adc x24, x24, x16
umlal v21.2d, v10.2s, v1.2s
mov w11, #38
umlal v21.2d, v12.2s, v19.2s
mul x2, x11, x21
mul x8, x11, x22
umlal v21.2d, v3.2s, v18.2s
mul x9, x11, x23
add v30.4s, v5.4s, v5.4s
mul x16, x11, x24
umull v26.2d, v30.2s, v1.2s
umulh x21, x11, x21
umlal2 v26.2d, v30.4s, v1.4s
umulh x22, x11, x22
add v30.4s, v7.4s, v7.4s
umulh x23, x11, x23
umlal v26.2d, v30.2s, v19.2s
umulh x24, x11, x24
umlal2 v26.2d, v30.4s, v19.4s
adds x4, x4, x2
add v30.4s, v8.4s, v8.4s
adcs x5, x5, x8
adcs x6, x6, x9
umlal v26.2d, v30.2s, v18.2s
adcs x7, x7, x16
umull2 v22.2d, v10.4s, v1.4s
adc x24, x24, x10
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x23
umlal2 v22.2d, v3.4s, v18.4s
adc x24, x24, x10
add v22.2d, v22.2d, v22.2d
mov w11, #19
umlal v22.2d, v10.2s, v2.2s
extr x17, x24, x7, #63
umlal v22.2d, v1.2s, v1.2s
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x11
umlal v22.2d, v13.2s, v19.2s
adds x4, x4, x17
add v30.4s, v5.4s, v5.4s
adcs x5, x5, x21
umull v27.2d, v30.2s, v2.2s
adcs x6, x6, x22
umlal2 v27.2d, v30.4s, v2.4s
adc x7, x7, x10
add v30.4s, v6.4s, v6.4s
stp x4, x5, [x0, #96]
umlal v27.2d, v30.2s, v1.2s
stp x6, x7, [x0, #112]
add v30.4s, v8.4s, v8.4s
ldp x4, x5, [x0, #352]
umlal v27.2d, v30.2s, v19.2s
ldp x6, x7, [x0, #368]
ldp x12, x13, [x0, #416]
umlal2 v27.2d, v30.4s, v19.4s
ldp x14, x15, [x0, #432]
umull2 v23.2d, v10.4s, v2.4s
movz x11, #56129, lsl #0
umlal2 v23.2d, v1.4s, v1.4s
movk x11, #1, lsl #16
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x12, x11
add v23.2d, v23.2d, v23.2d
mul x3, x13, x11
umlal v23.2d, v10.2s, v3.2s
mul x8, x14, x11
umlal v23.2d, v11.2s, v2.2s
mul x9, x15, x11
umlal v23.2d, v4.2s, v19.2s
umulh x20, x15, x11
adds x4, x4, x2
add v30.4s, v5.4s, v5.4s
adcs x5, x5, x3
umull v28.2d, v30.2s, v3.2s
adcs x6, x6, x8
umlal2 v28.2d, v30.4s, v3.4s
adcs x7, x7, x9
add v30.4s, v6.4s, v6.4s
adc x20, x20, x10
umlal v28.2d, v30.2s, v2.2s
umulh x2, x12, x11
umlal2 v28.2d, v30.4s, v2.4s
umulh x3, x13, x11
add v30.4s, v9.4s, v9.4s
umulh x8, x14, x11
umlal v28.2d, v30.2s, v19.2s
adds x16, x7, x7
adc x9, x20, x20
umull2 v24.2d, v10.4s, v3.4s
lsr x7, x16, #1
umlal2 v24.2d, v11.4s, v2.4s
movz w11, #19, lsl #0
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x9, x11
add v24.2d, v24.2d, v24.2d
adds x12, x4, x9
umlal v24.2d, v10.2s, v4.2s
adcs x13, x5, x2
umlal v24.2d, v11.2s, v3.2s
adcs x14, x6, x3
umlal v24.2d, v2.2s, v2.2s
adc x15, x7, x8
add v30.4s, v5.4s, v5.4s
stp x12, x13, [x0, #128]
stp x14, x15, [x0, #144]
umull v29.2d, v30.2s, v4.2s
ldp x12, x13, [x0, #128]
umlal2 v29.2d, v30.4s, v4.4s
ldp x14, x15, [x0, #144]
add v30.4s, v6.4s, v6.4s
ldr x3, [x0, #416]
umlal v29.2d, v30.2s, v3.2s
mul x4, x3, x12
umlal2 v29.2d, v30.4s, v3.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v29.2d, v30.2s, v2.2s
mul x7, x3, x15
umulh x2, x3, x12
ldr q3, [x0, #720]
umulh x8, x3, x13
ldr q4, [x0, #736]
umulh x9, x3, x14
ushr v2.2d, v29.2d, #25
umulh x16, x3, x15
and v29.16b, v29.16b, v4.16b
adds x5, x5, x2
ushr v0.2d, v24.2d, #26
adcs x6, x6, x8
and v24.16b, v24.16b, v3.16b
adcs x7, x7, x9
add v29.2d, v29.2d, v0.2d
adc x21, x16, x10
ushr v1.2d, v28.2d, #25
ldr x3, [x0, #424]
mul x2, x3, x12
and v28.16b, v28.16b, v4.16b
mul x8, x3, x13
add v24.2d, v24.2d, v1.2d
mul x9, x3, x14
ushr v0.2d, v23.2d, #26
mul x16, x3, x15
and v23.16b, v23.16b, v3.16b
adds x5, x5, x2
add v28.2d, v28.2d, v0.2d
adcs x6, x6, x8
ushr v1.2d, v27.2d, #25
adcs x7, x7, x9
and v27.16b, v27.16b, v4.16b
adcs x21, x21, x16
add v23.2d, v23.2d, v1.2d
adc x22, x10, x10
umulh x2, x3, x12
ushr v0.2d, v22.2d, #26
umulh x8, x3, x13
and v22.16b, v22.16b, v3.16b
umulh x9, x3, x14
add v27.2d, v27.2d, v0.2d
umulh x16, x3, x15
ushr v1.2d, v26.2d, #25
adds x6, x6, x2
and v26.16b, v26.16b, v4.16b
adcs x7, x7, x8
add v22.2d, v22.2d, v1.2d
adcs x21, x21, x9
ushr v0.2d, v21.2d, #26
adc x22, x22, x16
and v21.16b, v21.16b, v3.16b
ldr x3, [x0, #432]
mul x2, x3, x12
add v26.2d, v26.2d, v0.2d
mul x8, x3, x13
ushr v1.2d, v25.2d, #25
mul x9, x3, x14
and v25.16b, v25.16b, v4.16b
mul x16, x3, x15
add v21.2d, v21.2d, v1.2d
adds x6, x6, x2
ushr v0.2d, v20.2d, #26
adcs x7, x7, x8
and v20.16b, v20.16b, v3.16b
adcs x21, x21, x9
add v25.2d, v25.2d, v0.2d
adcs x22, x22, x16
add v20.2d, v20.2d, v2.2d
adc x23, x10, x10
umulh x2, x3, x12
shl v0.2d, v2.2d, #1
umulh x8, x3, x13
shl v2.2d, v2.2d, #4
umulh x9, x3, x14
add v20.2d, v20.2d, v0.2d
umulh x16, x3, x15
add v20.2d, v20.2d, v2.2d
adds x7, x7, x2
shl v25.2d, v25.2d, #26
adcs x21, x21, x8
add v20.2d, v20.2d, v25.2d
adcs x22, x22, x9
shl v26.2d, v26.2d, #26
adc x23, x23, x16
ldr x3, [x0, #440]
add v21.2d, v21.2d, v26.2d
mul x2, x3, x12
shl v27.2d, v27.2d, #26
mul x8, x3, x13
add v22.2d, v22.2d, v27.2d
mul x9, x3, x14
shl v28.2d, v28.2d, #26
mul x16, x3, x15
add v23.2d, v23.2d, v28.2d
adds x7, x7, x2
shl v29.2d, v29.2d, #26
adcs x21, x21, x8
add v24.2d, v24.2d, v29.2d
adcs x22, x22, x9
ldr q5, [x0, #704]
adcs x23, x23, x16
adc x24, x10, x10
ushr v25.2d, v20.2d, #51
umulh x2, x3, x12
and v20.16b, v20.16b, v5.16b
umulh x8, x3, x13
ushr v26.2d, v21.2d, #51
umulh x9, x3, x14
and v21.16b, v21.16b, v5.16b
umulh x16, x3, x15
ushr v27.2d, v22.2d, #51
adds x21, x21, x2
and v22.16b, v22.16b, v5.16b
adcs x22, x22, x8
ushr v28.2d, v23.2d, #51
adcs x23, x23, x9
and v23.16b, v23.16b, v5.16b
adc x24, x24, x16
mov w11, #38
ushr v29.2d, v24.2d, #51
mul x2, x11, x21
and v24.16b, v24.16b, v5.16b
mul x8, x11, x22
add v21.2d, v21.2d, v25.2d
mul x9, x11, x23
add v22.2d, v22.2d, v26.2d
mul x16, x11, x24
add v23.2d, v23.2d, v27.2d
umulh x21, x11, x21
add v24.2d, v24.2d, v28.2d
umulh x22, x11, x22
add v20.2d, v20.2d, v29.2d
umulh x23, x11, x23
shl v0.2d, v29.2d, #1
umulh x24, x11, x24
adds x4, x4, x2
shl v2.2d, v29.2d, #4
adcs x5, x5, x8
add v20.2d, v20.2d, v0.2d
adcs x6, x6, x9
add v20.2d, v20.2d, v2.2d
adcs x7, x7, x16
trn1 v0.2d, v20.2d, v21.2d
adc x24, x24, x10
trn2 v1.2d, v20.2d, v21.2d
adds x7, x7, x23
str q0, [x0, #1120]
adc x24, x24, x10
str q1, [x0, #1168]
mov w11, #19
trn1 v0.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
trn2 v1.2d, v22.2d, v23.2d
mul x17, x17, x11
str q0, [x0, #1136]
adds x4, x4, x17
str q1, [x0, #1184]
adcs x5, x5, x21
trn1 v0.2d, v24.2d, v24.2d
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
adc x7, x7, x10
str q0, [x0, #1152]
stp x4, x5, [x0, #128]
str q1, [x0, #1200]
stp x6, x7, [x0, #144]
ldr x2, [x0, #1120]
ldr x3, [x0, #1128]
ldr x8, [x0, #1136]
ldr x9, [x0, #1144]
ldr x16, [x0, #1152]
lsl x17, x3, #51
adds x4, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x5, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x6, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x7, x9, x17
stp x4, x5, [x0, #160]
stp x6, x7, [x0, #176]
ldr x2, [x0, #1168]
ldr x3, [x0, #1176]
ldr x8, [x0, #1184]
ldr x9, [x0, #1192]
ldr x16, [x0, #1200]
lsl x17, x3, #51
adds x21, x2, x17
lsr x3, x3, #13
lsl x17, x8, #38
adcs x22, x3, x17
lsr x8, x8, #26
lsl x17, x9, #25
adcs x23, x8, x17
lsr x9, x9, #39
lsl x17, x16, #12
adc x24, x9, x17
stp x21, x22, [x0, #192]
stp x23, x24, [x0, #208]
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
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_src(p: *mut u64, n: u64);fn lab_sn5(p: *mut u64, n: u64);fn lab_h1(p: *mut u64, n: u64);fn lab_h1b(p: *mut u64, n: u64);fn lab_h2(p: *mut u64, n: u64);fn lab_h3(p: *mut u64, n: u64);fn lab_h4(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_src"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_src(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn5"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn5(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h1b"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h1b(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h3"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h3(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h4"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h4(p, 100) })); g.finish();
}