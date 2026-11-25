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
.globl lab_sn1
lab_sn1:
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
str x6, [x0, #256]
str x7, [x0, #264]
str x8, [x0, #272]
str x9, [x0, #280]
str x10, [x0, #288]
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
str x1, [x0, #208]
str x2, [x0, #216]
str x3, [x0, #224]
str x4, [x0, #232]
str x5, [x0, #240]
ldp x1, x2, [x0, #352]
ldr q31, [x0, #720]
ldp x3, x4, [x0, #368]
ldr q28, [x0, #400]
ldr x5, [x0, #384]
ldr q29, [x0, #256]
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
ldr q29, [x0, #272]
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
ldr q29, [x0, #288]
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
ldr q29, [x0, #208]
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
ldr q29, [x0, #224]
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
ldr q29, [x0, #240]
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
.globl lab_sq2k
lab_sq2k:
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
add v5.4s, v0.4s, v0.4s
add v6.4s, v1.4s, v1.4s
add v7.4s, v2.4s, v2.4s
add v8.4s, v3.4s, v3.4s
ldr q31, [x0, #752]
mul v9.4s, v1.4s, v31.4s
mul v10.4s, v2.4s, v31.4s
mul v11.4s, v3.4s, v31.4s
mul v12.4s, v4.4s, v31.4s
umull v14.2d, v0.2s, v0.2s
umull2 v19.2d, v0.4s, v0.4s
umlal v14.2d, v6.2s, v12.2s
umlal2 v19.2d, v6.4s, v12.4s
umlal v14.2d, v7.2s, v11.2s
umlal2 v19.2d, v7.4s, v11.4s
umull v15.2d, v5.2s, v1.2s
umull2 v20.2d, v5.4s, v1.4s
umlal v15.2d, v7.2s, v12.2s
umlal2 v20.2d, v7.4s, v12.4s
umlal v15.2d, v3.2s, v11.2s
umlal2 v20.2d, v3.4s, v11.4s
umull v16.2d, v5.2s, v2.2s
umull2 v21.2d, v5.4s, v2.4s
umlal v16.2d, v1.2s, v1.2s
umlal2 v21.2d, v1.4s, v1.4s
umlal v16.2d, v8.2s, v12.2s
umlal2 v21.2d, v8.4s, v12.4s
umull v17.2d, v5.2s, v3.2s
umull2 v22.2d, v5.4s, v3.4s
umlal v17.2d, v6.2s, v2.2s
umlal2 v22.2d, v6.4s, v2.4s
umlal v17.2d, v4.2s, v12.2s
umlal2 v22.2d, v4.4s, v12.4s
umull v18.2d, v5.2s, v4.2s
umull2 v23.2d, v5.4s, v4.4s
umlal v18.2d, v6.2s, v3.2s
umlal2 v23.2d, v6.4s, v3.4s
umlal v18.2d, v2.2s, v2.2s
umlal2 v23.2d, v2.4s, v2.4s
ext v31.16b, v0.16b, v0.16b, #8
add v0.4s, v0.4s, v31.4s
ext v31.16b, v1.16b, v1.16b, #8
add v1.4s, v1.4s, v31.4s
ext v31.16b, v2.16b, v2.16b, #8
add v2.4s, v2.4s, v31.4s
ext v31.16b, v3.16b, v3.16b, #8
add v3.4s, v3.4s, v31.4s
ext v31.16b, v4.16b, v4.16b, #8
add v4.4s, v4.4s, v31.4s
ext v31.16b, v5.16b, v5.16b, #8
add v5.4s, v5.4s, v31.4s
ext v31.16b, v6.16b, v6.16b, #8
add v6.4s, v6.4s, v31.4s
ext v31.16b, v7.16b, v7.16b, #8
add v7.4s, v7.4s, v31.4s
ext v31.16b, v8.16b, v8.16b, #8
add v8.4s, v8.4s, v31.4s
ext v31.16b, v9.16b, v9.16b, #8
add v9.4s, v9.4s, v31.4s
ext v31.16b, v10.16b, v10.16b, #8
add v10.4s, v10.4s, v31.4s
ext v31.16b, v11.16b, v11.16b, #8
add v11.4s, v11.4s, v31.4s
ext v31.16b, v12.16b, v12.16b, #8
add v12.4s, v12.4s, v31.4s
umull v24.2d, v0.2s, v0.2s
umlal v24.2d, v6.2s, v12.2s
umlal v24.2d, v7.2s, v11.2s
umull v25.2d, v5.2s, v1.2s
umlal v25.2d, v7.2s, v12.2s
umlal v25.2d, v3.2s, v11.2s
umull v26.2d, v5.2s, v2.2s
umlal v26.2d, v1.2s, v1.2s
umlal v26.2d, v8.2s, v12.2s
umull v27.2d, v5.2s, v3.2s
umlal v27.2d, v6.2s, v2.2s
umlal v27.2d, v4.2s, v12.2s
umull v28.2d, v5.2s, v4.2s
umlal v28.2d, v6.2s, v3.2s
umlal v28.2d, v2.2s, v2.2s
sub v24.2d, v24.2d, v14.2d
sub v24.2d, v24.2d, v19.2d
sub v25.2d, v25.2d, v15.2d
sub v25.2d, v25.2d, v20.2d
sub v26.2d, v26.2d, v16.2d
sub v26.2d, v26.2d, v21.2d
sub v27.2d, v27.2d, v17.2d
sub v27.2d, v27.2d, v22.2d
sub v28.2d, v28.2d, v18.2d
sub v28.2d, v28.2d, v23.2d
add v15.2d, v15.2d, v19.2d
add v15.2d, v15.2d, v19.2d
add v16.2d, v16.2d, v20.2d
add v16.2d, v16.2d, v20.2d
add v17.2d, v17.2d, v21.2d
add v17.2d, v17.2d, v21.2d
add v18.2d, v18.2d, v22.2d
add v18.2d, v18.2d, v22.2d
shl v0.2d, v23.2d, #1
shl v1.2d, v23.2d, #2
shl v2.2d, v23.2d, #5
add v14.2d, v14.2d, v0.2d
add v1.2d, v1.2d, v2.2d
add v14.2d, v14.2d, v1.2d
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
ushr v0.2d, v18.2d, #26
and v18.16b, v18.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v18.2d, v18.2d, v1.2d
ushr v0.2d, v17.2d, #26
and v17.16b, v17.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v17.2d, v17.2d, v1.2d
ushr v0.2d, v16.2d, #26
and v16.16b, v16.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v16.2d, v16.2d, v1.2d
ushr v0.2d, v15.2d, #26
and v15.16b, v15.16b, v3.16b
add v25.2d, v25.2d, v0.2d
ushr v1.2d, v24.2d, #25
and v24.16b, v24.16b, v4.16b
add v15.2d, v15.2d, v1.2d
ushr v0.2d, v14.2d, #26
and v14.16b, v14.16b, v3.16b
add v24.2d, v24.2d, v0.2d
add v14.2d, v14.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v14.2d, v14.2d, v0.2d
add v14.2d, v14.2d, v2.2d
shl v24.2d, v24.2d, #26
add v14.2d, v14.2d, v24.2d
shl v25.2d, v25.2d, #26
add v15.2d, v15.2d, v25.2d
shl v26.2d, v26.2d, #26
add v16.2d, v16.2d, v26.2d
shl v27.2d, v27.2d, #26
add v17.2d, v17.2d, v27.2d
shl v28.2d, v28.2d, #26
add v18.2d, v18.2d, v28.2d
ldr q5, [x0, #704]
ushr v24.2d, v14.2d, #51
and v14.16b, v14.16b, v5.16b
ushr v25.2d, v15.2d, #51
and v15.16b, v15.16b, v5.16b
ushr v26.2d, v16.2d, #51
and v16.16b, v16.16b, v5.16b
ushr v27.2d, v17.2d, #51
and v17.16b, v17.16b, v5.16b
ushr v28.2d, v18.2d, #51
and v18.16b, v18.16b, v5.16b
add v15.2d, v15.2d, v24.2d
add v16.2d, v16.2d, v25.2d
add v17.2d, v17.2d, v26.2d
add v18.2d, v18.2d, v27.2d
add v14.2d, v14.2d, v28.2d
shl v0.2d, v28.2d, #1
shl v2.2d, v28.2d, #4
add v14.2d, v14.2d, v0.2d
add v14.2d, v14.2d, v2.2d
trn1 v0.2d, v14.2d, v15.2d
trn2 v1.2d, v14.2d, v15.2d
str q0, [x0, #400]
str q1, [x0, #448]
trn1 v0.2d, v16.2d, v17.2d
trn2 v1.2d, v16.2d, v17.2d
str q0, [x0, #416]
str q1, [x0, #464]
trn1 v0.2d, v18.2d, v18.2d
trn2 v1.2d, v18.2d, v18.2d
str q0, [x0, #432]
str q1, [x0, #480]
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
.globl lab_mu2k
lab_mu2k:
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
uzp1 v5.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v6.4s, v29.4s, v28.4s
ldr q28, [x0, #272]
ldr q29, [x0, #368]
trn1 v30.2d, v28.2d, v29.2d
trn2 v28.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v7.4s, v29.4s, v30.4s
and v29.16b, v28.16b, v31.16b
ushr v28.2d, v28.2d, #26
uzp1 v8.4s, v29.4s, v28.4s
ldr q28, [x0, #288]
ldr q29, [x0, #384]
trn1 v30.2d, v28.2d, v29.2d
and v29.16b, v30.16b, v31.16b
ushr v30.2d, v30.2d, #26
uzp1 v9.4s, v29.4s, v30.4s
ldr q31, [x0, #752]
mul v10.4s, v6.4s, v31.4s
mul v11.4s, v7.4s, v31.4s
mul v12.4s, v8.4s, v31.4s
mul v13.4s, v9.4s, v31.4s
umull v14.2d, v0.2s, v5.2s
umull2 v19.2d, v0.4s, v5.4s
umlal v14.2d, v1.2s, v13.2s
umlal2 v19.2d, v1.4s, v13.4s
umlal v14.2d, v2.2s, v12.2s
umlal2 v19.2d, v2.4s, v12.4s
umlal v14.2d, v3.2s, v11.2s
umlal2 v19.2d, v3.4s, v11.4s
umlal v14.2d, v4.2s, v10.2s
umlal2 v19.2d, v4.4s, v10.4s
umull v15.2d, v0.2s, v6.2s
umull2 v20.2d, v0.4s, v6.4s
umlal v15.2d, v1.2s, v5.2s
umlal2 v20.2d, v1.4s, v5.4s
umlal v15.2d, v2.2s, v13.2s
umlal2 v20.2d, v2.4s, v13.4s
umlal v15.2d, v3.2s, v12.2s
umlal2 v20.2d, v3.4s, v12.4s
umlal v15.2d, v4.2s, v11.2s
umlal2 v20.2d, v4.4s, v11.4s
umull v16.2d, v0.2s, v7.2s
umull2 v21.2d, v0.4s, v7.4s
umlal v16.2d, v1.2s, v6.2s
umlal2 v21.2d, v1.4s, v6.4s
umlal v16.2d, v2.2s, v5.2s
umlal2 v21.2d, v2.4s, v5.4s
umlal v16.2d, v3.2s, v13.2s
umlal2 v21.2d, v3.4s, v13.4s
umlal v16.2d, v4.2s, v12.2s
umlal2 v21.2d, v4.4s, v12.4s
umull v17.2d, v0.2s, v8.2s
umull2 v22.2d, v0.4s, v8.4s
umlal v17.2d, v1.2s, v7.2s
umlal2 v22.2d, v1.4s, v7.4s
umlal v17.2d, v2.2s, v6.2s
umlal2 v22.2d, v2.4s, v6.4s
umlal v17.2d, v3.2s, v5.2s
umlal2 v22.2d, v3.4s, v5.4s
umlal v17.2d, v4.2s, v13.2s
umlal2 v22.2d, v4.4s, v13.4s
umull v18.2d, v0.2s, v9.2s
umull2 v23.2d, v0.4s, v9.4s
umlal v18.2d, v1.2s, v8.2s
umlal2 v23.2d, v1.4s, v8.4s
umlal v18.2d, v2.2s, v7.2s
umlal2 v23.2d, v2.4s, v7.4s
umlal v18.2d, v3.2s, v6.2s
umlal2 v23.2d, v3.4s, v6.4s
umlal v18.2d, v4.2s, v5.2s
umlal2 v23.2d, v4.4s, v5.4s
ext v31.16b, v0.16b, v0.16b, #8
add v0.4s, v0.4s, v31.4s
ext v31.16b, v1.16b, v1.16b, #8
add v1.4s, v1.4s, v31.4s
ext v31.16b, v2.16b, v2.16b, #8
add v2.4s, v2.4s, v31.4s
ext v31.16b, v3.16b, v3.16b, #8
add v3.4s, v3.4s, v31.4s
ext v31.16b, v4.16b, v4.16b, #8
add v4.4s, v4.4s, v31.4s
ext v31.16b, v5.16b, v5.16b, #8
add v5.4s, v5.4s, v31.4s
ext v31.16b, v6.16b, v6.16b, #8
add v6.4s, v6.4s, v31.4s
ext v31.16b, v7.16b, v7.16b, #8
add v7.4s, v7.4s, v31.4s
ext v31.16b, v8.16b, v8.16b, #8
add v8.4s, v8.4s, v31.4s
ext v31.16b, v9.16b, v9.16b, #8
add v9.4s, v9.4s, v31.4s
ext v31.16b, v10.16b, v10.16b, #8
add v10.4s, v10.4s, v31.4s
ext v31.16b, v11.16b, v11.16b, #8
add v11.4s, v11.4s, v31.4s
ext v31.16b, v12.16b, v12.16b, #8
add v12.4s, v12.4s, v31.4s
ext v31.16b, v13.16b, v13.16b, #8
add v13.4s, v13.4s, v31.4s
umull v24.2d, v0.2s, v5.2s
umlal v24.2d, v1.2s, v13.2s
umlal v24.2d, v2.2s, v12.2s
umlal v24.2d, v3.2s, v11.2s
umlal v24.2d, v4.2s, v10.2s
umull v25.2d, v0.2s, v6.2s
umlal v25.2d, v1.2s, v5.2s
umlal v25.2d, v2.2s, v13.2s
umlal v25.2d, v3.2s, v12.2s
umlal v25.2d, v4.2s, v11.2s
umull v26.2d, v0.2s, v7.2s
umlal v26.2d, v1.2s, v6.2s
umlal v26.2d, v2.2s, v5.2s
umlal v26.2d, v3.2s, v13.2s
umlal v26.2d, v4.2s, v12.2s
umull v27.2d, v0.2s, v8.2s
umlal v27.2d, v1.2s, v7.2s
umlal v27.2d, v2.2s, v6.2s
umlal v27.2d, v3.2s, v5.2s
umlal v27.2d, v4.2s, v13.2s
umull v28.2d, v0.2s, v9.2s
umlal v28.2d, v1.2s, v8.2s
umlal v28.2d, v2.2s, v7.2s
umlal v28.2d, v3.2s, v6.2s
umlal v28.2d, v4.2s, v5.2s
sub v24.2d, v24.2d, v14.2d
sub v24.2d, v24.2d, v19.2d
sub v25.2d, v25.2d, v15.2d
sub v25.2d, v25.2d, v20.2d
sub v26.2d, v26.2d, v16.2d
sub v26.2d, v26.2d, v21.2d
sub v27.2d, v27.2d, v17.2d
sub v27.2d, v27.2d, v22.2d
sub v28.2d, v28.2d, v18.2d
sub v28.2d, v28.2d, v23.2d
add v15.2d, v15.2d, v19.2d
add v15.2d, v15.2d, v19.2d
add v16.2d, v16.2d, v20.2d
add v16.2d, v16.2d, v20.2d
add v17.2d, v17.2d, v21.2d
add v17.2d, v17.2d, v21.2d
add v18.2d, v18.2d, v22.2d
add v18.2d, v18.2d, v22.2d
shl v0.2d, v23.2d, #1
shl v1.2d, v23.2d, #2
shl v2.2d, v23.2d, #5
add v14.2d, v14.2d, v0.2d
add v1.2d, v1.2d, v2.2d
add v14.2d, v14.2d, v1.2d
ldr q3, [x0, #720]
ldr q4, [x0, #736]
ushr v2.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
ushr v0.2d, v18.2d, #26
and v18.16b, v18.16b, v3.16b
add v28.2d, v28.2d, v0.2d
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
add v18.2d, v18.2d, v1.2d
ushr v0.2d, v17.2d, #26
and v17.16b, v17.16b, v3.16b
add v27.2d, v27.2d, v0.2d
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
add v17.2d, v17.2d, v1.2d
ushr v0.2d, v16.2d, #26
and v16.16b, v16.16b, v3.16b
add v26.2d, v26.2d, v0.2d
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
add v16.2d, v16.2d, v1.2d
ushr v0.2d, v15.2d, #26
and v15.16b, v15.16b, v3.16b
add v25.2d, v25.2d, v0.2d
ushr v1.2d, v24.2d, #25
and v24.16b, v24.16b, v4.16b
add v15.2d, v15.2d, v1.2d
ushr v0.2d, v14.2d, #26
and v14.16b, v14.16b, v3.16b
add v24.2d, v24.2d, v0.2d
add v14.2d, v14.2d, v2.2d
shl v0.2d, v2.2d, #1
shl v2.2d, v2.2d, #4
add v14.2d, v14.2d, v0.2d
add v14.2d, v14.2d, v2.2d
shl v24.2d, v24.2d, #26
add v14.2d, v14.2d, v24.2d
shl v25.2d, v25.2d, #26
add v15.2d, v15.2d, v25.2d
shl v26.2d, v26.2d, #26
add v16.2d, v16.2d, v26.2d
shl v27.2d, v27.2d, #26
add v17.2d, v17.2d, v27.2d
shl v28.2d, v28.2d, #26
add v18.2d, v18.2d, v28.2d
ldr q5, [x0, #704]
ushr v24.2d, v14.2d, #51
and v14.16b, v14.16b, v5.16b
ushr v25.2d, v15.2d, #51
and v15.16b, v15.16b, v5.16b
ushr v26.2d, v16.2d, #51
and v16.16b, v16.16b, v5.16b
ushr v27.2d, v17.2d, #51
and v17.16b, v17.16b, v5.16b
ushr v28.2d, v18.2d, #51
and v18.16b, v18.16b, v5.16b
add v15.2d, v15.2d, v24.2d
add v16.2d, v16.2d, v25.2d
add v17.2d, v17.2d, v26.2d
add v18.2d, v18.2d, v27.2d
add v14.2d, v14.2d, v28.2d
shl v0.2d, v28.2d, #1
shl v2.2d, v28.2d, #4
add v14.2d, v14.2d, v0.2d
add v14.2d, v14.2d, v2.2d
trn1 v0.2d, v14.2d, v15.2d
trn2 v1.2d, v14.2d, v15.2d
str q0, [x0, #16]
str q1, [x0, #64]
trn1 v0.2d, v16.2d, v17.2d
trn2 v1.2d, v16.2d, v17.2d
str q0, [x0, #32]
str q1, [x0, #80]
trn1 v0.2d, v18.2d, v18.2d
trn2 v1.2d, v18.2d, v18.2d
str q0, [x0, #48]
str q1, [x0, #96]
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
.globl lab_sn2
lab_sn2:
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
stp x6, x6, [x0, #256]
stp x7, x7, [x0, #264]
stp x8, x8, [x0, #272]
stp x9, x9, [x0, #280]
stp x10, x10, [x0, #288]
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
stp x1, x2, [x0, #208]
stp x3, x4, [x0, #224]
stp x5, x5, [x0, #240]
ldp x1, x2, [x0, #352]
ldr q31, [x0, #720]
ldp x3, x4, [x0, #368]
ldr q28, [x0, #400]
ldr x5, [x0, #384]
ldr q29, [x0, #256]
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
ldr q29, [x0, #272]
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
ldr q29, [x0, #288]
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
ldr q29, [x0, #208]
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
ldr q29, [x0, #224]
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
ldr q29, [x0, #240]
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
.globl lab_sn3
lab_sn3:
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
and v29.16b, v30.16b, v31.16b
mul x9, x5, x22
ldr x22, [x0, #352]
ushr v30.2d, v30.2d, #26
mul x10, x22, x1
uzp1 v0.4s, v29.4s, v30.4s
umulh x11, x22, x1
and v29.16b, v28.16b, v31.16b
mul x12, x22, x2
umulh x13, x22, x2
ushr v28.2d, v28.2d, #26
mul x14, x22, x3
uzp1 v1.4s, v29.4s, v28.4s
umulh x15, x22, x3
mul x16, x22, x4
ldr q28, [x0, #224]
umulh x17, x22, x4
ldr q29, [x0, #272]
mul x20, x22, x5
trn1 v30.2d, v28.2d, v29.2d
umulh x21, x22, x5
ldr x22, [x0, #360]
trn2 v28.2d, v28.2d, v29.2d
mul x23, x22, x1
and v29.16b, v30.16b, v31.16b
umulh x24, x22, x1
ushr v30.2d, v30.2d, #26
adds x12, x12, x23
adc x13, x13, x24
uzp1 v2.4s, v29.4s, v30.4s
mul x23, x22, x2
and v29.16b, v28.16b, v31.16b
umulh x24, x22, x2
adds x14, x14, x23
ushr v28.2d, v28.2d, #26
adc x15, x15, x24
uzp1 v3.4s, v29.4s, v28.4s
mul x23, x22, x3
ldr q28, [x0, #240]
umulh x24, x22, x3
adds x16, x16, x23
ldr q29, [x0, #288]
adc x17, x17, x24
trn1 v30.2d, v28.2d, v29.2d
mul x23, x22, x4
and v29.16b, v30.16b, v31.16b
umulh x24, x22, x4
adds x20, x20, x23
ushr v30.2d, v30.2d, #26
adc x21, x21, x24
uzp1 v4.4s, v29.4s, v30.4s
mul x23, x22, x9
add v5.4s, v0.4s, v0.4s
umulh x24, x22, x9
adds x10, x10, x23
add v6.4s, v1.4s, v1.4s
adc x11, x11, x24
add v7.4s, v2.4s, v2.4s
ldr x22, [x0, #368]
mul x23, x22, x1
add v8.4s, v3.4s, v3.4s
umulh x24, x22, x1
ldr q31, [x0, #752]
adds x14, x14, x23
mul v9.4s, v1.4s, v31.4s
adc x15, x15, x24
mul x23, x22, x2
mul v10.4s, v2.4s, v31.4s
umulh x24, x22, x2
mul v11.4s, v3.4s, v31.4s
adds x16, x16, x23
mul v12.4s, v4.4s, v31.4s
adc x17, x17, x24
mul x23, x22, x3
umull v14.2d, v0.2s, v0.2s
umulh x24, x22, x3
umull2 v19.2d, v0.4s, v0.4s
adds x20, x20, x23
adc x21, x21, x24
umlal v14.2d, v6.2s, v12.2s
mul x23, x22, x8
umlal2 v19.2d, v6.4s, v12.4s
umulh x24, x22, x8
umlal v14.2d, v7.2s, v11.2s
adds x10, x10, x23
adc x11, x11, x24
umlal2 v19.2d, v7.4s, v11.4s
mul x23, x22, x9
umull v15.2d, v5.2s, v1.2s
umulh x24, x22, x9
umull2 v20.2d, v5.4s, v1.4s
adds x12, x12, x23
adc x13, x13, x24
umlal v15.2d, v7.2s, v12.2s
ldr x22, [x0, #376]
umlal2 v20.2d, v7.4s, v12.4s
mul x23, x22, x1
umlal v15.2d, v3.2s, v11.2s
umulh x24, x22, x1
adds x16, x16, x23
umlal2 v20.2d, v3.4s, v11.4s
adc x17, x17, x24
umull v16.2d, v5.2s, v2.2s
mul x23, x22, x2
umulh x24, x22, x2
umull2 v21.2d, v5.4s, v2.4s
adds x20, x20, x23
umlal v16.2d, v1.2s, v1.2s
adc x21, x21, x24
umlal2 v21.2d, v1.4s, v1.4s
mul x23, x22, x7
umulh x24, x22, x7
umlal v16.2d, v8.2s, v12.2s
adds x10, x10, x23
umlal2 v21.2d, v8.4s, v12.4s
adc x11, x11, x24
umull v17.2d, v5.2s, v3.2s
mul x23, x22, x8
umulh x24, x22, x8
umull2 v22.2d, v5.4s, v3.4s
adds x12, x12, x23
umlal v17.2d, v6.2s, v2.2s
adc x13, x13, x24
mul x23, x22, x9
umlal2 v22.2d, v6.4s, v2.4s
umulh x24, x22, x9
umlal v17.2d, v4.2s, v12.2s
adds x14, x14, x23
umlal2 v22.2d, v4.4s, v12.4s
adc x15, x15, x24
ldr x22, [x0, #384]
umull v18.2d, v5.2s, v4.2s
mul x23, x22, x1
umull2 v23.2d, v5.4s, v4.4s
umulh x24, x22, x1
umlal v18.2d, v6.2s, v3.2s
adds x20, x20, x23
adc x21, x21, x24
umlal2 v23.2d, v6.4s, v3.4s
mul x23, x22, x6
umlal v18.2d, v2.2s, v2.2s
umulh x24, x22, x6
umlal2 v23.2d, v2.4s, v2.4s
adds x10, x10, x23
adc x11, x11, x24
ext v31.16b, v0.16b, v0.16b, #8
mul x23, x22, x7
add v0.4s, v0.4s, v31.4s
umulh x24, x22, x7
adds x12, x12, x23
ext v31.16b, v1.16b, v1.16b, #8
adc x13, x13, x24
add v1.4s, v1.4s, v31.4s
mul x23, x22, x8
ext v31.16b, v2.16b, v2.16b, #8
umulh x24, x22, x8
adds x14, x14, x23
add v2.4s, v2.4s, v31.4s
adc x15, x15, x24
ext v31.16b, v3.16b, v3.16b, #8
mul x23, x22, x9
add v3.4s, v3.4s, v31.4s
umulh x24, x22, x9
adds x16, x16, x23
ext v31.16b, v4.16b, v4.16b, #8
adc x17, x17, x24
add v4.4s, v4.4s, v31.4s
mov x1, #0xffff
movk x1, #0xffff, lsl #16
ext v31.16b, v5.16b, v5.16b, #8
movk x1, #0xffff, lsl #32
add v5.4s, v5.4s, v31.4s
movk x1, #7, lsl #48
ext v31.16b, v6.16b, v6.16b, #8
mov w7, #19
extr x2, x11, x10, #51
add v6.4s, v6.4s, v31.4s
extr x3, x13, x12, #51
ext v31.16b, v7.16b, v7.16b, #8
extr x4, x15, x14, #51
add v7.4s, v7.4s, v31.4s
extr x5, x17, x16, #51
extr x6, x21, x20, #51
ext v31.16b, v8.16b, v8.16b, #8
and x10, x10, x1
add v8.4s, v8.4s, v31.4s
and x12, x12, x1
ext v31.16b, v9.16b, v9.16b, #8
and x14, x14, x1
and x16, x16, x1
add v9.4s, v9.4s, v31.4s
and x20, x20, x1
ext v31.16b, v10.16b, v10.16b, #8
mul x6, x6, x7
add x10, x10, x6
add v10.4s, v10.4s, v31.4s
add x12, x12, x2
ext v31.16b, v11.16b, v11.16b, #8
add x14, x14, x3
add v11.4s, v11.4s, v31.4s
add x16, x16, x4
add x20, x20, x5
ext v31.16b, v12.16b, v12.16b, #8
lsr x2, x10, #51
add v12.4s, v12.4s, v31.4s
lsr x3, x12, #51
umull v24.2d, v0.2s, v0.2s
lsr x4, x14, #51
lsr x5, x16, #51
umlal v24.2d, v6.2s, v12.2s
lsr x6, x20, #51
umlal v24.2d, v7.2s, v11.2s
and x10, x10, x1
and x12, x12, x1
umull v25.2d, v5.2s, v1.2s
and x14, x14, x1
umlal v25.2d, v7.2s, v12.2s
and x16, x16, x1
umlal v25.2d, v3.2s, v11.2s
and x20, x20, x1
mul x6, x6, x7
umull v26.2d, v5.2s, v2.2s
add x10, x10, x6
umlal v26.2d, v1.2s, v1.2s
add x12, x12, x2
umlal v26.2d, v8.2s, v12.2s
add x14, x14, x3
add x16, x16, x4
umull v27.2d, v5.2s, v3.2s
add x20, x20, x5
umlal v27.2d, v6.2s, v2.2s
stp x10, x12, [x0, #352]
umlal v27.2d, v4.2s, v12.2s
stp x14, x16, [x0, #368]
str x20, [x0, #384]
umull v28.2d, v5.2s, v4.2s
ldp x1, x2, [x0, #256]
umlal v28.2d, v6.2s, v3.2s
ldp x3, x4, [x0, #272]
ldr x5, [x0, #288]
umlal v28.2d, v2.2s, v2.2s
mov w22, #19
sub v24.2d, v24.2d, v14.2d
mul x6, x2, x22
sub v24.2d, v24.2d, v19.2d
mul x7, x3, x22
mul x8, x4, x22
sub v25.2d, v25.2d, v15.2d
mul x9, x5, x22
sub v25.2d, v25.2d, v20.2d
ldr x22, [x0, #304]
sub v26.2d, v26.2d, v16.2d
mul x10, x22, x1
umulh x11, x22, x1
sub v26.2d, v26.2d, v21.2d
mul x12, x22, x2
sub v27.2d, v27.2d, v17.2d
umulh x13, x22, x2
mul x14, x22, x3
sub v27.2d, v27.2d, v22.2d
umulh x15, x22, x3
sub v28.2d, v28.2d, v18.2d
mul x16, x22, x4
sub v28.2d, v28.2d, v23.2d
umulh x17, x22, x4
mul x20, x22, x5
add v15.2d, v15.2d, v19.2d
umulh x21, x22, x5
add v15.2d, v15.2d, v19.2d
ldr x22, [x0, #312]
add v16.2d, v16.2d, v20.2d
mul x23, x22, x1
umulh x24, x22, x1
add v16.2d, v16.2d, v20.2d
adds x12, x12, x23
add v17.2d, v17.2d, v21.2d
adc x13, x13, x24
add v17.2d, v17.2d, v21.2d
mul x23, x22, x2
umulh x24, x22, x2
add v18.2d, v18.2d, v22.2d
adds x14, x14, x23
add v18.2d, v18.2d, v22.2d
adc x15, x15, x24
mul x23, x22, x3
shl v0.2d, v23.2d, #1
umulh x24, x22, x3
shl v1.2d, v23.2d, #2
adds x16, x16, x23
shl v2.2d, v23.2d, #5
adc x17, x17, x24
mul x23, x22, x4
add v14.2d, v14.2d, v0.2d
umulh x24, x22, x4
add v1.2d, v1.2d, v2.2d
adds x20, x20, x23
add v14.2d, v14.2d, v1.2d
adc x21, x21, x24
mul x23, x22, x9
ldr q3, [x0, #720]
umulh x24, x22, x9
ldr q4, [x0, #736]
adds x10, x10, x23
adc x11, x11, x24
ushr v2.2d, v28.2d, #25
ldr x22, [x0, #320]
and v28.16b, v28.16b, v4.16b
mul x23, x22, x1
ushr v0.2d, v18.2d, #26
umulh x24, x22, x1
adds x14, x14, x23
and v18.16b, v18.16b, v3.16b
adc x15, x15, x24
add v28.2d, v28.2d, v0.2d
mul x23, x22, x2
ushr v1.2d, v27.2d, #25
umulh x24, x22, x2
adds x16, x16, x23
and v27.16b, v27.16b, v4.16b
adc x17, x17, x24
add v18.2d, v18.2d, v1.2d
mul x23, x22, x3
ushr v0.2d, v17.2d, #26
umulh x24, x22, x3
adds x20, x20, x23
and v17.16b, v17.16b, v3.16b
adc x21, x21, x24
add v27.2d, v27.2d, v0.2d
mul x23, x22, x8
umulh x24, x22, x8
ushr v1.2d, v26.2d, #25
adds x10, x10, x23
and v26.16b, v26.16b, v4.16b
adc x11, x11, x24
add v17.2d, v17.2d, v1.2d
mul x23, x22, x9
umulh x24, x22, x9
ushr v0.2d, v16.2d, #26
adds x12, x12, x23
and v16.16b, v16.16b, v3.16b
adc x13, x13, x24
add v26.2d, v26.2d, v0.2d
ldr x22, [x0, #328]
mul x23, x22, x1
ushr v1.2d, v25.2d, #25
umulh x24, x22, x1
and v25.16b, v25.16b, v4.16b
adds x16, x16, x23
adc x17, x17, x24
add v16.2d, v16.2d, v1.2d
mul x23, x22, x2
ushr v0.2d, v15.2d, #26
umulh x24, x22, x2
and v15.16b, v15.16b, v3.16b
adds x20, x20, x23
adc x21, x21, x24
add v25.2d, v25.2d, v0.2d
mul x23, x22, x7
ushr v1.2d, v24.2d, #25
umulh x24, x22, x7
and v24.16b, v24.16b, v4.16b
adds x10, x10, x23
adc x11, x11, x24
add v15.2d, v15.2d, v1.2d
mul x23, x22, x8
ushr v0.2d, v14.2d, #26
umulh x24, x22, x8
and v14.16b, v14.16b, v3.16b
adds x12, x12, x23
adc x13, x13, x24
add v24.2d, v24.2d, v0.2d
mul x23, x22, x9
add v14.2d, v14.2d, v2.2d
umulh x24, x22, x9
adds x14, x14, x23
shl v0.2d, v2.2d, #1
adc x15, x15, x24
shl v2.2d, v2.2d, #4
ldr x22, [x0, #336]
add v14.2d, v14.2d, v0.2d
mul x23, x22, x1
umulh x24, x22, x1
add v14.2d, v14.2d, v2.2d
adds x20, x20, x23
shl v24.2d, v24.2d, #26
adc x21, x21, x24
add v14.2d, v14.2d, v24.2d
mul x23, x22, x6
umulh x24, x22, x6
shl v25.2d, v25.2d, #26
adds x10, x10, x23
add v15.2d, v15.2d, v25.2d
adc x11, x11, x24
mul x23, x22, x7
shl v26.2d, v26.2d, #26
umulh x24, x22, x7
add v16.2d, v16.2d, v26.2d
adds x12, x12, x23
shl v27.2d, v27.2d, #26
adc x13, x13, x24
mul x23, x22, x8
add v17.2d, v17.2d, v27.2d
umulh x24, x22, x8
shl v28.2d, v28.2d, #26
adds x14, x14, x23
add v18.2d, v18.2d, v28.2d
adc x15, x15, x24
mul x23, x22, x9
ldr q5, [x0, #704]
umulh x24, x22, x9
ushr v24.2d, v14.2d, #51
adds x16, x16, x23
and v14.16b, v14.16b, v5.16b
adc x17, x17, x24
mov x1, #0xffff
ushr v25.2d, v15.2d, #51
movk x1, #0xffff, lsl #16
and v15.16b, v15.16b, v5.16b
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
ushr v26.2d, v16.2d, #51
mov w7, #19
and v16.16b, v16.16b, v5.16b
extr x2, x11, x10, #51
ushr v27.2d, v17.2d, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
and v17.16b, v17.16b, v5.16b
extr x5, x17, x16, #51
ushr v28.2d, v18.2d, #51
extr x6, x21, x20, #51
and v18.16b, v18.16b, v5.16b
and x10, x10, x1
and x12, x12, x1
add v15.2d, v15.2d, v24.2d
and x14, x14, x1
add v16.2d, v16.2d, v25.2d
and x16, x16, x1
and x20, x20, x1
add v17.2d, v17.2d, v26.2d
mul x6, x6, x7
add v18.2d, v18.2d, v27.2d
add x10, x10, x6
add v14.2d, v14.2d, v28.2d
add x12, x12, x2
add x14, x14, x3
shl v0.2d, v28.2d, #1
add x16, x16, x4
shl v2.2d, v28.2d, #4
add x20, x20, x5
add v14.2d, v14.2d, v0.2d
lsr x2, x10, #51
lsr x3, x12, #51
add v14.2d, v14.2d, v2.2d
lsr x4, x14, #51
trn1 v0.2d, v14.2d, v15.2d
lsr x5, x16, #51
trn2 v1.2d, v14.2d, v15.2d
lsr x6, x20, #51
and x10, x10, x1
str q0, [x0, #400]
and x12, x12, x1
str q1, [x0, #448]
and x14, x14, x1
and x16, x16, x1
trn1 v0.2d, v16.2d, v17.2d
and x20, x20, x1
trn2 v1.2d, v16.2d, v17.2d
mul x6, x6, x7
str q0, [x0, #416]
add x10, x10, x6
add x12, x12, x2
str q1, [x0, #464]
add x14, x14, x3
trn1 v0.2d, v18.2d, v18.2d
add x16, x16, x4
trn2 v1.2d, v18.2d, v18.2d
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
stp x6, x6, [x0, #256]
stp x7, x7, [x0, #264]
stp x8, x8, [x0, #272]
stp x9, x9, [x0, #280]
stp x10, x10, [x0, #288]
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
stp x1, x2, [x0, #208]
stp x3, x4, [x0, #224]
stp x5, x5, [x0, #240]
ldp x1, x2, [x0, #352]
ldr q31, [x0, #720]
ldp x3, x4, [x0, #368]
ldr q28, [x0, #400]
ldr x5, [x0, #384]
ldr q29, [x0, #256]
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
uzp1 v0.4s, v29.4s, v30.4s
add x5, x5, x10
mov w22, #19
and v29.16b, v28.16b, v31.16b
add x6, x1, x1
ushr v28.2d, v28.2d, #26
add x7, x2, x2
mul x8, x4, x22
uzp1 v1.4s, v29.4s, v28.4s
mul x9, x5, x22
ldr q28, [x0, #416]
add x24, x9, x9
ldr q29, [x0, #272]
mul x10, x1, x1
umulh x11, x1, x1
trn1 v30.2d, v28.2d, v29.2d
mul x12, x6, x2
trn2 v28.2d, v28.2d, v29.2d
umulh x13, x6, x2
mul x14, x6, x3
and v29.16b, v30.16b, v31.16b
umulh x15, x6, x3
ushr v30.2d, v30.2d, #26
mul x16, x6, x4
uzp1 v2.4s, v29.4s, v30.4s
umulh x17, x6, x4
mul x20, x6, x5
and v29.16b, v28.16b, v31.16b
umulh x21, x6, x5
ushr v28.2d, v28.2d, #26
mul x22, x2, x24
umulh x23, x2, x24
uzp1 v3.4s, v29.4s, v28.4s
adds x10, x10, x22
ldr q28, [x0, #432]
adc x11, x11, x23
ldr q29, [x0, #288]
mul x22, x2, x2
umulh x23, x2, x2
trn1 v30.2d, v28.2d, v29.2d
adds x14, x14, x22
and v29.16b, v30.16b, v31.16b
adc x15, x15, x23
mul x22, x7, x3
ushr v30.2d, v30.2d, #26
umulh x23, x7, x3
uzp1 v4.4s, v29.4s, v30.4s
adds x16, x16, x22
ldr q28, [x0, #448]
adc x17, x17, x23
mul x22, x7, x4
ldr q29, [x0, #208]
umulh x23, x7, x4
trn1 v30.2d, v28.2d, v29.2d
adds x20, x20, x22
adc x21, x21, x23
trn2 v28.2d, v28.2d, v29.2d
mul x22, x3, x24
and v29.16b, v30.16b, v31.16b
umulh x23, x3, x24
ushr v30.2d, v30.2d, #26
adds x12, x12, x22
adc x13, x13, x23
uzp1 v5.4s, v29.4s, v30.4s
mul x22, x3, x3
and v29.16b, v28.16b, v31.16b
umulh x23, x3, x3
adds x20, x20, x22
ushr v28.2d, v28.2d, #26
adc x21, x21, x23
uzp1 v6.4s, v29.4s, v28.4s
mul x22, x4, x24
ldr q28, [x0, #464]
umulh x23, x4, x24
adds x14, x14, x22
ldr q29, [x0, #224]
adc x15, x15, x23
trn1 v30.2d, v28.2d, v29.2d
mul x22, x5, x9
umulh x23, x5, x9
trn2 v28.2d, v28.2d, v29.2d
adds x16, x16, x22
and v29.16b, v30.16b, v31.16b
adc x17, x17, x23
ushr v30.2d, v30.2d, #26
mul x22, x4, x8
umulh x23, x4, x8
uzp1 v7.4s, v29.4s, v30.4s
adds x12, x12, x22
and v29.16b, v28.16b, v31.16b
adc x13, x13, x23
add x8, x8, x8
ushr v28.2d, v28.2d, #26
mul x22, x8, x3
uzp1 v8.4s, v29.4s, v28.4s
umulh x23, x8, x3
ldr q28, [x0, #480]
adds x10, x10, x22
adc x11, x11, x23
ldr q29, [x0, #240]
mov x1, #0xffff
trn1 v30.2d, v28.2d, v29.2d
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
and v29.16b, v30.16b, v31.16b
movk x1, #7, lsl #48
ushr v30.2d, v30.2d, #26
mov w7, #19
uzp1 v9.4s, v29.4s, v30.4s
extr x2, x11, x10, #51
extr x3, x13, x12, #51
ldr q31, [x0, #752]
extr x4, x15, x14, #51
mul v10.4s, v6.4s, v31.4s
extr x5, x17, x16, #51
extr x6, x21, x20, #51
mul v11.4s, v7.4s, v31.4s
and x10, x10, x1
mul v12.4s, v8.4s, v31.4s
and x12, x12, x1
mul v13.4s, v9.4s, v31.4s
and x14, x14, x1
and x16, x16, x1
umull v14.2d, v0.2s, v5.2s
and x20, x20, x1
umull2 v19.2d, v0.4s, v5.4s
mul x6, x6, x7
add x10, x10, x6
umlal v14.2d, v1.2s, v13.2s
add x12, x12, x2
umlal2 v19.2d, v1.4s, v13.4s
add x14, x14, x3
umlal v14.2d, v2.2s, v12.2s
add x16, x16, x4
add x20, x20, x5
umlal2 v19.2d, v2.4s, v12.4s
lsr x2, x10, #51
umlal v14.2d, v3.2s, v11.2s
lsr x3, x12, #51
lsr x4, x14, #51
umlal2 v19.2d, v3.4s, v11.4s
lsr x5, x16, #51
umlal v14.2d, v4.2s, v10.2s
lsr x6, x20, #51
and x10, x10, x1
umlal2 v19.2d, v4.4s, v10.4s
and x12, x12, x1
umull v15.2d, v0.2s, v6.2s
and x14, x14, x1
umull2 v20.2d, v0.4s, v6.4s
and x16, x16, x1
and x20, x20, x1
umlal v15.2d, v1.2s, v5.2s
mul x6, x6, x7
umlal2 v20.2d, v1.4s, v5.4s
add x10, x10, x6
add x12, x12, x2
umlal v15.2d, v2.2s, v13.2s
add x14, x14, x3
umlal2 v20.2d, v2.4s, v13.4s
add x16, x16, x4
umlal v15.2d, v3.2s, v12.2s
add x20, x20, x5
stp x10, x12, [x0, #112]
umlal2 v20.2d, v3.4s, v12.4s
stp x14, x16, [x0, #128]
umlal v15.2d, v4.2s, v11.2s
str x20, [x0, #144]
ldp x1, x2, [x0, #352]
umlal2 v20.2d, v4.4s, v11.4s
ldp x3, x4, [x0, #368]
umull v16.2d, v0.2s, v7.2s
ldr x5, [x0, #384]
umull2 v21.2d, v0.4s, v7.4s
ldp x6, x7, [x0, #304]
ldp x8, x9, [x0, #320]
umlal v16.2d, v1.2s, v6.2s
ldr x10, [x0, #336]
umlal2 v21.2d, v1.4s, v6.4s
mov x24, #0xfffe
movk x24, #0xffff, lsl #16
umlal v16.2d, v2.2s, v5.2s
movk x24, #0xffff, lsl #32
umlal2 v21.2d, v2.4s, v5.4s
movk x24, #0xf, lsl #48
umlal v16.2d, v3.2s, v13.2s
sub x23, x24, #36
add x1, x1, x23
umlal2 v21.2d, v3.4s, v13.4s
sub x1, x1, x6
umlal v16.2d, v4.2s, v12.2s
add x2, x2, x24
sub x2, x2, x7
umlal2 v21.2d, v4.4s, v12.4s
add x3, x3, x24
umull v17.2d, v0.2s, v8.2s
sub x3, x3, x8
umull2 v22.2d, v0.4s, v8.4s
add x4, x4, x24
sub x4, x4, x9
umlal v17.2d, v1.2s, v7.2s
add x5, x5, x24
umlal2 v22.2d, v1.4s, v7.4s
sub x5, x5, x10
mov w22, #19
umlal v17.2d, v2.2s, v6.2s
add x6, x1, x1
umlal2 v22.2d, v2.4s, v6.4s
add x7, x2, x2
umlal v17.2d, v3.2s, v5.2s
mul x8, x4, x22
mul x9, x5, x22
umlal2 v22.2d, v3.4s, v5.4s
add x24, x9, x9
umlal v17.2d, v4.2s, v13.2s
mul x10, x1, x1
umulh x11, x1, x1
umlal2 v22.2d, v4.4s, v13.4s
mul x12, x6, x2
umull v18.2d, v0.2s, v9.2s
umulh x13, x6, x2
umull2 v23.2d, v0.4s, v9.4s
mul x14, x6, x3
umulh x15, x6, x3
umlal v18.2d, v1.2s, v8.2s
mul x16, x6, x4
umlal2 v23.2d, v1.4s, v8.4s
umulh x17, x6, x4
mul x20, x6, x5
umlal v18.2d, v2.2s, v7.2s
umulh x21, x6, x5
umlal2 v23.2d, v2.4s, v7.4s
mul x22, x2, x24
umlal v18.2d, v3.2s, v6.2s
umulh x23, x2, x24
adds x10, x10, x22
umlal2 v23.2d, v3.4s, v6.4s
adc x11, x11, x23
umlal v18.2d, v4.2s, v5.2s
mul x22, x2, x2
umulh x23, x2, x2
umlal2 v23.2d, v4.4s, v5.4s
adds x14, x14, x22
ext v31.16b, v0.16b, v0.16b, #8
adc x15, x15, x23
add v0.4s, v0.4s, v31.4s
mul x22, x7, x3
umulh x23, x7, x3
ext v31.16b, v1.16b, v1.16b, #8
adds x16, x16, x22
add v1.4s, v1.4s, v31.4s
adc x17, x17, x23
mul x22, x7, x4
ext v31.16b, v2.16b, v2.16b, #8
umulh x23, x7, x4
add v2.4s, v2.4s, v31.4s
adds x20, x20, x22
ext v31.16b, v3.16b, v3.16b, #8
adc x21, x21, x23
mul x22, x3, x24
add v3.4s, v3.4s, v31.4s
umulh x23, x3, x24
ext v31.16b, v4.16b, v4.16b, #8
adds x12, x12, x22
adc x13, x13, x23
add v4.4s, v4.4s, v31.4s
mul x22, x3, x3
ext v31.16b, v5.16b, v5.16b, #8
umulh x23, x3, x3
add v5.4s, v5.4s, v31.4s
adds x20, x20, x22
adc x21, x21, x23
ext v31.16b, v6.16b, v6.16b, #8
mul x22, x4, x24
add v6.4s, v6.4s, v31.4s
umulh x23, x4, x24
adds x14, x14, x22
ext v31.16b, v7.16b, v7.16b, #8
adc x15, x15, x23
add v7.4s, v7.4s, v31.4s
mul x22, x5, x9
ext v31.16b, v8.16b, v8.16b, #8
umulh x23, x5, x9
adds x16, x16, x22
add v8.4s, v8.4s, v31.4s
adc x17, x17, x23
ext v31.16b, v9.16b, v9.16b, #8
mul x22, x4, x8
umulh x23, x4, x8
add v9.4s, v9.4s, v31.4s
adds x12, x12, x22
ext v31.16b, v10.16b, v10.16b, #8
adc x13, x13, x23
add v10.4s, v10.4s, v31.4s
add x8, x8, x8
mul x22, x8, x3
ext v31.16b, v11.16b, v11.16b, #8
umulh x23, x8, x3
add v11.4s, v11.4s, v31.4s
adds x10, x10, x22
adc x11, x11, x23
ext v31.16b, v12.16b, v12.16b, #8
mov x1, #0xffff
add v12.4s, v12.4s, v31.4s
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
ext v31.16b, v13.16b, v13.16b, #8
movk x1, #7, lsl #48
add v13.4s, v13.4s, v31.4s
mov w7, #19
umull v24.2d, v0.2s, v5.2s
extr x2, x11, x10, #51
extr x3, x13, x12, #51
umlal v24.2d, v1.2s, v13.2s
extr x4, x15, x14, #51
umlal v24.2d, v2.2s, v12.2s
extr x5, x17, x16, #51
extr x6, x21, x20, #51
umlal v24.2d, v3.2s, v11.2s
and x10, x10, x1
umlal v24.2d, v4.2s, v10.2s
and x12, x12, x1
umull v25.2d, v0.2s, v6.2s
and x14, x14, x1
and x16, x16, x1
umlal v25.2d, v1.2s, v5.2s
and x20, x20, x1
umlal v25.2d, v2.2s, v13.2s
mul x6, x6, x7
add x10, x10, x6
umlal v25.2d, v3.2s, v12.2s
add x12, x12, x2
umlal v25.2d, v4.2s, v11.2s
add x14, x14, x3
umull v26.2d, v0.2s, v7.2s
add x16, x16, x4
add x20, x20, x5
umlal v26.2d, v1.2s, v6.2s
lsr x2, x10, #51
umlal v26.2d, v2.2s, v5.2s
lsr x3, x12, #51
lsr x4, x14, #51
umlal v26.2d, v3.2s, v13.2s
lsr x5, x16, #51
umlal v26.2d, v4.2s, v12.2s
lsr x6, x20, #51
umull v27.2d, v0.2s, v8.2s
and x10, x10, x1
and x12, x12, x1
umlal v27.2d, v1.2s, v7.2s
and x14, x14, x1
umlal v27.2d, v2.2s, v6.2s
and x16, x16, x1
and x20, x20, x1
umlal v27.2d, v3.2s, v5.2s
mul x6, x6, x7
umlal v27.2d, v4.2s, v13.2s
add x10, x10, x6
umull v28.2d, v0.2s, v9.2s
add x12, x12, x2
add x14, x14, x3
umlal v28.2d, v1.2s, v8.2s
add x16, x16, x4
umlal v28.2d, v2.2s, v7.2s
add x20, x20, x5
stp x10, x12, [x0, #160]
umlal v28.2d, v3.2s, v6.2s
stp x14, x16, [x0, #176]
umlal v28.2d, v4.2s, v5.2s
str x20, [x0, #192]
sub v24.2d, v24.2d, v14.2d
ldp x1, x2, [x0, #160]
ldp x3, x4, [x0, #176]
sub v24.2d, v24.2d, v19.2d
ldr x5, [x0, #192]
sub v25.2d, v25.2d, v15.2d
mov w22, #19
mul x6, x2, x22
sub v25.2d, v25.2d, v20.2d
mul x7, x3, x22
sub v26.2d, v26.2d, v16.2d
mul x8, x4, x22
sub v26.2d, v26.2d, v21.2d
mul x9, x5, x22
ldr x22, [x0, #560]
sub v27.2d, v27.2d, v17.2d
mul x10, x22, x1
sub v27.2d, v27.2d, v22.2d
umulh x11, x22, x1
mul x12, x22, x2
sub v28.2d, v28.2d, v18.2d
umulh x13, x22, x2
sub v28.2d, v28.2d, v23.2d
mul x14, x22, x3
add v15.2d, v15.2d, v19.2d
umulh x15, x22, x3
mul x16, x22, x4
add v15.2d, v15.2d, v19.2d
umulh x17, x22, x4
add v16.2d, v16.2d, v20.2d
mul x20, x22, x5
umulh x21, x22, x5
add v16.2d, v16.2d, v20.2d
ldr x22, [x0, #568]
add v17.2d, v17.2d, v21.2d
mul x23, x22, x1
add v17.2d, v17.2d, v21.2d
umulh x24, x22, x1
adds x12, x12, x23
add v18.2d, v18.2d, v22.2d
adc x13, x13, x24
add v18.2d, v18.2d, v22.2d
mul x23, x22, x2
umulh x24, x22, x2
shl v0.2d, v23.2d, #1
adds x14, x14, x23
shl v1.2d, v23.2d, #2
adc x15, x15, x24
shl v2.2d, v23.2d, #5
mul x23, x22, x3
umulh x24, x22, x3
add v14.2d, v14.2d, v0.2d
adds x16, x16, x23
add v1.2d, v1.2d, v2.2d
adc x17, x17, x24
mul x23, x22, x4
add v14.2d, v14.2d, v1.2d
umulh x24, x22, x4
ldr q3, [x0, #720]
adds x20, x20, x23
ldr q4, [x0, #736]
adc x21, x21, x24
mul x23, x22, x9
ushr v2.2d, v28.2d, #25
umulh x24, x22, x9
and v28.16b, v28.16b, v4.16b
adds x10, x10, x23
adc x11, x11, x24
ushr v0.2d, v18.2d, #26
ldr x22, [x0, #576]
and v18.16b, v18.16b, v3.16b
mul x23, x22, x1
add v28.2d, v28.2d, v0.2d
umulh x24, x22, x1
adds x14, x14, x23
ushr v1.2d, v27.2d, #25
adc x15, x15, x24
and v27.16b, v27.16b, v4.16b
mul x23, x22, x2
umulh x24, x22, x2
add v18.2d, v18.2d, v1.2d
adds x16, x16, x23
ushr v0.2d, v17.2d, #26
adc x17, x17, x24
and v17.16b, v17.16b, v3.16b
mul x23, x22, x3
umulh x24, x22, x3
add v27.2d, v27.2d, v0.2d
adds x20, x20, x23
ushr v1.2d, v26.2d, #25
adc x21, x21, x24
mul x23, x22, x8
and v26.16b, v26.16b, v4.16b
umulh x24, x22, x8
add v17.2d, v17.2d, v1.2d
adds x10, x10, x23
adc x11, x11, x24
ushr v0.2d, v16.2d, #26
mul x23, x22, x9
and v16.16b, v16.16b, v3.16b
umulh x24, x22, x9
add v26.2d, v26.2d, v0.2d
adds x12, x12, x23
adc x13, x13, x24
ushr v1.2d, v25.2d, #25
ldr x22, [x0, #584]
and v25.16b, v25.16b, v4.16b
mul x23, x22, x1
umulh x24, x22, x1
add v16.2d, v16.2d, v1.2d
adds x16, x16, x23
ushr v0.2d, v15.2d, #26
adc x17, x17, x24
and v15.16b, v15.16b, v3.16b
mul x23, x22, x2
umulh x24, x22, x2
add v25.2d, v25.2d, v0.2d
adds x20, x20, x23
ushr v1.2d, v24.2d, #25
adc x21, x21, x24
mul x23, x22, x7
and v24.16b, v24.16b, v4.16b
umulh x24, x22, x7
add v15.2d, v15.2d, v1.2d
adds x10, x10, x23
ushr v0.2d, v14.2d, #26
adc x11, x11, x24
mul x23, x22, x8
and v14.16b, v14.16b, v3.16b
umulh x24, x22, x8
add v24.2d, v24.2d, v0.2d
adds x12, x12, x23
adc x13, x13, x24
add v14.2d, v14.2d, v2.2d
mul x23, x22, x9
shl v0.2d, v2.2d, #1
umulh x24, x22, x9
shl v2.2d, v2.2d, #4
adds x14, x14, x23
adc x15, x15, x24
add v14.2d, v14.2d, v0.2d
ldr x22, [x0, #592]
add v14.2d, v14.2d, v2.2d
mul x23, x22, x1
umulh x24, x22, x1
shl v24.2d, v24.2d, #26
adds x20, x20, x23
add v14.2d, v14.2d, v24.2d
adc x21, x21, x24
shl v25.2d, v25.2d, #26
mul x23, x22, x6
umulh x24, x22, x6
add v15.2d, v15.2d, v25.2d
adds x10, x10, x23
shl v26.2d, v26.2d, #26
adc x11, x11, x24
mul x23, x22, x7
add v16.2d, v16.2d, v26.2d
umulh x24, x22, x7
shl v27.2d, v27.2d, #26
adds x12, x12, x23
add v17.2d, v17.2d, v27.2d
adc x13, x13, x24
mul x23, x22, x8
shl v28.2d, v28.2d, #26
umulh x24, x22, x8
add v18.2d, v18.2d, v28.2d
adds x14, x14, x23
adc x15, x15, x24
ldr q5, [x0, #704]
mul x23, x22, x9
ushr v24.2d, v14.2d, #51
umulh x24, x22, x9
and v14.16b, v14.16b, v5.16b
adds x16, x16, x23
adc x17, x17, x24
ushr v25.2d, v15.2d, #51
mov x1, #0xffff
and v15.16b, v15.16b, v5.16b
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
ushr v26.2d, v16.2d, #51
movk x1, #7, lsl #48
and v16.16b, v16.16b, v5.16b
mov w7, #19
ushr v27.2d, v17.2d, #51
extr x2, x11, x10, #51
extr x3, x13, x12, #51
and v17.16b, v17.16b, v5.16b
extr x4, x15, x14, #51
ushr v28.2d, v18.2d, #51
extr x5, x17, x16, #51
extr x6, x21, x20, #51
and v18.16b, v18.16b, v5.16b
and x10, x10, x1
add v15.2d, v15.2d, v24.2d
and x12, x12, x1
add v16.2d, v16.2d, v25.2d
and x14, x14, x1
and x16, x16, x1
add v17.2d, v17.2d, v26.2d
and x20, x20, x1
add v18.2d, v18.2d, v27.2d
mul x6, x6, x7
add x10, x10, x6
add v14.2d, v14.2d, v28.2d
add x12, x12, x2
shl v0.2d, v28.2d, #1
add x14, x14, x3
shl v2.2d, v28.2d, #4
add x16, x16, x4
add x20, x20, x5
add v14.2d, v14.2d, v0.2d
lsr x2, x10, #51
add v14.2d, v14.2d, v2.2d
lsr x3, x12, #51
lsr x4, x14, #51
trn1 v0.2d, v14.2d, v15.2d
lsr x5, x16, #51
trn2 v1.2d, v14.2d, v15.2d
lsr x6, x20, #51
str q0, [x0, #16]
and x10, x10, x1
and x12, x12, x1
str q1, [x0, #64]
and x14, x14, x1
trn1 v0.2d, v16.2d, v17.2d
and x16, x16, x1
and x20, x20, x1
trn2 v1.2d, v16.2d, v17.2d
mul x6, x6, x7
str q0, [x0, #32]
add x10, x10, x6
str q1, [x0, #80]
add x12, x12, x2
add x14, x14, x3
trn1 v0.2d, v18.2d, v18.2d
add x16, x16, x4
trn2 v1.2d, v18.2d, v18.2d
add x20, x20, x5
stp x10, x12, [x0, #160]
str q0, [x0, #48]
stp x14, x16, [x0, #176]
str q1, [x0, #96]
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
.globl lab_sn4
lab_sn4:
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
and v29.16b, v30.16b, v31.16b
mul x9, x5, x22
ldr x22, [x0, #352]
ushr v30.2d, v30.2d, #26
mul x10, x22, x1
uzp1 v0.4s, v29.4s, v30.4s
umulh x11, x22, x1
and v29.16b, v28.16b, v31.16b
mul x12, x22, x2
umulh x13, x22, x2
ushr v28.2d, v28.2d, #26
mul x14, x22, x3
uzp1 v1.4s, v29.4s, v28.4s
umulh x15, x22, x3
mul x16, x22, x4
ldr q28, [x0, #224]
umulh x17, x22, x4
ldr q29, [x0, #272]
mul x20, x22, x5
trn1 v30.2d, v28.2d, v29.2d
umulh x21, x22, x5
ldr x22, [x0, #360]
trn2 v28.2d, v28.2d, v29.2d
mul x23, x22, x1
and v29.16b, v30.16b, v31.16b
umulh x24, x22, x1
ushr v30.2d, v30.2d, #26
adds x12, x12, x23
adc x13, x13, x24
uzp1 v2.4s, v29.4s, v30.4s
mul x23, x22, x2
and v29.16b, v28.16b, v31.16b
umulh x24, x22, x2
adds x14, x14, x23
ushr v28.2d, v28.2d, #26
adc x15, x15, x24
uzp1 v3.4s, v29.4s, v28.4s
mul x23, x22, x3
ldr q28, [x0, #240]
umulh x24, x22, x3
adds x16, x16, x23
ldr q29, [x0, #288]
adc x17, x17, x24
trn1 v30.2d, v28.2d, v29.2d
mul x23, x22, x4
and v29.16b, v30.16b, v31.16b
umulh x24, x22, x4
adds x20, x20, x23
ushr v30.2d, v30.2d, #26
adc x21, x21, x24
uzp1 v4.4s, v29.4s, v30.4s
mul x23, x22, x9
add v5.4s, v0.4s, v0.4s
umulh x24, x22, x9
adds x10, x10, x23
add v6.4s, v1.4s, v1.4s
adc x11, x11, x24
add v7.4s, v2.4s, v2.4s
ldr x22, [x0, #368]
mul x23, x22, x1
add v8.4s, v3.4s, v3.4s
umulh x24, x22, x1
ldr q31, [x0, #752]
adds x14, x14, x23
mul v9.4s, v1.4s, v31.4s
adc x15, x15, x24
mul x23, x22, x2
mul v10.4s, v2.4s, v31.4s
umulh x24, x22, x2
mul v11.4s, v3.4s, v31.4s
adds x16, x16, x23
mul v12.4s, v4.4s, v31.4s
adc x17, x17, x24
mul x23, x22, x3
umull v14.2d, v0.2s, v0.2s
umulh x24, x22, x3
umull2 v19.2d, v0.4s, v0.4s
adds x20, x20, x23
adc x21, x21, x24
umlal v14.2d, v6.2s, v12.2s
mul x23, x22, x8
umlal2 v19.2d, v6.4s, v12.4s
umulh x24, x22, x8
umlal v14.2d, v7.2s, v11.2s
adds x10, x10, x23
adc x11, x11, x24
umlal2 v19.2d, v7.4s, v11.4s
mul x23, x22, x9
umull v15.2d, v5.2s, v1.2s
umulh x24, x22, x9
umull2 v20.2d, v5.4s, v1.4s
adds x12, x12, x23
adc x13, x13, x24
umlal v15.2d, v7.2s, v12.2s
ldr x22, [x0, #376]
umlal2 v20.2d, v7.4s, v12.4s
mul x23, x22, x1
umlal v15.2d, v3.2s, v11.2s
umulh x24, x22, x1
adds x16, x16, x23
umlal2 v20.2d, v3.4s, v11.4s
adc x17, x17, x24
umull v16.2d, v5.2s, v2.2s
mul x23, x22, x2
umulh x24, x22, x2
umull2 v21.2d, v5.4s, v2.4s
adds x20, x20, x23
umlal v16.2d, v1.2s, v1.2s
adc x21, x21, x24
umlal2 v21.2d, v1.4s, v1.4s
mul x23, x22, x7
umulh x24, x22, x7
umlal v16.2d, v8.2s, v12.2s
adds x10, x10, x23
umlal2 v21.2d, v8.4s, v12.4s
adc x11, x11, x24
umull v17.2d, v5.2s, v3.2s
mul x23, x22, x8
umulh x24, x22, x8
umull2 v22.2d, v5.4s, v3.4s
adds x12, x12, x23
umlal v17.2d, v6.2s, v2.2s
adc x13, x13, x24
mul x23, x22, x9
umlal2 v22.2d, v6.4s, v2.4s
umulh x24, x22, x9
umlal v17.2d, v4.2s, v12.2s
adds x14, x14, x23
umlal2 v22.2d, v4.4s, v12.4s
adc x15, x15, x24
ldr x22, [x0, #384]
umull v18.2d, v5.2s, v4.2s
mul x23, x22, x1
umull2 v23.2d, v5.4s, v4.4s
umulh x24, x22, x1
umlal v18.2d, v6.2s, v3.2s
adds x20, x20, x23
adc x21, x21, x24
umlal2 v23.2d, v6.4s, v3.4s
mul x23, x22, x6
umlal v18.2d, v2.2s, v2.2s
umulh x24, x22, x6
umlal2 v23.2d, v2.4s, v2.4s
adds x10, x10, x23
adc x11, x11, x24
ext v31.16b, v0.16b, v0.16b, #8
mul x23, x22, x7
add v0.4s, v0.4s, v31.4s
umulh x24, x22, x7
adds x12, x12, x23
ext v31.16b, v1.16b, v1.16b, #8
adc x13, x13, x24
add v1.4s, v1.4s, v31.4s
mul x23, x22, x8
ext v31.16b, v2.16b, v2.16b, #8
umulh x24, x22, x8
adds x14, x14, x23
add v2.4s, v2.4s, v31.4s
adc x15, x15, x24
ext v31.16b, v3.16b, v3.16b, #8
mul x23, x22, x9
add v3.4s, v3.4s, v31.4s
umulh x24, x22, x9
adds x16, x16, x23
ext v31.16b, v4.16b, v4.16b, #8
adc x17, x17, x24
add v4.4s, v4.4s, v31.4s
mov x1, #0xffff
movk x1, #0xffff, lsl #16
ext v31.16b, v5.16b, v5.16b, #8
movk x1, #0xffff, lsl #32
add v5.4s, v5.4s, v31.4s
movk x1, #7, lsl #48
ext v31.16b, v6.16b, v6.16b, #8
mov w7, #19
extr x2, x11, x10, #51
add v6.4s, v6.4s, v31.4s
extr x3, x13, x12, #51
ext v31.16b, v7.16b, v7.16b, #8
extr x4, x15, x14, #51
add v7.4s, v7.4s, v31.4s
extr x5, x17, x16, #51
extr x6, x21, x20, #51
ext v31.16b, v8.16b, v8.16b, #8
and x10, x10, x1
add v8.4s, v8.4s, v31.4s
and x12, x12, x1
ext v31.16b, v9.16b, v9.16b, #8
and x14, x14, x1
and x16, x16, x1
add v9.4s, v9.4s, v31.4s
and x20, x20, x1
ext v31.16b, v10.16b, v10.16b, #8
mul x6, x6, x7
add x10, x10, x6
add v10.4s, v10.4s, v31.4s
add x12, x12, x2
ext v31.16b, v11.16b, v11.16b, #8
add x14, x14, x3
add v11.4s, v11.4s, v31.4s
add x16, x16, x4
add x20, x20, x5
ext v31.16b, v12.16b, v12.16b, #8
lsr x2, x10, #51
add v12.4s, v12.4s, v31.4s
lsr x3, x12, #51
umull v24.2d, v0.2s, v0.2s
lsr x4, x14, #51
lsr x5, x16, #51
umlal v24.2d, v6.2s, v12.2s
lsr x6, x20, #51
umlal v24.2d, v7.2s, v11.2s
and x10, x10, x1
and x12, x12, x1
umull v25.2d, v5.2s, v1.2s
and x14, x14, x1
umlal v25.2d, v7.2s, v12.2s
and x16, x16, x1
umlal v25.2d, v3.2s, v11.2s
and x20, x20, x1
mul x6, x6, x7
umull v26.2d, v5.2s, v2.2s
add x10, x10, x6
umlal v26.2d, v1.2s, v1.2s
add x12, x12, x2
umlal v26.2d, v8.2s, v12.2s
add x14, x14, x3
add x16, x16, x4
umull v27.2d, v5.2s, v3.2s
add x20, x20, x5
umlal v27.2d, v6.2s, v2.2s
stp x10, x12, [x0, #352]
umlal v27.2d, v4.2s, v12.2s
stp x14, x16, [x0, #368]
str x20, [x0, #384]
umull v28.2d, v5.2s, v4.2s
ldp x1, x2, [x0, #256]
umlal v28.2d, v6.2s, v3.2s
ldp x3, x4, [x0, #272]
ldr x5, [x0, #288]
umlal v28.2d, v2.2s, v2.2s
mov w22, #19
sub v24.2d, v24.2d, v14.2d
mul x6, x2, x22
sub v24.2d, v24.2d, v19.2d
mul x7, x3, x22
mul x8, x4, x22
sub v25.2d, v25.2d, v15.2d
mul x9, x5, x22
sub v25.2d, v25.2d, v20.2d
ldr x22, [x0, #304]
sub v26.2d, v26.2d, v16.2d
mul x10, x22, x1
umulh x11, x22, x1
sub v26.2d, v26.2d, v21.2d
mul x12, x22, x2
sub v27.2d, v27.2d, v17.2d
umulh x13, x22, x2
mul x14, x22, x3
sub v27.2d, v27.2d, v22.2d
umulh x15, x22, x3
sub v28.2d, v28.2d, v18.2d
mul x16, x22, x4
sub v28.2d, v28.2d, v23.2d
umulh x17, x22, x4
mul x20, x22, x5
add v15.2d, v15.2d, v19.2d
umulh x21, x22, x5
add v15.2d, v15.2d, v19.2d
ldr x22, [x0, #312]
add v16.2d, v16.2d, v20.2d
mul x23, x22, x1
umulh x24, x22, x1
add v16.2d, v16.2d, v20.2d
adds x12, x12, x23
add v17.2d, v17.2d, v21.2d
adc x13, x13, x24
add v17.2d, v17.2d, v21.2d
mul x23, x22, x2
umulh x24, x22, x2
add v18.2d, v18.2d, v22.2d
adds x14, x14, x23
add v18.2d, v18.2d, v22.2d
adc x15, x15, x24
mul x23, x22, x3
shl v0.2d, v23.2d, #1
umulh x24, x22, x3
shl v1.2d, v23.2d, #2
adds x16, x16, x23
shl v2.2d, v23.2d, #5
adc x17, x17, x24
mul x23, x22, x4
add v14.2d, v14.2d, v0.2d
umulh x24, x22, x4
add v1.2d, v1.2d, v2.2d
adds x20, x20, x23
add v14.2d, v14.2d, v1.2d
adc x21, x21, x24
mul x23, x22, x9
ldr q3, [x0, #720]
umulh x24, x22, x9
ldr q4, [x0, #736]
adds x10, x10, x23
adc x11, x11, x24
ushr v2.2d, v28.2d, #25
ldr x22, [x0, #320]
and v28.16b, v28.16b, v4.16b
mul x23, x22, x1
ushr v0.2d, v18.2d, #26
umulh x24, x22, x1
adds x14, x14, x23
and v18.16b, v18.16b, v3.16b
adc x15, x15, x24
add v28.2d, v28.2d, v0.2d
mul x23, x22, x2
ushr v1.2d, v27.2d, #25
umulh x24, x22, x2
adds x16, x16, x23
and v27.16b, v27.16b, v4.16b
adc x17, x17, x24
add v18.2d, v18.2d, v1.2d
mul x23, x22, x3
ushr v0.2d, v17.2d, #26
umulh x24, x22, x3
adds x20, x20, x23
and v17.16b, v17.16b, v3.16b
adc x21, x21, x24
add v27.2d, v27.2d, v0.2d
mul x23, x22, x8
umulh x24, x22, x8
ushr v1.2d, v26.2d, #25
adds x10, x10, x23
and v26.16b, v26.16b, v4.16b
adc x11, x11, x24
add v17.2d, v17.2d, v1.2d
mul x23, x22, x9
umulh x24, x22, x9
ushr v0.2d, v16.2d, #26
adds x12, x12, x23
and v16.16b, v16.16b, v3.16b
adc x13, x13, x24
add v26.2d, v26.2d, v0.2d
ldr x22, [x0, #328]
mul x23, x22, x1
ushr v1.2d, v25.2d, #25
umulh x24, x22, x1
and v25.16b, v25.16b, v4.16b
adds x16, x16, x23
adc x17, x17, x24
add v16.2d, v16.2d, v1.2d
mul x23, x22, x2
ushr v0.2d, v15.2d, #26
umulh x24, x22, x2
and v15.16b, v15.16b, v3.16b
adds x20, x20, x23
adc x21, x21, x24
add v25.2d, v25.2d, v0.2d
mul x23, x22, x7
ushr v1.2d, v24.2d, #25
umulh x24, x22, x7
and v24.16b, v24.16b, v4.16b
adds x10, x10, x23
adc x11, x11, x24
add v15.2d, v15.2d, v1.2d
mul x23, x22, x8
ushr v0.2d, v14.2d, #26
umulh x24, x22, x8
and v14.16b, v14.16b, v3.16b
adds x12, x12, x23
adc x13, x13, x24
add v24.2d, v24.2d, v0.2d
mul x23, x22, x9
add v14.2d, v14.2d, v2.2d
umulh x24, x22, x9
adds x14, x14, x23
shl v0.2d, v2.2d, #1
adc x15, x15, x24
shl v2.2d, v2.2d, #4
ldr x22, [x0, #336]
add v14.2d, v14.2d, v0.2d
mul x23, x22, x1
umulh x24, x22, x1
add v14.2d, v14.2d, v2.2d
adds x20, x20, x23
shl v24.2d, v24.2d, #26
adc x21, x21, x24
add v14.2d, v14.2d, v24.2d
mul x23, x22, x6
umulh x24, x22, x6
shl v25.2d, v25.2d, #26
adds x10, x10, x23
add v15.2d, v15.2d, v25.2d
adc x11, x11, x24
mul x23, x22, x7
shl v26.2d, v26.2d, #26
umulh x24, x22, x7
add v16.2d, v16.2d, v26.2d
adds x12, x12, x23
shl v27.2d, v27.2d, #26
adc x13, x13, x24
mul x23, x22, x8
add v17.2d, v17.2d, v27.2d
umulh x24, x22, x8
shl v28.2d, v28.2d, #26
adds x14, x14, x23
add v18.2d, v18.2d, v28.2d
adc x15, x15, x24
mul x23, x22, x9
ldr q5, [x0, #704]
umulh x24, x22, x9
ushr v24.2d, v14.2d, #51
adds x16, x16, x23
and v14.16b, v14.16b, v5.16b
adc x17, x17, x24
mov x1, #0xffff
ushr v25.2d, v15.2d, #51
movk x1, #0xffff, lsl #16
and v15.16b, v15.16b, v5.16b
movk x1, #0xffff, lsl #32
movk x1, #7, lsl #48
ushr v26.2d, v16.2d, #51
mov w7, #19
and v16.16b, v16.16b, v5.16b
extr x2, x11, x10, #51
ushr v27.2d, v17.2d, #51
extr x3, x13, x12, #51
extr x4, x15, x14, #51
and v17.16b, v17.16b, v5.16b
extr x5, x17, x16, #51
ushr v28.2d, v18.2d, #51
extr x6, x21, x20, #51
and v18.16b, v18.16b, v5.16b
and x10, x10, x1
and x12, x12, x1
add v15.2d, v15.2d, v24.2d
and x14, x14, x1
add v16.2d, v16.2d, v25.2d
and x16, x16, x1
and x20, x20, x1
add v17.2d, v17.2d, v26.2d
mul x6, x6, x7
add v18.2d, v18.2d, v27.2d
add x10, x10, x6
add v14.2d, v14.2d, v28.2d
add x12, x12, x2
add x14, x14, x3
shl v0.2d, v28.2d, #1
add x16, x16, x4
shl v2.2d, v28.2d, #4
add x20, x20, x5
add v14.2d, v14.2d, v0.2d
lsr x2, x10, #51
lsr x3, x12, #51
add v14.2d, v14.2d, v2.2d
lsr x4, x14, #51
trn1 v0.2d, v14.2d, v15.2d
lsr x5, x16, #51
trn2 v1.2d, v14.2d, v15.2d
lsr x6, x20, #51
and x10, x10, x1
str q0, [x0, #400]
and x12, x12, x1
str q1, [x0, #448]
and x14, x14, x1
and x16, x16, x1
trn1 v0.2d, v16.2d, v17.2d
and x20, x20, x1
trn2 v1.2d, v16.2d, v17.2d
mul x6, x6, x7
str q0, [x0, #416]
add x10, x10, x6
add x12, x12, x2
str q1, [x0, #464]
add x14, x14, x3
trn1 v0.2d, v18.2d, v18.2d
add x16, x16, x4
trn2 v1.2d, v18.2d, v18.2d
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
ldr q20, [x0, #352]
ldr x10, [x0, #480]
mov x24, #0xfffe
ldr q21, [x0, #304]
movk x24, #0xffff, lsl #16
movk x24, #0xffff, lsl #32
add v22.2d, v20.2d, v21.2d
movk x24, #0xf, lsl #48
add v20.2d, v20.2d, v30.2d
sub x23, x24, #36
sub x6, x1, x6
sub v20.2d, v20.2d, v21.2d
add x6, x6, x23
trn1 v23.2d, v22.2d, v20.2d
sub x7, x2, x7
add x7, x7, x24
trn2 v24.2d, v22.2d, v20.2d
sub x8, x3, x8
add x8, x8, x24
and v25.16b, v23.16b, v31.16b
sub x9, x4, x9
ushr v23.2d, v23.2d, #26
add x9, x9, x24
sub x10, x5, x10
uzp1 v0.4s, v25.4s, v23.4s
add x10, x10, x24
and v25.16b, v24.16b, v31.16b
str x6, [x0, #256]
str x7, [x0, #264]
ushr v24.2d, v24.2d, #26
str x8, [x0, #272]
str x9, [x0, #280]
uzp1 v1.4s, v25.4s, v24.4s
str x10, [x0, #288]
ldr q20, [x0, #368]
mov w16, #0xdb41
movk w16, #1, lsl #16
ldr q21, [x0, #320]
mov x17, #0xffff
movk x17, #0xffff, lsl #16
add v22.2d, v20.2d, v21.2d
movk x17, #0xffff, lsl #32
add v20.2d, v20.2d, v29.2d
movk x17, #7, lsl #48
umulh x11, x6, x16
sub v20.2d, v20.2d, v21.2d
umulh x12, x7, x16
trn1 v23.2d, v22.2d, v20.2d
umulh x13, x8, x16
umulh x14, x9, x16
trn2 v24.2d, v22.2d, v20.2d
umulh x15, x10, x16
mul x6, x6, x16
and v25.16b, v23.16b, v31.16b
mul x7, x7, x16
ushr v23.2d, v23.2d, #26
mul x8, x8, x16
mul x9, x9, x16
uzp1 v2.4s, v25.4s, v23.4s
mul x10, x10, x16
and v25.16b, v24.16b, v31.16b
extr x11, x11, x6, #51
extr x12, x12, x7, #51
ushr v24.2d, v24.2d, #26
extr x13, x13, x8, #51
extr x14, x14, x9, #51
uzp1 v3.4s, v25.4s, v24.4s
extr x15, x15, x10, #51
ldr q20, [x0, #384]
and x6, x6, x17
and x7, x7, x17
ldr q21, [x0, #336]
and x8, x8, x17
and x9, x9, x17
add v22.2d, v20.2d, v21.2d
and x10, x10, x17
add v20.2d, v20.2d, v29.2d
mov w16, #19
mul x15, x15, x16
sub v20.2d, v20.2d, v21.2d
add x1, x1, x6
trn1 v23.2d, v22.2d, v20.2d
add x2, x2, x7
add x3, x3, x8
and v25.16b, v23.16b, v31.16b
add x4, x4, x9
add x5, x5, x10
ushr v23.2d, v23.2d, #26
add x1, x1, x15
uzp1 v4.4s, v25.4s, v23.4s
add x2, x2, x11
add x3, x3, x12
add v5.4s, v0.4s, v0.4s
add x4, x4, x13
add v6.4s, v1.4s, v1.4s
add x5, x5, x14
str x1, [x0, #208]
add v7.4s, v2.4s, v2.4s
str x2, [x0, #216]
str x3, [x0, #224]
add v8.4s, v3.4s, v3.4s
str x4, [x0, #232]
ldr q31, [x0, #752]
str x5, [x0, #240]
ldp x1, x2, [x0, #448]
mul v9.4s, v1.4s, v31.4s
ldp x3, x4, [x0, #464]
ldr x5, [x0, #480]
mul v10.4s, v2.4s, v31.4s
mov w22, #19
mul v11.4s, v3.4s, v31.4s
mul x6, x2, x22
mul x7, x3, x22
mul v12.4s, v4.4s, v31.4s
mul x8, x4, x22
umull v14.2d, v0.2s, v0.2s
mul x9, x5, x22
ldr x22, [x0, #400]
umull2 v19.2d, v0.4s, v0.4s
mul x10, x22, x1
umulh x11, x22, x1
umlal v14.2d, v6.2s, v12.2s
mul x12, x22, x2
umlal2 v19.2d, v6.4s, v12.4s
umulh x13, x22, x2
mul x14, x22, x3
umlal v14.2d, v7.2s, v11.2s
umulh x15, x22, x3
umlal2 v19.2d, v7.4s, v11.4s
mul x16, x22, x4
umulh x17, x22, x4
umull v15.2d, v5.2s, v1.2s
mul x20, x22, x5
umulh x21, x22, x5
umull2 v20.2d, v5.4s, v1.4s
ldr x22, [x0, #408]
umlal v15.2d, v7.2s, v12.2s
mul x23, x22, x1
umulh x24, x22, x1
umlal2 v20.2d, v7.4s, v12.4s
adds x12, x12, x23
umlal v15.2d, v3.2s, v11.2s
adc x13, x13, x24
mul x23, x22, x2
umlal2 v20.2d, v3.4s, v11.4s
umulh x24, x22, x2
adds x14, x14, x23
umull v16.2d, v5.2s, v2.2s
adc x15, x15, x24
umull2 v21.2d, v5.4s, v2.4s
mul x23, x22, x3
umulh x24, x22, x3
umlal v16.2d, v1.2s, v1.2s
adds x16, x16, x23
adc x17, x17, x24
umlal2 v21.2d, v1.4s, v1.4s
mul x23, x22, x4
umlal v16.2d, v8.2s, v12.2s
umulh x24, x22, x4
adds x20, x20, x23
umlal2 v21.2d, v8.4s, v12.4s
adc x21, x21, x24
umull v17.2d, v5.2s, v3.2s
mul x23, x22, x9
umulh x24, x22, x9
umull2 v22.2d, v5.4s, v3.4s
adds x10, x10, x23
adc x11, x11, x24
umlal v17.2d, v6.2s, v2.2s
ldr x22, [x0, #416]
umlal2 v22.2d, v6.4s, v2.4s
mul x23, x22, x1
umulh x24, x22, x1
umlal v17.2d, v4.2s, v12.2s
adds x14, x14, x23
umlal2 v22.2d, v4.4s, v12.4s
adc x15, x15, x24
mul x23, x22, x2
umull v18.2d, v5.2s, v4.2s
umulh x24, x22, x2
adds x16, x16, x23
umull2 v23.2d, v5.4s, v4.4s
adc x17, x17, x24
umlal v18.2d, v6.2s, v3.2s
mul x23, x22, x3
umulh x24, x22, x3
umlal2 v23.2d, v6.4s, v3.4s
adds x20, x20, x23
adc x21, x21, x24
umlal v18.2d, v2.2s, v2.2s
mul x23, x22, x8
umlal2 v23.2d, v2.4s, v2.4s
umulh x24, x22, x8
adds x10, x10, x23
ext v31.16b, v0.16b, v0.16b, #8
adc x11, x11, x24
add v0.4s, v0.4s, v31.4s
mul x23, x22, x9
umulh x24, x22, x9
ext v31.16b, v1.16b, v1.16b, #8
adds x12, x12, x23
adc x13, x13, x24
add v1.4s, v1.4s, v31.4s
ldr x22, [x0, #424]
ext v31.16b, v2.16b, v2.16b, #8
mul x23, x22, x1
umulh x24, x22, x1
add v2.4s, v2.4s, v31.4s
adds x16, x16, x23
ext v31.16b, v3.16b, v3.16b, #8
adc x17, x17, x24
mul x23, x22, x2
add v3.4s, v3.4s, v31.4s
umulh x24, x22, x2
adds x20, x20, x23
ext v31.16b, v4.16b, v4.16b, #8
adc x21, x21, x24
add v4.4s, v4.4s, v31.4s
mul x23, x22, x7
umulh x24, x22, x7
ext v31.16b, v5.16b, v5.16b, #8
adds x10, x10, x23
adc x11, x11, x24
add v5.4s, v5.4s, v31.4s
mul x23, x22, x8
ext v31.16b, v6.16b, v6.16b, #8
umulh x24, x22, x8
adds x12, x12, x23
add v6.4s, v6.4s, v31.4s
adc x13, x13, x24
ext v31.16b, v7.16b, v7.16b, #8
mul x23, x22, x9
umulh x24, x22, x9
add v7.4s, v7.4s, v31.4s
adds x14, x14, x23
adc x15, x15, x24
ext v31.16b, v8.16b, v8.16b, #8
ldr x22, [x0, #432]
add v8.4s, v8.4s, v31.4s
mul x23, x22, x1
umulh x24, x22, x1
ext v31.16b, v9.16b, v9.16b, #8
adds x20, x20, x23
add v9.4s, v9.4s, v31.4s
adc x21, x21, x24
mul x23, x22, x6
ext v31.16b, v10.16b, v10.16b, #8
umulh x24, x22, x6
adds x10, x10, x23
add v10.4s, v10.4s, v31.4s
adc x11, x11, x24
ext v31.16b, v11.16b, v11.16b, #8
mul x23, x22, x7
umulh x24, x22, x7
add v11.4s, v11.4s, v31.4s
adds x12, x12, x23
ext v31.16b, v12.16b, v12.16b, #8
adc x13, x13, x24
mul x23, x22, x8
add v12.4s, v12.4s, v31.4s
umulh x24, x22, x8
adds x14, x14, x23
umull v24.2d, v0.2s, v0.2s
adc x15, x15, x24
umlal v24.2d, v6.2s, v12.2s
mul x23, x22, x9
umulh x24, x22, x9
umlal v24.2d, v7.2s, v11.2s
adds x16, x16, x23
adc x17, x17, x24
umull v25.2d, v5.2s, v1.2s
mov x1, #0xffff
umlal v25.2d, v7.2s, v12.2s
movk x1, #0xffff, lsl #16
movk x1, #0xffff, lsl #32
umlal v25.2d, v3.2s, v11.2s
movk x1, #7, lsl #48
umull v26.2d, v5.2s, v2.2s
mov w7, #19
extr x2, x11, x10, #51
umlal v26.2d, v1.2s, v1.2s
extr x3, x13, x12, #51
extr x4, x15, x14, #51
umlal v26.2d, v8.2s, v12.2s
extr x5, x17, x16, #51
umull v27.2d, v5.2s, v3.2s
extr x6, x21, x20, #51
and x10, x10, x1
umlal v27.2d, v6.2s, v2.2s
and x12, x12, x1
umlal v27.2d, v4.2s, v12.2s
and x14, x14, x1
and x16, x16, x1
umull v28.2d, v5.2s, v4.2s
and x20, x20, x1
mul x6, x6, x7
umlal v28.2d, v6.2s, v3.2s
add x10, x10, x6
umlal v28.2d, v2.2s, v2.2s
add x12, x12, x2
add x14, x14, x3
sub v24.2d, v24.2d, v14.2d
add x16, x16, x4
add x20, x20, x5
sub v24.2d, v24.2d, v19.2d
lsr x2, x10, #51
sub v25.2d, v25.2d, v15.2d
lsr x3, x12, #51
lsr x4, x14, #51
sub v25.2d, v25.2d, v20.2d
lsr x5, x16, #51
sub v26.2d, v26.2d, v16.2d
lsr x6, x20, #51
and x10, x10, x1
sub v26.2d, v26.2d, v21.2d
and x12, x12, x1
and x14, x14, x1
sub v27.2d, v27.2d, v17.2d
and x16, x16, x1
sub v27.2d, v27.2d, v22.2d
and x20, x20, x1
mul x6, x6, x7
sub v28.2d, v28.2d, v18.2d
add x10, x10, x6
sub v28.2d, v28.2d, v23.2d
add x12, x12, x2
add x14, x14, x3
add v15.2d, v15.2d, v19.2d
add x16, x16, x4
add x20, x20, x5
add v15.2d, v15.2d, v19.2d
stp x10, x12, [x0, #16]
add v16.2d, v16.2d, v20.2d
stp x14, x16, [x0, #32]
str x20, [x0, #48]
add v16.2d, v16.2d, v20.2d
ldp x1, x2, [x0, #208]
ldp x3, x4, [x0, #224]
add v17.2d, v17.2d, v21.2d
ldr x5, [x0, #240]
add v17.2d, v17.2d, v21.2d
mov w22, #19
mul x6, x2, x22
add v18.2d, v18.2d, v22.2d
mul x7, x3, x22
add v18.2d, v18.2d, v22.2d
mul x8, x4, x22
mul x9, x5, x22
shl v0.2d, v23.2d, #1
ldr x22, [x0, #256]
mul x10, x22, x1
shl v1.2d, v23.2d, #2
umulh x11, x22, x1
shl v2.2d, v23.2d, #5
mul x12, x22, x2
umulh x13, x22, x2
add v14.2d, v14.2d, v0.2d
mul x14, x22, x3
add v1.2d, v1.2d, v2.2d
umulh x15, x22, x3
mul x16, x22, x4
add v14.2d, v14.2d, v1.2d
umulh x17, x22, x4
mul x20, x22, x5
ldr q3, [x0, #720]
umulh x21, x22, x5
ldr q4, [x0, #736]
ldr x22, [x0, #264]
mul x23, x22, x1
ushr v2.2d, v28.2d, #25
umulh x24, x22, x1
and v28.16b, v28.16b, v4.16b
adds x12, x12, x23
adc x13, x13, x24
ushr v0.2d, v18.2d, #26
mul x23, x22, x2
umulh x24, x22, x2
and v18.16b, v18.16b, v3.16b
adds x14, x14, x23
add v28.2d, v28.2d, v0.2d
adc x15, x15, x24
mul x23, x22, x3
ushr v1.2d, v27.2d, #25
umulh x24, x22, x3
adds x16, x16, x23
and v27.16b, v27.16b, v4.16b
adc x17, x17, x24
add v18.2d, v18.2d, v1.2d
mul x23, x22, x4
umulh x24, x22, x4
ushr v0.2d, v17.2d, #26
adds x20, x20, x23
and v17.16b, v17.16b, v3.16b
adc x21, x21, x24
mul x23, x22, x9
add v27.2d, v27.2d, v0.2d
umulh x24, x22, x9
adds x10, x10, x23
ushr v1.2d, v26.2d, #25
adc x11, x11, x24
and v26.16b, v26.16b, v4.16b
ldr x22, [x0, #272]
mul x23, x22, x1
add v17.2d, v17.2d, v1.2d
umulh x24, x22, x1
ushr v0.2d, v16.2d, #26
adds x14, x14, x23
adc x15, x15, x24
and v16.16b, v16.16b, v3.16b
mul x23, x22, x2
umulh x24, x22, x2
add v26.2d, v26.2d, v0.2d
adds x16, x16, x23
ushr v1.2d, v25.2d, #25
adc x17, x17, x24
mul x23, x22, x3
and v25.16b, v25.16b, v4.16b
umulh x24, x22, x3
adds x20, x20, x23
add v16.2d, v16.2d, v1.2d
adc x21, x21, x24
ushr v0.2d, v15.2d, #26
mul x23, x22, x8
umulh x24, x22, x8
and v15.16b, v15.16b, v3.16b
adds x10, x10, x23
add v25.2d, v25.2d, v0.2d
adc x11, x11, x24
mul x23, x22, x9
ushr v1.2d, v24.2d, #25
umulh x24, x22, x9
adds x12, x12, x23
and v24.16b, v24.16b, v4.16b
adc x13, x13, x24
add v15.2d, v15.2d, v1.2d
ldr x22, [x0, #280]
mul x23, x22, x1
ushr v0.2d, v14.2d, #26
umulh x24, x22, x1
and v14.16b, v14.16b, v3.16b
adds x16, x16, x23
adc x17, x17, x24
add v24.2d, v24.2d, v0.2d
mul x23, x22, x2
umulh x24, x22, x2
add v14.2d, v14.2d, v2.2d
adds x20, x20, x23
shl v0.2d, v2.2d, #1
adc x21, x21, x24
mul x23, x22, x7
shl v2.2d, v2.2d, #4
umulh x24, x22, x7
adds x10, x10, x23
add v14.2d, v14.2d, v0.2d
adc x11, x11, x24
add v14.2d, v14.2d, v2.2d
mul x23, x22, x8
umulh x24, x22, x8
shl v24.2d, v24.2d, #26
adds x12, x12, x23
add v14.2d, v14.2d, v24.2d
adc x13, x13, x24
mul x23, x22, x9
shl v25.2d, v25.2d, #26
umulh x24, x22, x9
adds x14, x14, x23
add v15.2d, v15.2d, v25.2d
adc x15, x15, x24
shl v26.2d, v26.2d, #26
ldr x22, [x0, #288]
mul x23, x22, x1
add v16.2d, v16.2d, v26.2d
umulh x24, x22, x1
shl v27.2d, v27.2d, #26
adds x20, x20, x23
adc x21, x21, x24
add v17.2d, v17.2d, v27.2d
mul x23, x22, x6
umulh x24, x22, x6
shl v28.2d, v28.2d, #26
adds x10, x10, x23
add v18.2d, v18.2d, v28.2d
adc x11, x11, x24
mul x23, x22, x7
ldr q5, [x0, #704]
umulh x24, x22, x7
ushr v24.2d, v14.2d, #51
adds x12, x12, x23
adc x13, x13, x24
and v14.16b, v14.16b, v5.16b
mul x23, x22, x8
umulh x24, x22, x8
ushr v25.2d, v15.2d, #51
adds x14, x14, x23
and v15.16b, v15.16b, v5.16b
adc x15, x15, x24
mul x23, x22, x9
ushr v26.2d, v16.2d, #51
umulh x24, x22, x9
adds x16, x16, x23
and v16.16b, v16.16b, v5.16b
adc x17, x17, x24
ushr v27.2d, v17.2d, #51
mov x1, #0xffff
movk x1, #0xffff, lsl #16
and v17.16b, v17.16b, v5.16b
movk x1, #0xffff, lsl #32
ushr v28.2d, v18.2d, #51
movk x1, #7, lsl #48
mov w7, #19
and v18.16b, v18.16b, v5.16b
extr x2, x11, x10, #51
extr x3, x13, x12, #51
add v15.2d, v15.2d, v24.2d
extr x4, x15, x14, #51
add v16.2d, v16.2d, v25.2d
extr x5, x17, x16, #51
extr x6, x21, x20, #51
add v17.2d, v17.2d, v26.2d
and x10, x10, x1
add v18.2d, v18.2d, v27.2d
and x12, x12, x1
and x14, x14, x1
add v14.2d, v14.2d, v28.2d
and x16, x16, x1
and x20, x20, x1
shl v0.2d, v28.2d, #1
mul x6, x6, x7
shl v2.2d, v28.2d, #4
add x10, x10, x6
add x12, x12, x2
add v14.2d, v14.2d, v0.2d
add x14, x14, x3
add x16, x16, x4
add v14.2d, v14.2d, v2.2d
add x20, x20, x5
trn1 v0.2d, v14.2d, v15.2d
lsr x2, x10, #51
lsr x3, x12, #51
trn2 v1.2d, v14.2d, v15.2d
lsr x4, x14, #51
str q0, [x0, #112]
lsr x5, x16, #51
lsr x6, x20, #51
str q1, [x0, #160]
and x10, x10, x1
and x12, x12, x1
trn1 v0.2d, v16.2d, v17.2d
and x14, x14, x1
trn2 v1.2d, v16.2d, v17.2d
and x16, x16, x1
and x20, x20, x1
str q0, [x0, #128]
mul x6, x6, x7
str q1, [x0, #176]
add x10, x10, x6
add x12, x12, x2
trn1 v0.2d, v18.2d, v18.2d
add x14, x14, x3
add x16, x16, x4
trn2 v1.2d, v18.2d, v18.2d
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
");
unsafe extern "C" {
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_sn1(p: *mut u64, n: u64);fn lab_sq2k(p: *mut u64, n: u64);fn lab_mu2k(p: *mut u64, n: u64);fn lab_sn2(p: *mut u64, n: u64);fn lab_sn3(p: *mut u64, n: u64);fn lab_sn4(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn1"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn1(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sq2k"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sq2k(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_mu2k"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_mu2k(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn3"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn3(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_sn4"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_sn4(p, 100) })); g.finish();
}