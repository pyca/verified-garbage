//! Lab.
use criterion::{BenchmarkId, Criterion};
use crate::{BenchDyn, VG};
pub const USES: &[&str] = &["x25519"];
core::arch::global_asm!(r".p2align 6
.globl lab_ue
lab_ue:
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
mul x2, x3, x12
trn2 v27.2d, v22.2d, v23.2d
mul x8, x3, x13
and v20.16b, v24.16b, v31.16b
mul x9, x3, x14
mul x16, x3, x15
ushr v21.2d, v24.2d, #26
adds x5, x5, x2
adcs x6, x6, x8
and v21.16b, v21.16b, v30.16b
adcs x7, x7, x9
adcs x21, x21, x16
uzp1 v0.4s, v20.4s, v21.4s
adc x22, x10, x10
umulh x2, x3, x12
shl v20.2d, v25.2d, #13
umulh x8, x3, x13
sri v20.2d, v24.2d, #51
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
adcs x7, x7, x8
ushr v21.2d, v25.2d, #13
adcs x21, x21, x9
adc x22, x22, x16
and v21.16b, v21.16b, v30.16b
ldr x3, [x0, #336]
uzp1 v1.4s, v20.4s, v21.4s
mul x2, x3, x12
mul x8, x3, x13
ushr v20.2d, v25.2d, #38
mul x9, x3, x14
mul x16, x3, x15
and v21.16b, v26.16b, v30.16b
adds x6, x6, x2
adcs x7, x7, x8
uzp1 v2.4s, v20.4s, v21.4s
adcs x21, x21, x9
adcs x22, x22, x16
ushr v20.2d, v26.2d, #25
adc x23, x10, x10
and v20.16b, v20.16b, v31.16b
umulh x2, x3, x12
umulh x8, x3, x13
shl v21.2d, v27.2d, #13
umulh x9, x3, x14
umulh x16, x3, x15
sri v21.2d, v26.2d, #51
adds x7, x7, x2
adcs x21, x21, x8
and v21.16b, v21.16b, v30.16b
adcs x22, x22, x9
adc x23, x23, x16
uzp1 v3.4s, v20.4s, v21.4s
ldr x3, [x0, #344]
ushr v20.2d, v27.2d, #12
mul x2, x3, x12
mul x8, x3, x13
and v20.16b, v20.16b, v31.16b
mul x9, x3, x14
mul x16, x3, x15
ushr v21.2d, v27.2d, #38
adds x7, x7, x2
adcs x21, x21, x8
uzp1 v4.4s, v20.4s, v21.4s
adcs x22, x22, x9
ext v5.16b, v0.16b, v0.16b, #8
adcs x23, x23, x16
adc x24, x10, x10
ext v6.16b, v1.16b, v1.16b, #8
umulh x2, x3, x12
umulh x8, x3, x13
ext v7.16b, v2.16b, v2.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v8.16b, v3.16b, v3.16b, #8
adds x21, x21, x2
adcs x22, x22, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x23, x23, x9
add v10.4s, v0.4s, v0.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v11.4s, v1.4s, v1.4s
mul x2, x11, x21
adds x4, x4, x2
add v12.4s, v2.4s, v2.4s
mul x8, x11, x22
adcs x5, x5, x8
add v13.4s, v3.4s, v3.4s
mul x9, x11, x23
adcs x6, x6, x9
add v14.4s, v4.4s, v4.4s
mul x16, x11, x24
ldr q31, [x0, #752]
adcs x7, x7, x16
adc x20, x10, x10
mul v15.4s, v0.4s, v31.4s
umulh x2, x11, x21
umulh x8, x11, x22
mul v16.4s, v1.4s, v31.4s
umulh x9, x11, x23
umulh x16, x11, x24
mul v17.4s, v2.4s, v31.4s
adds x7, x7, x9
mul v18.4s, v3.4s, v31.4s
adc x20, x20, x16
adds x16, x7, x7
mul v19.4s, v4.4s, v31.4s
adc x9, x20, x20
lsr x7, x16, #1
umull2 v20.2d, v10.4s, v19.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal2 v20.2d, v11.4s, v18.4s
adds x4, x4, x9
adcs x5, x5, x2
umlal2 v20.2d, v2.4s, v17.4s
adcs x6, x6, x8
add v20.2d, v20.2d, v20.2d
adc x7, x7, x10
stp x4, x5, [x0, #448]
umlal v20.2d, v0.2s, v0.2s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal v20.2d, v11.2s, v19.2s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umlal v20.2d, v12.2s, v18.2s
mul x4, x3, x12
mul x5, x3, x13
add v30.4s, v5.4s, v5.4s
mul x6, x3, x14
umull v25.2d, v30.2s, v0.2s
mul x7, x3, x15
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v25.2d, v30.2s, v19.2s
umulh x16, x3, x15
adds x5, x5, x2
umlal2 v25.2d, v30.4s, v19.4s
adcs x6, x6, x8
adcs x7, x7, x9
add v30.4s, v7.4s, v7.4s
adc x21, x16, x10
umlal v25.2d, v30.2s, v18.2s
ldr x3, [x0, #296]
mul x2, x3, x12
umlal2 v25.2d, v30.4s, v18.4s
mul x8, x3, x13
mul x9, x3, x14
umull2 v21.2d, v0.4s, v0.4s
mul x16, x3, x15
adds x5, x5, x2
umlal2 v21.2d, v11.4s, v19.4s
adcs x6, x6, x8
umlal2 v21.2d, v12.4s, v18.4s
adcs x7, x7, x9
adcs x21, x21, x16
add v21.2d, v21.2d, v21.2d
adc x22, x10, x10
umulh x2, x3, x12
umlal v21.2d, v10.2s, v1.2s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v21.2d, v12.2s, v19.2s
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v3.2s, v18.2s
adcs x7, x7, x8
add v30.4s, v5.4s, v5.4s
adcs x21, x21, x9
adc x22, x22, x16
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #304]
mul x2, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x8, x3, x13
mul x9, x3, x14
add v30.4s, v7.4s, v7.4s
mul x16, x3, x15
adds x6, x6, x2
umlal v26.2d, v30.2s, v19.2s
adcs x7, x7, x8
umlal2 v26.2d, v30.4s, v19.4s
adcs x21, x21, x9
adcs x22, x22, x16
add v30.4s, v8.4s, v8.4s
adc x23, x10, x10
umulh x2, x3, x12
umlal v26.2d, v30.2s, v18.2s
umulh x8, x3, x13
umulh x9, x3, x14
umull2 v22.2d, v10.4s, v1.4s
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
umlal v22.2d, v13.2s, v19.2s
adds x7, x7, x2
adcs x21, x21, x8
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x9
adcs x23, x23, x16
umull v27.2d, v30.2s, v2.2s
adc x24, x10, x10
umulh x2, x3, x12
umlal2 v27.2d, v30.4s, v2.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v27.2d, v30.2s, v1.2s
adds x21, x21, x2
adcs x22, x22, x8
add v30.4s, v8.4s, v8.4s
adcs x23, x23, x9
adc x24, x24, x16
umlal v27.2d, v30.2s, v19.2s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v27.2d, v30.4s, v19.4s
adds x4, x4, x2
umull2 v23.2d, v10.4s, v2.4s
mul x8, x11, x22
adcs x5, x5, x8
umlal2 v23.2d, v1.4s, v1.4s
mul x9, x11, x23
adcs x6, x6, x9
umlal2 v23.2d, v13.4s, v19.4s
mul x16, x11, x24
adcs x7, x7, x16
add v23.2d, v23.2d, v23.2d
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v10.2s, v3.2s
umulh x8, x11, x22
umlal v23.2d, v11.2s, v2.2s
umulh x9, x11, x23
umulh x16, x11, x24
umlal v23.2d, v4.2s, v19.2s
adds x7, x7, x9
adc x20, x20, x16
add v30.4s, v5.4s, v5.4s
adds x16, x7, x7
adc x9, x20, x20
umull v28.2d, v30.2s, v3.2s
lsr x7, x16, #1
movz w11, #19, lsl #0
umlal2 v28.2d, v30.4s, v3.4s
mul x9, x9, x11
add v30.4s, v6.4s, v6.4s
adds x4, x4, x9
adcs x5, x5, x2
umlal v28.2d, v30.2s, v2.2s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v28.2d, v30.4s, v2.4s
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
add v30.4s, v9.4s, v9.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
umlal v28.2d, v30.2s, v19.2s
ldp x21, x22, [x0, #480]
umull2 v24.2d, v10.4s, v3.4s
ldp x23, x24, [x0, #496]
subs x12, x4, x21
umlal2 v24.2d, v11.4s, v2.4s
sbcs x13, x5, x22
movz w2, #38, lsl #0
umlal2 v24.2d, v4.4s, v19.4s
sbcs x14, x6, x23
sbcs x15, x7, x24
add v24.2d, v24.2d, v24.2d
csel x3, x10, x2, hs
umlal v24.2d, v10.2s, v4.2s
subs x12, x12, x3
sbcs x13, x13, x10
umlal v24.2d, v11.2s, v3.2s
sbcs x14, x14, x10
sbc x15, x15, x10
umlal v24.2d, v2.2s, v2.2s
mul x5, x12, x13
mul x6, x12, x14
add v30.4s, v5.4s, v5.4s
mul x7, x12, x15
umulh x2, x12, x13
umull v29.2d, v30.2s, v4.2s
umulh x8, x12, x14
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x12, x15
adds x6, x6, x2
add v30.4s, v6.4s, v6.4s
adcs x7, x7, x8
adc x21, x9, x10
umlal v29.2d, v30.2s, v3.2s
mul x2, x13, x14
mul x8, x13, x15
umlal2 v29.2d, v30.4s, v3.4s
umulh x9, x13, x14
umulh x16, x13, x15
add v30.4s, v7.4s, v7.4s
adds x7, x7, x2
umlal v29.2d, v30.2s, v2.2s
adcs x21, x21, x8
adc x22, x16, x10
ldr q3, [x0, #720]
adds x21, x21, x9
adc x22, x22, x10
ldr q4, [x0, #736]
mul x2, x14, x15
umulh x8, x14, x15
ushr v2.2d, v29.2d, #25
adds x22, x22, x2
and v29.16b, v29.16b, v4.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v0.2d, v24.2d, #26
adcs x6, x6, x6
adcs x7, x7, x7
and v24.16b, v24.16b, v3.16b
adcs x21, x21, x21
adcs x22, x22, x22
add v29.2d, v29.2d, v0.2d
adcs x23, x23, x23
adc x24, x10, x10
ushr v1.2d, v28.2d, #25
mul x4, x12, x12
and v28.16b, v28.16b, v4.16b
umulh x2, x12, x12
mul x8, x13, x13
add v24.2d, v24.2d, v1.2d
umulh x9, x13, x13
mul x16, x14, x14
ushr v0.2d, v23.2d, #26
umulh x17, x14, x14
mul x3, x15, x15
and v23.16b, v23.16b, v3.16b
umulh x11, x15, x15
adds x5, x5, x2
add v28.2d, v28.2d, v0.2d
adcs x6, x6, x8
ushr v1.2d, v27.2d, #25
adcs x7, x7, x9
adcs x21, x21, x16
and v27.16b, v27.16b, v4.16b
adcs x22, x22, x17
adcs x23, x23, x3
add v23.2d, v23.2d, v1.2d
adc x24, x24, x11
movz w11, #38, lsl #0
ushr v0.2d, v22.2d, #26
mul x2, x11, x21
and v22.16b, v22.16b, v3.16b
adds x4, x4, x2
mul x8, x11, x22
add v27.2d, v27.2d, v0.2d
adcs x5, x5, x8
mul x9, x11, x23
ushr v1.2d, v26.2d, #25
adcs x6, x6, x9
mul x16, x11, x24
and v26.16b, v26.16b, v4.16b
adcs x7, x7, x16
adc x20, x10, x10
add v22.2d, v22.2d, v1.2d
umulh x2, x11, x21
ushr v0.2d, v21.2d, #26
umulh x8, x11, x22
umulh x9, x11, x23
and v21.16b, v21.16b, v3.16b
umulh x16, x11, x24
adds x7, x7, x9
add v26.2d, v26.2d, v0.2d
adc x20, x20, x16
adds x16, x7, x7
ushr v1.2d, v25.2d, #25
adc x9, x20, x20
lsr x7, x16, #1
and v25.16b, v25.16b, v4.16b
movz w11, #19, lsl #0
add v21.2d, v21.2d, v1.2d
mul x9, x9, x11
adds x4, x4, x9
ushr v0.2d, v20.2d, #26
adcs x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v3.16b
adc x7, x7, x10
stp x4, x5, [x0, #192]
add v25.2d, v25.2d, v0.2d
stp x6, x7, [x0, #208]
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
shl v0.2d, v2.2d, #1
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
shl v2.2d, v2.2d, #4
adds x12, x4, x21
adcs x13, x5, x22
add v20.2d, v20.2d, v0.2d
movz w2, #38, lsl #0
adcs x14, x6, x23
add v20.2d, v20.2d, v2.2d
adcs x15, x7, x24
shl v25.2d, v25.2d, #26
csel x3, x2, x10, hs
adds x12, x12, x3
add v20.2d, v20.2d, v25.2d
adcs x13, x13, x10
adc x14, x14, x10
shl v26.2d, v26.2d, #26
mul x5, x12, x13
mul x6, x12, x14
add v21.2d, v21.2d, v26.2d
mul x7, x12, x15
umulh x2, x12, x13
shl v27.2d, v27.2d, #26
umulh x8, x12, x14
add v22.2d, v22.2d, v27.2d
umulh x9, x12, x15
adds x6, x6, x2
shl v28.2d, v28.2d, #26
adcs x7, x7, x8
adc x21, x9, x10
add v23.2d, v23.2d, v28.2d
mul x2, x13, x14
mul x8, x13, x15
shl v29.2d, v29.2d, #26
umulh x9, x13, x14
umulh x16, x13, x15
add v24.2d, v24.2d, v29.2d
adds x7, x7, x2
ldr q5, [x0, #704]
adcs x21, x21, x8
adc x22, x16, x10
ushr v25.2d, v20.2d, #51
adds x21, x21, x9
adc x22, x22, x10
and v20.16b, v20.16b, v5.16b
mul x2, x14, x15
umulh x8, x14, x15
ushr v26.2d, v21.2d, #51
adds x22, x22, x2
and v21.16b, v21.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v27.2d, v22.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v22.16b, v22.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v28.2d, v23.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v23.16b, v23.16b, v5.16b
mul x4, x12, x12
ushr v29.2d, v24.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v24.16b, v24.16b, v5.16b
umulh x9, x13, x13
mul x16, x14, x14
add v21.2d, v21.2d, v25.2d
umulh x17, x14, x14
mul x3, x15, x15
add v22.2d, v22.2d, v26.2d
umulh x11, x15, x15
adds x5, x5, x2
add v23.2d, v23.2d, v27.2d
adcs x6, x6, x8
add v24.2d, v24.2d, v28.2d
adcs x7, x7, x9
adcs x21, x21, x16
add v20.2d, v20.2d, v29.2d
adcs x22, x22, x17
adcs x23, x23, x3
shl v0.2d, v29.2d, #1
adc x24, x24, x11
movz w11, #38, lsl #0
shl v2.2d, v29.2d, #4
mul x2, x11, x21
add v20.2d, v20.2d, v0.2d
adds x4, x4, x2
mul x8, x11, x22
add v20.2d, v20.2d, v2.2d
adcs x5, x5, x8
mul x9, x11, x23
trn1 v0.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
trn2 v1.2d, v20.2d, v21.2d
adcs x7, x7, x16
adc x20, x10, x10
str q0, [x0, #1024]
umulh x2, x11, x21
str q1, [x0, #1072]
umulh x8, x11, x22
umulh x9, x11, x23
trn1 v0.2d, v22.2d, v23.2d
umulh x16, x11, x24
adds x7, x7, x9
trn2 v1.2d, v22.2d, v23.2d
adc x20, x20, x16
adds x16, x7, x7
str q0, [x0, #1040]
adc x9, x20, x20
lsr x7, x16, #1
str q1, [x0, #1088]
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
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
.globl lab_xe
lab_xe:
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
umulh x9, x3, x14
ldr q23, [x0, #272]
umulh x16, x3, x15
adds x5, x5, x2
trn1 v24.2d, v20.2d, v21.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v25.2d, v20.2d, v21.2d
adc x21, x16, x10
ldr x3, [x0, #328]
trn1 v26.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v24.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v24.2d, #26
adcs x7, x7, x9
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
umulh x16, x3, x15
sri v20.2d, v24.2d, #51
adds x6, x6, x2
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
adc x22, x22, x16
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v2.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v26.2d, #25
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x7, x7, x2
adcs x21, x21, x8
shl v21.2d, v27.2d, #13
adcs x22, x22, x9
adc x23, x23, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #344]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x7, x7, x2
adcs x21, x21, x8
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x9
adcs x23, x23, x16
ushr v21.2d, v27.2d, #38
adc x24, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v10.4s, v0.4s, v0.4s
umulh x16, x3, x15
adds x21, x21, x2
add v11.4s, v1.4s, v1.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v12.4s, v2.4s, v2.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v13.4s, v3.4s, v3.4s
mul x2, x11, x21
adds x4, x4, x2
add v14.4s, v4.4s, v4.4s
mul x8, x11, x22
adcs x5, x5, x8
ext v5.16b, v10.16b, v10.16b, #8
mul x9, x11, x23
adcs x6, x6, x9
ext v6.16b, v11.16b, v11.16b, #8
mul x16, x11, x24
adcs x7, x7, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x20, x10, x10
umulh x2, x11, x21
ext v8.16b, v13.16b, v13.16b, #8
umulh x8, x11, x22
umulh x9, x11, x23
ext v9.16b, v14.16b, v14.16b, #8
umulh x16, x11, x24
adds x7, x7, x9
ldr q31, [x0, #752]
adc x20, x20, x16
mul v15.4s, v0.4s, v31.4s
adds x16, x7, x7
adc x9, x20, x20
mul v16.4s, v1.4s, v31.4s
lsr x7, x16, #1
movz w11, #19, lsl #0
mul v17.4s, v2.4s, v31.4s
mul x9, x9, x11
adds x4, x4, x9
mul v18.4s, v3.4s, v31.4s
adcs x5, x5, x2
adcs x6, x6, x8
mul v19.4s, v4.4s, v31.4s
adc x7, x7, x10
stp x4, x5, [x0, #448]
umull2 v20.2d, v10.4s, v19.4s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal2 v20.2d, v11.4s, v18.4s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umlal2 v20.2d, v2.4s, v17.4s
mul x4, x3, x12
mul x5, x3, x13
add v20.2d, v20.2d, v20.2d
mul x6, x3, x14
mul x7, x3, x15
umlal v20.2d, v0.2s, v0.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v20.2d, v12.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull v25.2d, v5.2s, v0.2s
adcs x7, x7, x9
adc x21, x16, x10
umlal v25.2d, v6.2s, v19.2s
ldr x3, [x0, #296]
umlal2 v25.2d, v6.4s, v19.4s
mul x2, x3, x12
mul x8, x3, x13
umlal v25.2d, v7.2s, v18.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v25.2d, v7.4s, v18.4s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v21.2d, v0.4s, v0.4s
adcs x7, x7, x9
adcs x21, x21, x16
umlal2 v21.2d, v11.4s, v19.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v10.2s, v1.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v21.2d, v12.2s, v19.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal v21.2d, v3.2s, v18.2s
mul x2, x3, x12
mul x8, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
adds x6, x6, x2
adcs x7, x7, x8
umlal v26.2d, v7.2s, v19.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v26.2d, v7.4s, v19.4s
adc x23, x10, x10
umlal v26.2d, v8.2s, v18.2s
umulh x2, x3, x12
umulh x8, x3, x13
umull2 v22.2d, v10.4s, v1.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v22.2d, v13.2s, v19.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v27.2d, v5.2s, v2.2s
adcs x23, x23, x16
adc x24, x10, x10
umlal2 v27.2d, v5.4s, v2.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v27.2d, v6.2s, v1.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v8.2s, v19.2s
adds x21, x21, x2
adcs x22, x22, x8
umlal2 v27.2d, v8.4s, v19.4s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v23.2d, v10.4s, v2.4s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v23.2d, v1.4s, v1.4s
adds x4, x4, x2
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x11, x22
adcs x5, x5, x8
add v23.2d, v23.2d, v23.2d
mul x9, x11, x23
adcs x6, x6, x9
umlal v23.2d, v10.2s, v3.2s
mul x16, x11, x24
adcs x7, x7, x16
umlal v23.2d, v11.2s, v2.2s
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v4.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umull v28.2d, v5.2s, v3.2s
umulh x16, x11, x24
adds x7, x7, x9
umlal2 v28.2d, v5.4s, v3.4s
adc x20, x20, x16
adds x16, x7, x7
umlal v28.2d, v6.2s, v2.2s
adc x9, x20, x20
lsr x7, x16, #1
umlal2 v28.2d, v6.4s, v2.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal v28.2d, v9.2s, v19.2s
adds x4, x4, x9
adcs x5, x5, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v24.2d, v11.4s, v2.4s
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
umlal2 v24.2d, v4.4s, v19.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
add v24.2d, v24.2d, v24.2d
ldp x21, x22, [x0, #480]
umlal v24.2d, v10.2s, v4.2s
ldp x23, x24, [x0, #496]
subs x12, x4, x21
umlal v24.2d, v11.2s, v3.2s
sbcs x13, x5, x22
movz w2, #38, lsl #0
umlal v24.2d, v2.2s, v2.2s
sbcs x14, x6, x23
sbcs x15, x7, x24
umull v29.2d, v5.2s, v4.2s
csel x3, x10, x2, hs
subs x12, x12, x3
umlal2 v29.2d, v5.4s, v4.4s
sbcs x13, x13, x10
sbcs x14, x14, x10
umlal v29.2d, v6.2s, v3.2s
sbc x15, x15, x10
mul x5, x12, x13
umlal2 v29.2d, v6.4s, v3.4s
mul x6, x12, x14
mul x7, x12, x15
umlal v29.2d, v7.2s, v2.2s
umulh x2, x12, x13
umulh x8, x12, x14
ldr q3, [x0, #720]
umulh x9, x12, x15
adds x6, x6, x2
ldr q4, [x0, #736]
adcs x7, x7, x8
adc x21, x9, x10
ushr v2.2d, v29.2d, #25
mul x2, x13, x14
mul x8, x13, x15
and v29.16b, v29.16b, v4.16b
umulh x9, x13, x14
umulh x16, x13, x15
ushr v0.2d, v24.2d, #26
adds x7, x7, x2
adcs x21, x21, x8
and v24.16b, v24.16b, v3.16b
adc x22, x16, x10
adds x21, x21, x9
add v29.2d, v29.2d, v0.2d
adc x22, x22, x10
ushr v1.2d, v28.2d, #25
mul x2, x14, x15
umulh x8, x14, x15
and v28.16b, v28.16b, v4.16b
adds x22, x22, x2
adc x23, x8, x10
add v24.2d, v24.2d, v1.2d
adds x5, x5, x5
adcs x6, x6, x6
ushr v0.2d, v23.2d, #26
adcs x7, x7, x7
adcs x21, x21, x21
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x22
adcs x23, x23, x23
add v28.2d, v28.2d, v0.2d
adc x24, x10, x10
mul x4, x12, x12
ushr v1.2d, v27.2d, #25
umulh x2, x12, x12
mul x8, x13, x13
and v27.16b, v27.16b, v4.16b
umulh x9, x13, x13
mul x16, x14, x14
add v23.2d, v23.2d, v1.2d
umulh x17, x14, x14
mul x3, x15, x15
ushr v0.2d, v22.2d, #26
umulh x11, x15, x15
adds x5, x5, x2
and v22.16b, v22.16b, v3.16b
adcs x6, x6, x8
adcs x7, x7, x9
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x16
adcs x22, x22, x17
ushr v1.2d, v26.2d, #25
adcs x23, x23, x3
adc x24, x24, x11
and v26.16b, v26.16b, v4.16b
movz w11, #38, lsl #0
add v22.2d, v22.2d, v1.2d
mul x2, x11, x21
adds x4, x4, x2
ushr v0.2d, v21.2d, #26
mul x8, x11, x22
adcs x5, x5, x8
and v21.16b, v21.16b, v3.16b
mul x9, x11, x23
adcs x6, x6, x9
add v26.2d, v26.2d, v0.2d
mul x16, x11, x24
adcs x7, x7, x16
ushr v1.2d, v25.2d, #25
adc x20, x10, x10
umulh x2, x11, x21
and v25.16b, v25.16b, v4.16b
umulh x8, x11, x22
umulh x9, x11, x23
add v21.2d, v21.2d, v1.2d
umulh x16, x11, x24
adds x7, x7, x9
ushr v0.2d, v20.2d, #26
adc x20, x20, x16
adds x16, x7, x7
and v20.16b, v20.16b, v3.16b
adc x9, x20, x20
lsr x7, x16, #1
add v25.2d, v25.2d, v0.2d
movz w11, #19, lsl #0
mul x9, x9, x11
add v20.2d, v20.2d, v2.2d
adds x4, x4, x9
adcs x5, x5, x2
shl v0.2d, v2.2d, #1
adcs x6, x6, x8
adc x7, x7, x10
shl v2.2d, v2.2d, #4
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
shl v25.2d, v25.2d, #26
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v20.2d, v20.2d, v25.2d
adcs x13, x5, x22
movz w2, #38, lsl #0
shl v26.2d, v26.2d, #26
adcs x14, x6, x23
adcs x15, x7, x24
add v21.2d, v21.2d, v26.2d
csel x3, x2, x10, hs
adds x12, x12, x3
shl v27.2d, v27.2d, #26
adcs x13, x13, x10
adc x14, x14, x10
add v22.2d, v22.2d, v27.2d
mul x5, x12, x13
mul x6, x12, x14
shl v28.2d, v28.2d, #26
mul x7, x12, x15
umulh x2, x12, x13
add v23.2d, v23.2d, v28.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v29.2d, v29.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v24.2d, v24.2d, v29.2d
adc x21, x9, x10
mul x2, x13, x14
ldr q5, [x0, #704]
mul x8, x13, x15
umulh x9, x13, x14
ushr v25.2d, v20.2d, #51
umulh x16, x13, x15
adds x7, x7, x2
and v20.16b, v20.16b, v5.16b
adcs x21, x21, x8
adc x22, x16, x10
ushr v26.2d, v21.2d, #51
adds x21, x21, x9
and v21.16b, v21.16b, v5.16b
adc x22, x22, x10
mul x2, x14, x15
ushr v27.2d, v22.2d, #51
umulh x8, x14, x15
adds x22, x22, x2
and v22.16b, v22.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v28.2d, v23.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v23.16b, v23.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v29.2d, v24.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v24.16b, v24.16b, v5.16b
mul x4, x12, x12
umulh x2, x12, x12
add v21.2d, v21.2d, v25.2d
mul x8, x13, x13
umulh x9, x13, x13
add v22.2d, v22.2d, v26.2d
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v27.2d
mul x3, x15, x15
umulh x11, x15, x15
add v24.2d, v24.2d, v28.2d
adds x5, x5, x2
adcs x6, x6, x8
add v20.2d, v20.2d, v29.2d
adcs x7, x7, x9
adcs x21, x21, x16
shl v0.2d, v29.2d, #1
adcs x22, x22, x17
adcs x23, x23, x3
shl v2.2d, v29.2d, #4
adc x24, x24, x11
add v20.2d, v20.2d, v0.2d
movz w11, #38, lsl #0
mul x2, x11, x21
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
mul x8, x11, x22
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
mul x9, x11, x23
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
str q0, [x0, #1024]
adcs x7, x7, x16
adc x20, x10, x10
str q1, [x0, #1072]
umulh x2, x11, x21
umulh x8, x11, x22
trn1 v0.2d, v22.2d, v23.2d
umulh x9, x11, x23
umulh x16, x11, x24
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x9
adc x20, x20, x16
str q0, [x0, #1040]
adds x16, x7, x7
adc x9, x20, x20
str q1, [x0, #1088]
lsr x7, x16, #1
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
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
.globl lab_xE
lab_xE:
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
umulh x9, x3, x14
ldr q23, [x0, #272]
umulh x16, x3, x15
adds x5, x5, x2
trn1 v24.2d, v20.2d, v21.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v25.2d, v20.2d, v21.2d
adc x21, x16, x10
ldr x3, [x0, #328]
trn1 v26.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v24.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v24.2d, #26
adcs x7, x7, x9
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
umulh x16, x3, x15
sri v20.2d, v24.2d, #51
adds x6, x6, x2
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
adc x22, x22, x16
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v2.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v26.2d, #25
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x7, x7, x2
adcs x21, x21, x8
shl v21.2d, v27.2d, #13
adcs x22, x22, x9
adc x23, x23, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #344]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x7, x7, x2
adcs x21, x21, x8
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x9
adcs x23, x23, x16
ushr v21.2d, v27.2d, #38
adc x24, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v10.4s, v0.4s, v0.4s
umulh x16, x3, x15
adds x21, x21, x2
add v11.4s, v1.4s, v1.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v12.4s, v2.4s, v2.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v13.4s, v3.4s, v3.4s
mul x2, x11, x21
adds x4, x4, x2
add v14.4s, v4.4s, v4.4s
mul x8, x11, x22
adcs x5, x5, x8
ext v5.16b, v10.16b, v10.16b, #8
mul x9, x11, x23
adcs x6, x6, x9
ext v6.16b, v11.16b, v11.16b, #8
mul x16, x11, x24
adcs x7, x7, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x20, x10, x10
umulh x2, x11, x21
ext v8.16b, v13.16b, v13.16b, #8
umulh x8, x11, x22
umulh x9, x11, x23
ext v9.16b, v14.16b, v14.16b, #8
umulh x16, x11, x24
adds x7, x7, x9
ldr q31, [x0, #752]
adc x20, x20, x16
mul v15.4s, v0.4s, v31.4s
adds x16, x7, x7
adc x9, x20, x20
mul v16.4s, v1.4s, v31.4s
lsr x7, x16, #1
movz w11, #19, lsl #0
mul v17.4s, v2.4s, v31.4s
mul x9, x9, x11
adds x4, x4, x9
mul v18.4s, v3.4s, v31.4s
adcs x5, x5, x2
adcs x6, x6, x8
mul v19.4s, v4.4s, v31.4s
adc x7, x7, x10
stp x4, x5, [x0, #448]
umull2 v20.2d, v10.4s, v19.4s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal2 v20.2d, v11.4s, v18.4s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umlal2 v20.2d, v2.4s, v17.4s
mul x4, x3, x12
mul x5, x3, x13
add v20.2d, v20.2d, v20.2d
mul x6, x3, x14
mul x7, x3, x15
umlal v20.2d, v0.2s, v0.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v20.2d, v12.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull v25.2d, v5.2s, v0.2s
adcs x7, x7, x9
adc x21, x16, x10
umlal v25.2d, v6.2s, v19.2s
ldr x3, [x0, #296]
umlal2 v25.2d, v6.4s, v19.4s
mul x2, x3, x12
mul x8, x3, x13
umlal v25.2d, v7.2s, v18.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v25.2d, v7.4s, v18.4s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v21.2d, v0.4s, v0.4s
adcs x7, x7, x9
adcs x21, x21, x16
umlal2 v21.2d, v11.4s, v19.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v10.2s, v1.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v21.2d, v12.2s, v19.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal v21.2d, v3.2s, v18.2s
mul x2, x3, x12
mul x8, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
adds x6, x6, x2
adcs x7, x7, x8
umlal v26.2d, v7.2s, v19.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v26.2d, v7.4s, v19.4s
adc x23, x10, x10
umlal v26.2d, v8.2s, v18.2s
umulh x2, x3, x12
umulh x8, x3, x13
umull2 v22.2d, v10.4s, v1.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v22.2d, v13.2s, v19.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v27.2d, v5.2s, v2.2s
adcs x23, x23, x16
adc x24, x10, x10
umlal2 v27.2d, v5.4s, v2.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v27.2d, v6.2s, v1.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v8.2s, v19.2s
adds x21, x21, x2
adcs x22, x22, x8
umlal2 v27.2d, v8.4s, v19.4s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v23.2d, v10.4s, v2.4s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v23.2d, v1.4s, v1.4s
adds x4, x4, x2
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x11, x22
adcs x5, x5, x8
add v23.2d, v23.2d, v23.2d
mul x9, x11, x23
adcs x6, x6, x9
umlal v23.2d, v10.2s, v3.2s
mul x16, x11, x24
adcs x7, x7, x16
umlal v23.2d, v11.2s, v2.2s
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v4.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umull v28.2d, v5.2s, v3.2s
umulh x16, x11, x24
adds x7, x7, x9
umlal2 v28.2d, v5.4s, v3.4s
adc x20, x20, x16
adds x16, x7, x7
umlal v28.2d, v6.2s, v2.2s
adc x9, x20, x20
lsr x7, x16, #1
umlal2 v28.2d, v6.4s, v2.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal v28.2d, v9.2s, v19.2s
adds x4, x4, x9
adcs x5, x5, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v24.2d, v11.4s, v2.4s
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
umlal2 v24.2d, v4.4s, v19.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
add v24.2d, v24.2d, v24.2d
ldp x21, x22, [x0, #480]
umlal v24.2d, v10.2s, v4.2s
ldp x23, x24, [x0, #496]
adds x12, x4, x21
umlal v24.2d, v11.2s, v3.2s
adcs x13, x5, x22
movz w2, #38, lsl #0
umlal v24.2d, v2.2s, v2.2s
adcs x14, x6, x23
adcs x15, x7, x24
umull v29.2d, v5.2s, v4.2s
csel x3, x2, x10, hs
adds x12, x12, x3
umlal2 v29.2d, v5.4s, v4.4s
adcs x13, x13, x10
adc x14, x14, x10
umlal v29.2d, v6.2s, v3.2s
mul x5, x12, x13
mul x6, x12, x14
umlal2 v29.2d, v6.4s, v3.4s
mul x7, x12, x15
umulh x2, x12, x13
umlal v29.2d, v7.2s, v2.2s
umulh x8, x12, x14
umulh x9, x12, x15
ldr q3, [x0, #720]
adds x6, x6, x2
adcs x7, x7, x8
ldr q4, [x0, #736]
adc x21, x9, x10
mul x2, x13, x14
ushr v2.2d, v29.2d, #25
mul x8, x13, x15
umulh x9, x13, x14
and v29.16b, v29.16b, v4.16b
umulh x16, x13, x15
adds x7, x7, x2
ushr v0.2d, v24.2d, #26
adcs x21, x21, x8
adc x22, x16, x10
and v24.16b, v24.16b, v3.16b
adds x21, x21, x9
adc x22, x22, x10
add v29.2d, v29.2d, v0.2d
mul x2, x14, x15
ushr v1.2d, v28.2d, #25
umulh x8, x14, x15
adds x22, x22, x2
and v28.16b, v28.16b, v4.16b
adc x23, x8, x10
adds x5, x5, x5
add v24.2d, v24.2d, v1.2d
adcs x6, x6, x6
adcs x7, x7, x7
ushr v0.2d, v23.2d, #26
adcs x21, x21, x21
adcs x22, x22, x22
and v23.16b, v23.16b, v3.16b
adcs x23, x23, x23
adc x24, x10, x10
add v28.2d, v28.2d, v0.2d
mul x4, x12, x12
umulh x2, x12, x12
ushr v1.2d, v27.2d, #25
mul x8, x13, x13
umulh x9, x13, x13
and v27.16b, v27.16b, v4.16b
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v1.2d
mul x3, x15, x15
umulh x11, x15, x15
ushr v0.2d, v22.2d, #26
adds x5, x5, x2
adcs x6, x6, x8
and v22.16b, v22.16b, v3.16b
adcs x7, x7, x9
adcs x21, x21, x16
add v27.2d, v27.2d, v0.2d
adcs x22, x22, x17
adcs x23, x23, x3
ushr v1.2d, v26.2d, #25
adc x24, x24, x11
movz w11, #38, lsl #0
and v26.16b, v26.16b, v4.16b
mul x2, x11, x21
add v22.2d, v22.2d, v1.2d
adds x4, x4, x2
mul x8, x11, x22
ushr v0.2d, v21.2d, #26
adcs x5, x5, x8
mul x9, x11, x23
and v21.16b, v21.16b, v3.16b
adcs x6, x6, x9
mul x16, x11, x24
add v26.2d, v26.2d, v0.2d
adcs x7, x7, x16
adc x20, x10, x10
ushr v1.2d, v25.2d, #25
umulh x2, x11, x21
umulh x8, x11, x22
and v25.16b, v25.16b, v4.16b
umulh x9, x11, x23
umulh x16, x11, x24
add v21.2d, v21.2d, v1.2d
adds x7, x7, x9
adc x20, x20, x16
ushr v0.2d, v20.2d, #26
adds x16, x7, x7
adc x9, x20, x20
and v20.16b, v20.16b, v3.16b
lsr x7, x16, #1
movz w11, #19, lsl #0
add v25.2d, v25.2d, v0.2d
mul x9, x9, x11
adds x4, x4, x9
add v20.2d, v20.2d, v2.2d
adcs x5, x5, x2
adcs x6, x6, x8
shl v0.2d, v2.2d, #1
adc x7, x7, x10
stp x4, x5, [x0, #160]
shl v2.2d, v2.2d, #4
stp x6, x7, [x0, #176]
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v0.2d
ldp x6, x7, [x0, #464]
add v20.2d, v20.2d, v2.2d
ldp x21, x22, [x0, #480]
ldp x23, x24, [x0, #496]
shl v25.2d, v25.2d, #26
subs x12, x4, x21
sbcs x13, x5, x22
add v20.2d, v20.2d, v25.2d
movz w2, #38, lsl #0
sbcs x14, x6, x23
shl v26.2d, v26.2d, #26
sbcs x15, x7, x24
csel x3, x10, x2, hs
add v21.2d, v21.2d, v26.2d
subs x12, x12, x3
sbcs x13, x13, x10
shl v27.2d, v27.2d, #26
sbcs x14, x14, x10
sbc x15, x15, x10
add v22.2d, v22.2d, v27.2d
mul x5, x12, x13
mul x6, x12, x14
shl v28.2d, v28.2d, #26
mul x7, x12, x15
umulh x2, x12, x13
add v23.2d, v23.2d, v28.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v29.2d, v29.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v24.2d, v24.2d, v29.2d
adc x21, x9, x10
mul x2, x13, x14
ldr q5, [x0, #704]
mul x8, x13, x15
umulh x9, x13, x14
ushr v25.2d, v20.2d, #51
umulh x16, x13, x15
adds x7, x7, x2
and v20.16b, v20.16b, v5.16b
adcs x21, x21, x8
adc x22, x16, x10
ushr v26.2d, v21.2d, #51
adds x21, x21, x9
and v21.16b, v21.16b, v5.16b
adc x22, x22, x10
mul x2, x14, x15
ushr v27.2d, v22.2d, #51
umulh x8, x14, x15
adds x22, x22, x2
and v22.16b, v22.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v28.2d, v23.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v23.16b, v23.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v29.2d, v24.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v24.16b, v24.16b, v5.16b
mul x4, x12, x12
umulh x2, x12, x12
add v21.2d, v21.2d, v25.2d
mul x8, x13, x13
umulh x9, x13, x13
add v22.2d, v22.2d, v26.2d
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v27.2d
mul x3, x15, x15
umulh x11, x15, x15
add v24.2d, v24.2d, v28.2d
adds x5, x5, x2
adcs x6, x6, x8
add v20.2d, v20.2d, v29.2d
adcs x7, x7, x9
adcs x21, x21, x16
shl v0.2d, v29.2d, #1
adcs x22, x22, x17
adcs x23, x23, x3
shl v2.2d, v29.2d, #4
adc x24, x24, x11
add v20.2d, v20.2d, v0.2d
movz w11, #38, lsl #0
mul x2, x11, x21
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
mul x8, x11, x22
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
mul x9, x11, x23
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
str q0, [x0, #1024]
adcs x7, x7, x16
adc x20, x10, x10
str q1, [x0, #1072]
umulh x2, x11, x21
umulh x8, x11, x22
trn1 v0.2d, v22.2d, v23.2d
umulh x9, x11, x23
umulh x16, x11, x24
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x9
adc x20, x20, x16
str q0, [x0, #1040]
adds x16, x7, x7
adc x9, x20, x20
str q1, [x0, #1088]
lsr x7, x16, #1
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
str q0, [x0, #1056]
adc x7, x7, x10
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
.globl lab_xc
lab_xc:
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
umulh x2, x3, x12
ldr q23, [x0, #272]
umulh x8, x3, x13
trn1 v24.2d, v20.2d, v21.2d
umulh x9, x3, x14
umulh x16, x3, x15
trn2 v25.2d, v20.2d, v21.2d
adds x5, x5, x2
trn1 v26.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v27.2d, v22.2d, v23.2d
adc x21, x16, x10
and v20.16b, v24.16b, v31.16b
ldr x3, [x0, #328]
mul x2, x3, x12
ushr v21.2d, v24.2d, #26
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
mul x16, x3, x15
uzp1 v0.4s, v20.4s, v21.4s
adds x5, x5, x2
shl v20.2d, v25.2d, #13
adcs x6, x6, x8
adcs x7, x7, x9
sri v20.2d, v24.2d, #51
adcs x21, x21, x16
and v20.16b, v20.16b, v31.16b
adc x22, x10, x10
umulh x2, x3, x12
ushr v21.2d, v25.2d, #13
umulh x8, x3, x13
and v21.16b, v21.16b, v30.16b
umulh x9, x3, x14
umulh x16, x3, x15
uzp1 v1.4s, v20.4s, v21.4s
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
and v21.16b, v26.16b, v30.16b
adcs x21, x21, x9
adc x22, x22, x16
uzp1 v2.4s, v20.4s, v21.4s
ldr x3, [x0, #336]
ushr v20.2d, v26.2d, #25
mul x2, x3, x12
mul x8, x3, x13
and v20.16b, v20.16b, v31.16b
mul x9, x3, x14
shl v21.2d, v27.2d, #13
mul x16, x3, x15
adds x6, x6, x2
sri v21.2d, v26.2d, #51
adcs x7, x7, x8
and v21.16b, v21.16b, v30.16b
adcs x21, x21, x9
adcs x22, x22, x16
uzp1 v3.4s, v20.4s, v21.4s
adc x23, x10, x10
ushr v20.2d, v27.2d, #12
umulh x2, x3, x12
umulh x8, x3, x13
and v20.16b, v20.16b, v31.16b
umulh x9, x3, x14
ushr v21.2d, v27.2d, #38
umulh x16, x3, x15
adds x7, x7, x2
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x8
add v10.4s, v0.4s, v0.4s
adcs x22, x22, x9
adc x23, x23, x16
add v11.4s, v1.4s, v1.4s
ldr x3, [x0, #344]
add v12.4s, v2.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
add v14.4s, v4.4s, v4.4s
mul x16, x3, x15
adds x7, x7, x2
ext v5.16b, v10.16b, v10.16b, #8
adcs x21, x21, x8
ext v6.16b, v11.16b, v11.16b, #8
adcs x22, x22, x9
adcs x23, x23, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x24, x10, x10
ext v8.16b, v13.16b, v13.16b, #8
umulh x2, x3, x12
ext v9.16b, v14.16b, v14.16b, #8
umulh x8, x3, x13
umulh x9, x3, x14
ldr q31, [x0, #752]
umulh x16, x3, x15
mul v15.4s, v0.4s, v31.4s
adds x21, x21, x2
adcs x22, x22, x8
mul v16.4s, v1.4s, v31.4s
adcs x23, x23, x9
mul v17.4s, v2.4s, v31.4s
adc x24, x24, x16
movz w11, #38, lsl #0
mul v18.4s, v3.4s, v31.4s
mul x2, x11, x21
mul v19.4s, v4.4s, v31.4s
adds x4, x4, x2
mul x8, x11, x22
umull2 v20.2d, v10.4s, v19.4s
adcs x5, x5, x8
umlal2 v20.2d, v11.4s, v18.4s
mul x9, x11, x23
adcs x6, x6, x9
umlal2 v20.2d, v2.4s, v17.4s
mul x16, x11, x24
add v20.2d, v20.2d, v20.2d
adcs x7, x7, x16
adc x20, x10, x10
umlal v20.2d, v0.2s, v0.2s
umulh x2, x11, x21
umlal v20.2d, v11.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umlal v20.2d, v12.2s, v18.2s
umulh x16, x11, x24
umull v25.2d, v5.2s, v0.2s
adds x7, x7, x9
adc x20, x20, x16
umlal v25.2d, v6.2s, v19.2s
adds x16, x7, x7
umlal2 v25.2d, v6.4s, v19.4s
adc x9, x20, x20
lsr x7, x16, #1
umlal v25.2d, v7.2s, v18.2s
movz w11, #19, lsl #0
umlal2 v25.2d, v7.4s, v18.4s
mul x9, x9, x11
adds x4, x4, x9
umull2 v21.2d, v0.4s, v0.4s
adcs x5, x5, x2
umlal2 v21.2d, v11.4s, v19.4s
adcs x6, x6, x8
umlal2 v21.2d, v12.4s, v18.4s
adc x7, x7, x10
stp x4, x5, [x0, #448]
add v21.2d, v21.2d, v21.2d
stp x6, x7, [x0, #464]
umlal v21.2d, v10.2s, v1.2s
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
umlal v21.2d, v12.2s, v19.2s
ldr x3, [x0, #288]
umlal v21.2d, v3.2s, v18.2s
mul x4, x3, x12
mul x5, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x6, x3, x14
umlal2 v26.2d, v5.4s, v1.4s
mul x7, x3, x15
umulh x2, x3, x12
umlal v26.2d, v7.2s, v19.2s
umulh x8, x3, x13
umlal2 v26.2d, v7.4s, v19.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v26.2d, v8.2s, v18.2s
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
adcs x7, x7, x9
umlal2 v22.2d, v12.4s, v19.4s
adc x21, x16, x10
umlal2 v22.2d, v3.4s, v18.4s
ldr x3, [x0, #296]
mul x2, x3, x12
add v22.2d, v22.2d, v22.2d
mul x8, x3, x13
umlal v22.2d, v10.2s, v2.2s
mul x9, x3, x14
mul x16, x3, x15
umlal v22.2d, v1.2s, v1.2s
adds x5, x5, x2
umlal v22.2d, v13.2s, v19.2s
adcs x6, x6, x8
adcs x7, x7, x9
umull v27.2d, v5.2s, v2.2s
adcs x21, x21, x16
umlal2 v27.2d, v5.4s, v2.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal v27.2d, v6.2s, v1.2s
umulh x8, x3, x13
umlal v27.2d, v8.2s, v19.2s
umulh x9, x3, x14
umlal2 v27.2d, v8.4s, v19.4s
umulh x16, x3, x15
adds x6, x6, x2
umull2 v23.2d, v10.4s, v2.4s
adcs x7, x7, x8
umlal2 v23.2d, v1.4s, v1.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v13.4s, v19.4s
ldr x3, [x0, #304]
add v23.2d, v23.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
umlal v23.2d, v10.2s, v3.2s
mul x9, x3, x14
umlal v23.2d, v11.2s, v2.2s
mul x16, x3, x15
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
umull v28.2d, v5.2s, v3.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v28.2d, v5.4s, v3.4s
adc x23, x10, x10
umlal v28.2d, v6.2s, v2.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal2 v28.2d, v6.4s, v2.4s
umulh x9, x3, x14
umlal v28.2d, v9.2s, v19.2s
umulh x16, x3, x15
adds x7, x7, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x21, x21, x8
umlal2 v24.2d, v11.4s, v2.4s
adcs x22, x22, x9
adc x23, x23, x16
umlal2 v24.2d, v4.4s, v19.4s
ldr x3, [x0, #312]
add v24.2d, v24.2d, v24.2d
mul x2, x3, x12
mul x8, x3, x13
umlal v24.2d, v10.2s, v4.2s
mul x9, x3, x14
umlal v24.2d, v11.2s, v3.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v24.2d, v2.2s, v2.2s
adcs x21, x21, x8
umull v29.2d, v5.2s, v4.2s
adcs x22, x22, x9
umlal2 v29.2d, v5.4s, v4.4s
adcs x23, x23, x16
adc x24, x10, x10
umlal v29.2d, v6.2s, v3.2s
umulh x2, x3, x12
umlal2 v29.2d, v6.4s, v3.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v29.2d, v7.2s, v2.2s
umulh x16, x3, x15
ldr q3, [x0, #720]
adds x21, x21, x2
adcs x22, x22, x8
ldr q4, [x0, #736]
adcs x23, x23, x9
ushr v2.2d, v29.2d, #25
adc x24, x24, x16
movz w11, #38, lsl #0
and v29.16b, v29.16b, v4.16b
mul x2, x11, x21
ushr v0.2d, v24.2d, #26
adds x4, x4, x2
mul x8, x11, x22
and v24.16b, v24.16b, v3.16b
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
mul x9, x11, x23
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
mul x16, x11, x24
and v28.16b, v28.16b, v4.16b
adcs x7, x7, x16
adc x20, x10, x10
add v24.2d, v24.2d, v1.2d
umulh x2, x11, x21
ushr v0.2d, v23.2d, #26
umulh x8, x11, x22
umulh x9, x11, x23
and v23.16b, v23.16b, v3.16b
umulh x16, x11, x24
add v28.2d, v28.2d, v0.2d
adds x7, x7, x9
adc x20, x20, x16
ushr v1.2d, v27.2d, #25
adds x16, x7, x7
and v27.16b, v27.16b, v4.16b
adc x9, x20, x20
lsr x7, x16, #1
add v23.2d, v23.2d, v1.2d
movz w11, #19, lsl #0
ushr v0.2d, v22.2d, #26
mul x9, x9, x11
and v22.16b, v22.16b, v3.16b
adds x4, x4, x9
adcs x5, x5, x2
add v27.2d, v27.2d, v0.2d
adcs x6, x6, x8
ushr v1.2d, v26.2d, #25
adc x7, x7, x10
stp x4, x5, [x0, #480]
and v26.16b, v26.16b, v4.16b
stp x6, x7, [x0, #496]
add v22.2d, v22.2d, v1.2d
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
ushr v0.2d, v21.2d, #26
ldp x21, x22, [x0, #480]
and v21.16b, v21.16b, v3.16b
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v26.2d, v26.2d, v0.2d
adcs x13, x5, x22
ushr v1.2d, v25.2d, #25
movz w2, #38, lsl #0
adcs x14, x6, x23
and v25.16b, v25.16b, v4.16b
adcs x15, x7, x24
add v21.2d, v21.2d, v1.2d
csel x3, x2, x10, hs
adds x12, x12, x3
ushr v0.2d, v20.2d, #26
adcs x13, x13, x10
and v20.16b, v20.16b, v3.16b
adc x14, x14, x10
mul x5, x12, x13
add v25.2d, v25.2d, v0.2d
mul x6, x12, x14
add v20.2d, v20.2d, v2.2d
mul x7, x12, x15
umulh x2, x12, x13
shl v0.2d, v2.2d, #1
umulh x8, x12, x14
shl v2.2d, v2.2d, #4
umulh x9, x12, x15
adds x6, x6, x2
add v20.2d, v20.2d, v0.2d
adcs x7, x7, x8
add v20.2d, v20.2d, v2.2d
adc x21, x9, x10
mul x2, x13, x14
shl v25.2d, v25.2d, #26
mul x8, x13, x15
add v20.2d, v20.2d, v25.2d
umulh x9, x13, x14
shl v26.2d, v26.2d, #26
umulh x16, x13, x15
adds x7, x7, x2
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x8
shl v27.2d, v27.2d, #26
adc x22, x16, x10
adds x21, x21, x9
add v22.2d, v22.2d, v27.2d
adc x22, x22, x10
shl v28.2d, v28.2d, #26
mul x2, x14, x15
umulh x8, x14, x15
add v23.2d, v23.2d, v28.2d
adds x22, x22, x2
shl v29.2d, v29.2d, #26
adc x23, x8, x10
adds x5, x5, x5
add v24.2d, v24.2d, v29.2d
adcs x6, x6, x6
ldr q5, [x0, #704]
adcs x7, x7, x7
adcs x21, x21, x21
ushr v25.2d, v20.2d, #51
adcs x22, x22, x22
and v20.16b, v20.16b, v5.16b
adcs x23, x23, x23
adc x24, x10, x10
ushr v26.2d, v21.2d, #51
mul x4, x12, x12
and v21.16b, v21.16b, v5.16b
umulh x2, x12, x12
mul x8, x13, x13
ushr v27.2d, v22.2d, #51
umulh x9, x13, x13
and v22.16b, v22.16b, v5.16b
mul x16, x14, x14
umulh x17, x14, x14
ushr v28.2d, v23.2d, #51
mul x3, x15, x15
and v23.16b, v23.16b, v5.16b
umulh x11, x15, x15
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
and v24.16b, v24.16b, v5.16b
adcs x7, x7, x9
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
movz w11, #38, lsl #0
add v24.2d, v24.2d, v28.2d
mul x2, x11, x21
add v20.2d, v20.2d, v29.2d
adds x4, x4, x2
mul x8, x11, x22
shl v0.2d, v29.2d, #1
adcs x5, x5, x8
shl v2.2d, v29.2d, #4
mul x9, x11, x23
adcs x6, x6, x9
add v20.2d, v20.2d, v0.2d
mul x16, x11, x24
add v20.2d, v20.2d, v2.2d
adcs x7, x7, x16
adc x20, x10, x10
trn1 v0.2d, v20.2d, v21.2d
umulh x2, x11, x21
trn2 v1.2d, v20.2d, v21.2d
umulh x8, x11, x22
umulh x9, x11, x23
str q0, [x0, #1024]
umulh x16, x11, x24
str q1, [x0, #1072]
adds x7, x7, x9
adc x20, x20, x16
trn1 v0.2d, v22.2d, v23.2d
adds x16, x7, x7
trn2 v1.2d, v22.2d, v23.2d
adc x9, x20, x20
lsr x7, x16, #1
str q0, [x0, #1040]
movz w11, #19, lsl #0
str q1, [x0, #1088]
mul x9, x9, x11
adds x4, x4, x9
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x2
trn2 v1.2d, v24.2d, v24.2d
adcs x6, x6, x8
adc x7, x7, x10
str q0, [x0, #1056]
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
.globl lab_xi
lab_xi:
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
umulh x2, x3, x12
ldr q23, [x0, #272]
umulh x8, x3, x13
trn1 v24.2d, v20.2d, v21.2d
umulh x9, x3, x14
umulh x16, x3, x15
trn2 v25.2d, v20.2d, v21.2d
adds x5, x5, x2
trn1 v26.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v27.2d, v22.2d, v23.2d
adc x21, x16, x10
and v20.16b, v24.16b, v31.16b
ldr x3, [x0, #328]
mul x2, x3, x12
ushr v21.2d, v24.2d, #26
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
mul x16, x3, x15
uzp1 v0.4s, v20.4s, v21.4s
adds x5, x5, x2
shl v20.2d, v25.2d, #13
adcs x6, x6, x8
adcs x7, x7, x9
sri v20.2d, v24.2d, #51
adcs x21, x21, x16
and v20.16b, v20.16b, v31.16b
adc x22, x10, x10
umulh x2, x3, x12
ushr v21.2d, v25.2d, #13
umulh x8, x3, x13
and v21.16b, v21.16b, v30.16b
umulh x9, x3, x14
umulh x16, x3, x15
uzp1 v1.4s, v20.4s, v21.4s
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adc x22, x22, x16
uzp1 v2.4s, v20.4s, v21.4s
ldr x3, [x0, #336]
mul x2, x3, x12
ushr v20.2d, v26.2d, #25
mul x8, x3, x13
and v20.16b, v20.16b, v31.16b
mul x9, x3, x14
mul x16, x3, x15
shl v21.2d, v27.2d, #13
adds x6, x6, x2
sri v21.2d, v26.2d, #51
adcs x7, x7, x8
and v21.16b, v21.16b, v30.16b
adcs x21, x21, x9
adcs x22, x22, x16
uzp1 v3.4s, v20.4s, v21.4s
adc x23, x10, x10
ushr v20.2d, v27.2d, #12
umulh x2, x3, x12
umulh x8, x3, x13
and v20.16b, v20.16b, v31.16b
umulh x9, x3, x14
ushr v21.2d, v27.2d, #38
umulh x16, x3, x15
adds x7, x7, x2
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x8
add v10.4s, v0.4s, v0.4s
adcs x22, x22, x9
adc x23, x23, x16
add v11.4s, v1.4s, v1.4s
ldr x3, [x0, #344]
add v12.4s, v2.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
add v14.4s, v4.4s, v4.4s
mul x16, x3, x15
adds x7, x7, x2
ext v5.16b, v10.16b, v10.16b, #8
adcs x21, x21, x8
ext v6.16b, v11.16b, v11.16b, #8
adcs x22, x22, x9
adcs x23, x23, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x24, x10, x10
ext v8.16b, v13.16b, v13.16b, #8
umulh x2, x3, x12
umulh x8, x3, x13
ext v9.16b, v14.16b, v14.16b, #8
umulh x9, x3, x14
ldr q31, [x0, #752]
umulh x16, x3, x15
adds x21, x21, x2
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x8
mul v16.4s, v1.4s, v31.4s
adcs x23, x23, x9
adc x24, x24, x16
mul v17.4s, v2.4s, v31.4s
movz w11, #38, lsl #0
mul v18.4s, v3.4s, v31.4s
mul x2, x11, x21
adds x4, x4, x2
mul v19.4s, v4.4s, v31.4s
mul x8, x11, x22
umull2 v20.2d, v10.4s, v19.4s
adcs x5, x5, x8
mul x9, x11, x23
umlal2 v20.2d, v11.4s, v18.4s
adcs x6, x6, x9
umlal2 v20.2d, v2.4s, v17.4s
mul x16, x11, x24
adcs x7, x7, x16
add v20.2d, v20.2d, v20.2d
adc x20, x10, x10
umlal v20.2d, v0.2s, v0.2s
umulh x2, x11, x21
umlal v20.2d, v11.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umlal v20.2d, v12.2s, v18.2s
umulh x16, x11, x24
umull v25.2d, v5.2s, v0.2s
adds x7, x7, x9
adc x20, x20, x16
umlal v25.2d, v6.2s, v19.2s
adds x16, x7, x7
umlal2 v25.2d, v6.4s, v19.4s
adc x9, x20, x20
lsr x7, x16, #1
umlal v25.2d, v7.2s, v18.2s
movz w11, #19, lsl #0
umlal2 v25.2d, v7.4s, v18.4s
mul x9, x9, x11
adds x4, x4, x9
umull2 v21.2d, v0.4s, v0.4s
adcs x5, x5, x2
umlal2 v21.2d, v11.4s, v19.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v21.2d, v12.4s, v18.4s
stp x4, x5, [x0, #448]
add v21.2d, v21.2d, v21.2d
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal v21.2d, v10.2s, v1.2s
ldp x14, x15, [x0, #272]
umlal v21.2d, v12.2s, v19.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal v21.2d, v3.2s, v18.2s
mul x5, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x6, x3, x14
mul x7, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
umulh x2, x3, x12
umlal v26.2d, v7.2s, v19.2s
umulh x8, x3, x13
umulh x9, x3, x14
umlal2 v26.2d, v7.4s, v19.4s
umulh x16, x3, x15
umlal v26.2d, v8.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v22.2d, v10.4s, v1.4s
adcs x7, x7, x9
umlal2 v22.2d, v12.4s, v19.4s
adc x21, x16, x10
ldr x3, [x0, #296]
umlal2 v22.2d, v3.4s, v18.4s
mul x2, x3, x12
add v22.2d, v22.2d, v22.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v10.2s, v2.2s
mul x16, x3, x15
umlal v22.2d, v1.2s, v1.2s
adds x5, x5, x2
adcs x6, x6, x8
umlal v22.2d, v13.2s, v19.2s
adcs x7, x7, x9
umull v27.2d, v5.2s, v2.2s
adcs x21, x21, x16
umlal2 v27.2d, v5.4s, v2.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal v27.2d, v6.2s, v1.2s
umulh x8, x3, x13
umlal v27.2d, v8.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v27.2d, v8.4s, v19.4s
adds x6, x6, x2
umull2 v23.2d, v10.4s, v2.4s
adcs x7, x7, x8
adcs x21, x21, x9
umlal2 v23.2d, v1.4s, v1.4s
adc x22, x22, x16
umlal2 v23.2d, v13.4s, v19.4s
ldr x3, [x0, #304]
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
umlal v23.2d, v10.2s, v3.2s
mul x9, x3, x14
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
umull v28.2d, v5.2s, v3.2s
adcs x22, x22, x16
umlal2 v28.2d, v5.4s, v3.4s
adc x23, x10, x10
umulh x2, x3, x12
umlal v28.2d, v6.2s, v2.2s
umulh x8, x3, x13
umlal2 v28.2d, v6.4s, v2.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v28.2d, v9.2s, v19.2s
adds x7, x7, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal2 v24.2d, v11.4s, v2.4s
adc x23, x23, x16
umlal2 v24.2d, v4.4s, v19.4s
ldr x3, [x0, #312]
mul x2, x3, x12
add v24.2d, v24.2d, v24.2d
mul x8, x3, x13
umlal v24.2d, v10.2s, v4.2s
mul x9, x3, x14
mul x16, x3, x15
umlal v24.2d, v11.2s, v3.2s
adds x7, x7, x2
umlal v24.2d, v2.2s, v2.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v29.2d, v5.2s, v4.2s
adcs x23, x23, x16
umlal2 v29.2d, v5.4s, v4.4s
adc x24, x10, x10
umulh x2, x3, x12
umlal v29.2d, v6.2s, v3.2s
umulh x8, x3, x13
umlal2 v29.2d, v6.4s, v3.4s
umulh x9, x3, x14
umlal v29.2d, v7.2s, v2.2s
umulh x16, x3, x15
adds x21, x21, x2
ldr q3, [x0, #720]
adcs x22, x22, x8
ldr q4, [x0, #736]
adcs x23, x23, x9
adc x24, x24, x16
ushr v2.2d, v29.2d, #25
movz w11, #38, lsl #0
and v29.16b, v29.16b, v4.16b
mul x2, x11, x21
adds x4, x4, x2
ushr v0.2d, v24.2d, #26
mul x8, x11, x22
and v24.16b, v24.16b, v3.16b
adcs x5, x5, x8
mul x9, x11, x23
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
mul x16, x11, x24
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x20, x10, x10
add v24.2d, v24.2d, v1.2d
umulh x2, x11, x21
umulh x8, x11, x22
ushr v0.2d, v23.2d, #26
umulh x9, x11, x23
and v23.16b, v23.16b, v3.16b
umulh x16, x11, x24
adds x7, x7, x9
add v28.2d, v28.2d, v0.2d
adc x20, x20, x16
ushr v1.2d, v27.2d, #25
adds x16, x7, x7
adc x9, x20, x20
and v27.16b, v27.16b, v4.16b
lsr x7, x16, #1
add v23.2d, v23.2d, v1.2d
movz w11, #19, lsl #0
mul x9, x9, x11
ushr v0.2d, v22.2d, #26
adds x4, x4, x9
and v22.16b, v22.16b, v3.16b
adcs x5, x5, x2
adcs x6, x6, x8
add v27.2d, v27.2d, v0.2d
adc x7, x7, x10
ushr v1.2d, v26.2d, #25
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
and v26.16b, v26.16b, v4.16b
ldp x4, x5, [x0, #448]
add v22.2d, v22.2d, v1.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v0.2d, v21.2d, #26
ldp x23, x24, [x0, #496]
and v21.16b, v21.16b, v3.16b
subs x12, x4, x21
sbcs x13, x5, x22
add v26.2d, v26.2d, v0.2d
movz w2, #38, lsl #0
ushr v1.2d, v25.2d, #25
sbcs x14, x6, x23
and v25.16b, v25.16b, v4.16b
sbcs x15, x7, x24
csel x3, x10, x2, hs
add v21.2d, v21.2d, v1.2d
subs x12, x12, x3
ushr v0.2d, v20.2d, #26
sbcs x13, x13, x10
sbcs x14, x14, x10
and v20.16b, v20.16b, v3.16b
sbc x15, x15, x10
add v25.2d, v25.2d, v0.2d
mul x5, x12, x13
mul x6, x12, x14
add v20.2d, v20.2d, v2.2d
mul x7, x12, x15
shl v0.2d, v2.2d, #1
umulh x2, x12, x13
umulh x8, x12, x14
shl v2.2d, v2.2d, #4
umulh x9, x12, x15
add v20.2d, v20.2d, v0.2d
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v2.2d
adc x21, x9, x10
shl v25.2d, v25.2d, #26
mul x2, x13, x14
mul x8, x13, x15
add v20.2d, v20.2d, v25.2d
umulh x9, x13, x14
shl v26.2d, v26.2d, #26
umulh x16, x13, x15
adds x7, x7, x2
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x8
shl v27.2d, v27.2d, #26
adc x22, x16, x10
adds x21, x21, x9
add v22.2d, v22.2d, v27.2d
adc x22, x22, x10
shl v28.2d, v28.2d, #26
mul x2, x14, x15
umulh x8, x14, x15
add v23.2d, v23.2d, v28.2d
adds x22, x22, x2
shl v29.2d, v29.2d, #26
adc x23, x8, x10
adds x5, x5, x5
add v24.2d, v24.2d, v29.2d
adcs x6, x6, x6
ldr q5, [x0, #704]
adcs x7, x7, x7
adcs x21, x21, x21
ushr v25.2d, v20.2d, #51
adcs x22, x22, x22
and v20.16b, v20.16b, v5.16b
adcs x23, x23, x23
adc x24, x10, x10
ushr v26.2d, v21.2d, #51
mul x4, x12, x12
and v21.16b, v21.16b, v5.16b
umulh x2, x12, x12
mul x8, x13, x13
ushr v27.2d, v22.2d, #51
umulh x9, x13, x13
and v22.16b, v22.16b, v5.16b
mul x16, x14, x14
ushr v28.2d, v23.2d, #51
umulh x17, x14, x14
mul x3, x15, x15
and v23.16b, v23.16b, v5.16b
umulh x11, x15, x15
ushr v29.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v24.16b, v24.16b, v5.16b
adcs x7, x7, x9
add v21.2d, v21.2d, v25.2d
adcs x21, x21, x16
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
movz w11, #38, lsl #0
add v24.2d, v24.2d, v28.2d
mul x2, x11, x21
add v20.2d, v20.2d, v29.2d
adds x4, x4, x2
mul x8, x11, x22
shl v0.2d, v29.2d, #1
adcs x5, x5, x8
shl v2.2d, v29.2d, #4
mul x9, x11, x23
adcs x6, x6, x9
add v20.2d, v20.2d, v0.2d
mul x16, x11, x24
add v20.2d, v20.2d, v2.2d
adcs x7, x7, x16
adc x20, x10, x10
trn1 v0.2d, v20.2d, v21.2d
umulh x2, x11, x21
trn2 v1.2d, v20.2d, v21.2d
umulh x8, x11, x22
umulh x9, x11, x23
str q0, [x0, #1024]
umulh x16, x11, x24
str q1, [x0, #1072]
adds x7, x7, x9
adc x20, x20, x16
trn1 v0.2d, v22.2d, v23.2d
adds x16, x7, x7
trn2 v1.2d, v22.2d, v23.2d
adc x9, x20, x20
lsr x7, x16, #1
str q0, [x0, #1040]
movz w11, #19, lsl #0
str q1, [x0, #1088]
mul x9, x9, x11
adds x4, x4, x9
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x2
trn2 v1.2d, v24.2d, v24.2d
adcs x6, x6, x8
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
.globl lab_xf
lab_xf:
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
umulh x9, x3, x14
ldr q23, [x0, #272]
umulh x16, x3, x15
adds x5, x5, x2
trn1 v24.2d, v20.2d, v21.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v25.2d, v20.2d, v21.2d
adc x21, x16, x10
ldr x3, [x0, #328]
trn1 v26.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v24.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v24.2d, #26
adcs x7, x7, x9
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
umulh x16, x3, x15
sri v20.2d, v24.2d, #51
adds x6, x6, x2
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
adc x22, x22, x16
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v2.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v26.2d, #25
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x7, x7, x2
adcs x21, x21, x8
shl v21.2d, v27.2d, #13
adcs x22, x22, x9
adc x23, x23, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #344]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x7, x7, x2
adcs x21, x21, x8
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x9
adcs x23, x23, x16
ushr v21.2d, v27.2d, #38
adc x24, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v10.4s, v0.4s, v0.4s
umulh x16, x3, x15
adds x21, x21, x2
add v11.4s, v1.4s, v1.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v12.4s, v2.4s, v2.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v13.4s, v3.4s, v3.4s
mul x2, x11, x21
adds x4, x4, x2
add v14.4s, v4.4s, v4.4s
mul x8, x11, x22
adcs x5, x5, x8
ext v5.16b, v10.16b, v10.16b, #8
mul x9, x11, x23
adcs x6, x6, x9
ext v6.16b, v11.16b, v11.16b, #8
mul x16, x11, x24
adcs x7, x7, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x20, x10, x10
umulh x2, x11, x21
ext v8.16b, v13.16b, v13.16b, #8
umulh x8, x11, x22
umulh x9, x11, x23
ext v9.16b, v14.16b, v14.16b, #8
umulh x16, x11, x24
adds x7, x7, x9
ldr q31, [x0, #752]
adc x20, x20, x16
mul v15.4s, v0.4s, v31.4s
adds x16, x7, x7
adc x9, x20, x20
mul v16.4s, v1.4s, v31.4s
lsr x7, x16, #1
movz w11, #19, lsl #0
mul v17.4s, v2.4s, v31.4s
mul x9, x9, x11
adds x4, x4, x9
mul v18.4s, v3.4s, v31.4s
adcs x5, x5, x2
adcs x6, x6, x8
mul v19.4s, v4.4s, v31.4s
adc x7, x7, x10
stp x4, x5, [x0, #448]
umull2 v20.2d, v10.4s, v19.4s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal2 v20.2d, v11.4s, v18.4s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umlal2 v20.2d, v2.4s, v17.4s
mul x4, x3, x12
mul x5, x3, x13
add v20.2d, v20.2d, v20.2d
mul x6, x3, x14
mul x7, x3, x15
umlal v20.2d, v0.2s, v0.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v20.2d, v12.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull v25.2d, v5.2s, v0.2s
adcs x7, x7, x9
adc x21, x16, x10
umlal v25.2d, v6.2s, v19.2s
ldr x3, [x0, #296]
umlal2 v25.2d, v6.4s, v19.4s
mul x2, x3, x12
mul x8, x3, x13
umlal v25.2d, v7.2s, v18.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v25.2d, v7.4s, v18.4s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v21.2d, v0.4s, v0.4s
adcs x7, x7, x9
adcs x21, x21, x16
umlal2 v21.2d, v11.4s, v19.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v10.2s, v1.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v21.2d, v12.2s, v19.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal v21.2d, v3.2s, v18.2s
mul x2, x3, x12
mul x8, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
adds x6, x6, x2
adcs x7, x7, x8
umlal v26.2d, v7.2s, v19.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v26.2d, v7.4s, v19.4s
adc x23, x10, x10
umlal v26.2d, v8.2s, v18.2s
umulh x2, x3, x12
umulh x8, x3, x13
umull2 v22.2d, v10.4s, v1.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v22.2d, v13.2s, v19.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v27.2d, v5.2s, v2.2s
adcs x23, x23, x16
adc x24, x10, x10
umlal2 v27.2d, v5.4s, v2.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v27.2d, v6.2s, v1.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v8.2s, v19.2s
adds x21, x21, x2
adcs x22, x22, x8
umlal2 v27.2d, v8.4s, v19.4s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v23.2d, v10.4s, v2.4s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v23.2d, v1.4s, v1.4s
adds x4, x4, x2
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x11, x22
adcs x5, x5, x8
add v23.2d, v23.2d, v23.2d
mul x9, x11, x23
adcs x6, x6, x9
umlal v23.2d, v10.2s, v3.2s
mul x16, x11, x24
adcs x7, x7, x16
umlal v23.2d, v11.2s, v2.2s
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v4.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umull v28.2d, v5.2s, v3.2s
umulh x16, x11, x24
adds x7, x7, x9
umlal2 v28.2d, v5.4s, v3.4s
adc x20, x20, x16
adds x16, x7, x7
umlal v28.2d, v6.2s, v2.2s
adc x9, x20, x20
lsr x7, x16, #1
umlal2 v28.2d, v6.4s, v2.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal v28.2d, v9.2s, v19.2s
adds x4, x4, x9
adcs x5, x5, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v24.2d, v11.4s, v2.4s
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
umlal2 v24.2d, v4.4s, v19.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
add v24.2d, v24.2d, v24.2d
ldp x21, x22, [x0, #480]
umlal v24.2d, v10.2s, v4.2s
ldp x23, x24, [x0, #496]
subs x12, x4, x21
umlal v24.2d, v11.2s, v3.2s
sbcs x13, x5, x22
movz w2, #38, lsl #0
umlal v24.2d, v2.2s, v2.2s
sbcs x14, x6, x23
sbcs x15, x7, x24
umull v29.2d, v5.2s, v4.2s
csel x3, x10, x2, hs
subs x12, x12, x3
umlal2 v29.2d, v5.4s, v4.4s
sbcs x13, x13, x10
sbcs x14, x14, x10
umlal v29.2d, v6.2s, v3.2s
sbc x15, x15, x10
mul x5, x12, x13
umlal2 v29.2d, v6.4s, v3.4s
mul x6, x12, x14
mul x7, x12, x15
umlal v29.2d, v7.2s, v2.2s
umulh x2, x12, x13
umulh x8, x12, x14
ldr q3, [x0, #720]
umulh x9, x12, x15
adds x6, x6, x2
ldr q4, [x0, #736]
adcs x7, x7, x8
adc x21, x9, x10
ushr v2.2d, v29.2d, #25
mul x2, x13, x14
mul x8, x13, x15
and v29.16b, v29.16b, v4.16b
umulh x9, x13, x14
umulh x16, x13, x15
ushr v0.2d, v24.2d, #26
adds x7, x7, x2
adcs x21, x21, x8
and v24.16b, v24.16b, v3.16b
adc x22, x16, x10
adds x21, x21, x9
add v29.2d, v29.2d, v0.2d
adc x22, x22, x10
ushr v1.2d, v28.2d, #25
mul x2, x14, x15
umulh x8, x14, x15
and v28.16b, v28.16b, v4.16b
adds x22, x22, x2
adc x23, x8, x10
add v24.2d, v24.2d, v1.2d
adds x5, x5, x5
adcs x6, x6, x6
ushr v0.2d, v23.2d, #26
adcs x7, x7, x7
adcs x21, x21, x21
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x22
adcs x23, x23, x23
add v28.2d, v28.2d, v0.2d
adc x24, x10, x10
mul x4, x12, x12
ushr v1.2d, v27.2d, #25
umulh x2, x12, x12
mul x8, x13, x13
and v27.16b, v27.16b, v4.16b
umulh x9, x13, x13
mul x16, x14, x14
add v23.2d, v23.2d, v1.2d
umulh x17, x14, x14
mul x3, x15, x15
ushr v0.2d, v22.2d, #26
umulh x11, x15, x15
adds x5, x5, x2
and v22.16b, v22.16b, v3.16b
adcs x6, x6, x8
adcs x7, x7, x9
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x16
adcs x22, x22, x17
ushr v1.2d, v26.2d, #25
adcs x23, x23, x3
adc x24, x24, x11
and v26.16b, v26.16b, v4.16b
movz w11, #38, lsl #0
add v22.2d, v22.2d, v1.2d
mul x2, x11, x21
adds x4, x4, x2
ushr v0.2d, v21.2d, #26
mul x8, x11, x22
adcs x5, x5, x8
and v21.16b, v21.16b, v3.16b
mul x9, x11, x23
adcs x6, x6, x9
add v26.2d, v26.2d, v0.2d
mul x16, x11, x24
adcs x7, x7, x16
ushr v1.2d, v25.2d, #25
adc x20, x10, x10
umulh x2, x11, x21
and v25.16b, v25.16b, v4.16b
umulh x8, x11, x22
umulh x9, x11, x23
add v21.2d, v21.2d, v1.2d
umulh x16, x11, x24
adds x7, x7, x9
ushr v0.2d, v20.2d, #26
adc x20, x20, x16
adds x16, x7, x7
and v20.16b, v20.16b, v3.16b
adc x9, x20, x20
lsr x7, x16, #1
add v25.2d, v25.2d, v0.2d
movz w11, #19, lsl #0
mul x9, x9, x11
add v20.2d, v20.2d, v2.2d
adds x4, x4, x9
adcs x5, x5, x2
shl v0.2d, v2.2d, #1
adcs x6, x6, x8
adc x7, x7, x10
shl v2.2d, v2.2d, #4
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
shl v25.2d, v25.2d, #26
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v20.2d, v20.2d, v25.2d
adcs x13, x5, x22
movz w2, #38, lsl #0
shl v26.2d, v26.2d, #26
adcs x14, x6, x23
adcs x15, x7, x24
add v21.2d, v21.2d, v26.2d
csel x3, x2, x10, hs
adds x12, x12, x3
shl v27.2d, v27.2d, #26
adcs x13, x13, x10
adc x14, x14, x10
add v22.2d, v22.2d, v27.2d
mul x5, x12, x13
mul x6, x12, x14
shl v28.2d, v28.2d, #26
mul x7, x12, x15
umulh x2, x12, x13
add v23.2d, v23.2d, v28.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v29.2d, v29.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v24.2d, v24.2d, v29.2d
adc x21, x9, x10
mul x2, x13, x14
ldr q5, [x0, #704]
mul x8, x13, x15
umulh x9, x13, x14
ushr v25.2d, v20.2d, #51
umulh x16, x13, x15
adds x7, x7, x2
and v20.16b, v20.16b, v5.16b
adcs x21, x21, x8
adc x22, x16, x10
ushr v26.2d, v21.2d, #51
adds x21, x21, x9
and v21.16b, v21.16b, v5.16b
adc x22, x22, x10
mul x2, x14, x15
ushr v27.2d, v22.2d, #51
umulh x8, x14, x15
adds x22, x22, x2
and v22.16b, v22.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v28.2d, v23.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v23.16b, v23.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v29.2d, v24.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v24.16b, v24.16b, v5.16b
mul x4, x12, x12
umulh x2, x12, x12
add v21.2d, v21.2d, v25.2d
mul x8, x13, x13
umulh x9, x13, x13
add v22.2d, v22.2d, v26.2d
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v27.2d
mul x3, x15, x15
umulh x11, x15, x15
add v24.2d, v24.2d, v28.2d
adds x5, x5, x2
adcs x6, x6, x8
add v20.2d, v20.2d, v29.2d
adcs x7, x7, x9
adcs x21, x21, x16
shl v0.2d, v29.2d, #1
adcs x22, x22, x17
adcs x23, x23, x3
shl v2.2d, v29.2d, #4
adc x24, x24, x11
add v20.2d, v20.2d, v0.2d
movz w11, #38, lsl #0
mul x2, x11, x21
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
mul x8, x11, x22
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
mul x9, x11, x23
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
str q0, [x0, #1024]
adcs x7, x7, x16
adc x20, x10, x10
str q1, [x0, #1072]
umulh x2, x11, x21
umulh x8, x11, x22
trn1 v0.2d, v22.2d, v23.2d
umulh x9, x11, x23
umulh x16, x11, x24
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x9
adc x20, x20, x16
str q0, [x0, #1040]
adds x16, x7, x7
adc x9, x20, x20
str q1, [x0, #1088]
lsr x7, x16, #1
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
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
.globl lab_xg
lab_xg:
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
umulh x9, x3, x14
ldr q23, [x0, #272]
umulh x16, x3, x15
adds x5, x5, x2
trn1 v24.2d, v20.2d, v21.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v25.2d, v20.2d, v21.2d
adc x21, x16, x10
ldr x3, [x0, #328]
trn1 v26.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v24.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v24.2d, #26
adcs x7, x7, x9
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
umulh x16, x3, x15
sri v20.2d, v24.2d, #51
adds x6, x6, x2
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
adc x22, x22, x16
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v2.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v26.2d, #25
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x7, x7, x2
adcs x21, x21, x8
shl v21.2d, v27.2d, #13
adcs x22, x22, x9
adc x23, x23, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #344]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x7, x7, x2
adcs x21, x21, x8
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x9
adcs x23, x23, x16
ushr v21.2d, v27.2d, #38
adc x24, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v10.4s, v0.4s, v0.4s
umulh x16, x3, x15
adds x21, x21, x2
add v11.4s, v1.4s, v1.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v12.4s, v2.4s, v2.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v13.4s, v3.4s, v3.4s
mul x2, x11, x21
adds x4, x4, x2
add v14.4s, v4.4s, v4.4s
mul x8, x11, x22
adcs x5, x5, x8
ext v5.16b, v10.16b, v10.16b, #8
mul x9, x11, x23
adcs x6, x6, x9
ext v6.16b, v11.16b, v11.16b, #8
mul x16, x11, x24
adcs x7, x7, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x20, x10, x10
umulh x2, x11, x21
ext v8.16b, v13.16b, v13.16b, #8
umulh x8, x11, x22
umulh x9, x11, x23
ext v9.16b, v14.16b, v14.16b, #8
umulh x16, x11, x24
adds x7, x7, x9
ldr q31, [x0, #752]
adc x20, x20, x16
mul v15.4s, v0.4s, v31.4s
adds x16, x7, x7
adc x9, x20, x20
mul v16.4s, v1.4s, v31.4s
lsr x7, x16, #1
movz w11, #19, lsl #0
mul v17.4s, v2.4s, v31.4s
mul x9, x9, x11
adds x4, x4, x9
mul v18.4s, v3.4s, v31.4s
adcs x5, x5, x2
adcs x6, x6, x8
mul v19.4s, v4.4s, v31.4s
adc x7, x7, x10
stp x4, x5, [x0, #448]
umull2 v20.2d, v10.4s, v19.4s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
umlal2 v20.2d, v11.4s, v18.4s
ldp x14, x15, [x0, #272]
ldr x3, [x0, #288]
umlal2 v20.2d, v2.4s, v17.4s
mul x4, x3, x12
mul x5, x3, x13
add v20.2d, v20.2d, v20.2d
mul x6, x3, x14
mul x7, x3, x15
umlal v20.2d, v0.2s, v0.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v20.2d, v12.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull v25.2d, v5.2s, v0.2s
adcs x7, x7, x9
adc x21, x16, x10
umlal v25.2d, v6.2s, v19.2s
ldr x3, [x0, #296]
umlal2 v25.2d, v6.4s, v19.4s
mul x2, x3, x12
mul x8, x3, x13
umlal v25.2d, v7.2s, v18.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v25.2d, v7.4s, v18.4s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v21.2d, v0.4s, v0.4s
adcs x7, x7, x9
adcs x21, x21, x16
umlal2 v21.2d, v11.4s, v19.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v10.2s, v1.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v21.2d, v12.2s, v19.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal v21.2d, v3.2s, v18.2s
mul x2, x3, x12
mul x8, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
adds x6, x6, x2
adcs x7, x7, x8
umlal v26.2d, v7.2s, v19.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v26.2d, v7.4s, v19.4s
adc x23, x10, x10
umlal v26.2d, v8.2s, v18.2s
umulh x2, x3, x12
umulh x8, x3, x13
umull2 v22.2d, v10.4s, v1.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #312]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v22.2d, v13.2s, v19.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v27.2d, v5.2s, v2.2s
adcs x23, x23, x16
adc x24, x10, x10
umlal2 v27.2d, v5.4s, v2.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v27.2d, v6.2s, v1.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v8.2s, v19.2s
adds x21, x21, x2
adcs x22, x22, x8
umlal2 v27.2d, v8.4s, v19.4s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v23.2d, v10.4s, v2.4s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v23.2d, v1.4s, v1.4s
adds x4, x4, x2
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x11, x22
adcs x5, x5, x8
add v23.2d, v23.2d, v23.2d
mul x9, x11, x23
adcs x6, x6, x9
umlal v23.2d, v10.2s, v3.2s
mul x16, x11, x24
adcs x7, x7, x16
umlal v23.2d, v11.2s, v2.2s
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v4.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umull v28.2d, v5.2s, v3.2s
umulh x16, x11, x24
adds x7, x7, x9
umlal2 v28.2d, v5.4s, v3.4s
adc x20, x20, x16
adds x16, x7, x7
umlal v28.2d, v6.2s, v2.2s
adc x9, x20, x20
lsr x7, x16, #1
umlal2 v28.2d, v6.4s, v2.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal v28.2d, v9.2s, v19.2s
adds x4, x4, x9
adcs x5, x5, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v24.2d, v11.4s, v2.4s
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
umlal2 v24.2d, v4.4s, v19.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
add v24.2d, v24.2d, v24.2d
ldp x21, x22, [x0, #480]
umlal v24.2d, v10.2s, v4.2s
ldp x23, x24, [x0, #496]
subs x12, x4, x21
umlal v24.2d, v11.2s, v3.2s
sbcs x13, x5, x22
movz w2, #38, lsl #0
umlal v24.2d, v2.2s, v2.2s
sbcs x14, x6, x23
sbcs x15, x7, x24
umull v29.2d, v5.2s, v4.2s
csel x3, x10, x2, hs
subs x12, x12, x3
umlal2 v29.2d, v5.4s, v4.4s
sbcs x13, x13, x10
sbcs x14, x14, x10
umlal v29.2d, v6.2s, v3.2s
sbc x15, x15, x10
mul x5, x12, x13
umlal2 v29.2d, v6.4s, v3.4s
mul x6, x12, x14
mul x7, x12, x15
umlal v29.2d, v7.2s, v2.2s
umulh x2, x12, x13
umulh x8, x12, x14
ldr q3, [x0, #720]
umulh x9, x12, x15
adds x6, x6, x2
ldr q4, [x0, #736]
adcs x7, x7, x8
adc x21, x9, x10
ushr v2.2d, v29.2d, #25
mul x2, x13, x14
mul x8, x13, x15
and v29.16b, v29.16b, v4.16b
umulh x9, x13, x14
umulh x16, x13, x15
ushr v0.2d, v24.2d, #26
adds x7, x7, x2
adcs x21, x21, x8
and v24.16b, v24.16b, v3.16b
adc x22, x16, x10
adds x21, x21, x9
add v29.2d, v29.2d, v0.2d
adc x22, x22, x10
ushr v1.2d, v28.2d, #25
mul x2, x14, x15
umulh x8, x14, x15
and v28.16b, v28.16b, v4.16b
adds x22, x22, x2
adc x23, x8, x10
add v24.2d, v24.2d, v1.2d
adds x5, x5, x5
adcs x6, x6, x6
ushr v0.2d, v23.2d, #26
adcs x7, x7, x7
adcs x21, x21, x21
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x22
adcs x23, x23, x23
add v28.2d, v28.2d, v0.2d
adc x24, x10, x10
mul x4, x12, x12
ushr v1.2d, v27.2d, #25
umulh x2, x12, x12
mul x8, x13, x13
and v27.16b, v27.16b, v4.16b
umulh x9, x13, x13
mul x16, x14, x14
add v23.2d, v23.2d, v1.2d
umulh x17, x14, x14
mul x3, x15, x15
ushr v0.2d, v22.2d, #26
umulh x11, x15, x15
adds x5, x5, x2
and v22.16b, v22.16b, v3.16b
adcs x6, x6, x8
adcs x7, x7, x9
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x16
adcs x22, x22, x17
ushr v1.2d, v26.2d, #25
adcs x23, x23, x3
adc x24, x24, x11
and v26.16b, v26.16b, v4.16b
movz w11, #38, lsl #0
add v22.2d, v22.2d, v1.2d
mul x2, x11, x21
adds x4, x4, x2
ushr v0.2d, v21.2d, #26
mul x8, x11, x22
adcs x5, x5, x8
and v21.16b, v21.16b, v3.16b
mul x9, x11, x23
adcs x6, x6, x9
add v26.2d, v26.2d, v0.2d
mul x16, x11, x24
adcs x7, x7, x16
ushr v1.2d, v25.2d, #25
adc x20, x10, x10
umulh x2, x11, x21
and v25.16b, v25.16b, v4.16b
umulh x8, x11, x22
umulh x9, x11, x23
add v21.2d, v21.2d, v1.2d
umulh x16, x11, x24
adds x7, x7, x9
ushr v0.2d, v20.2d, #26
adc x20, x20, x16
adds x16, x7, x7
and v20.16b, v20.16b, v3.16b
adc x9, x20, x20
lsr x7, x16, #1
add v25.2d, v25.2d, v0.2d
movz w11, #19, lsl #0
mul x9, x9, x11
add v20.2d, v20.2d, v2.2d
adds x4, x4, x9
adcs x5, x5, x2
shl v0.2d, v2.2d, #1
adcs x6, x6, x8
adc x7, x7, x10
shl v2.2d, v2.2d, #4
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
shl v25.2d, v25.2d, #26
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v20.2d, v20.2d, v25.2d
adcs x13, x5, x22
movz w2, #38, lsl #0
shl v26.2d, v26.2d, #26
adcs x14, x6, x23
adcs x15, x7, x24
add v21.2d, v21.2d, v26.2d
csel x3, x2, x10, hs
adds x12, x12, x3
shl v27.2d, v27.2d, #26
adcs x13, x13, x10
adc x14, x14, x10
add v22.2d, v22.2d, v27.2d
mul x5, x12, x13
mul x6, x12, x14
shl v28.2d, v28.2d, #26
mul x7, x12, x15
umulh x2, x12, x13
add v23.2d, v23.2d, v28.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v29.2d, v29.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v24.2d, v24.2d, v29.2d
adc x21, x9, x10
mul x2, x13, x14
ldr q5, [x0, #704]
mul x8, x13, x15
umulh x9, x13, x14
ushr v25.2d, v20.2d, #51
umulh x16, x13, x15
adds x7, x7, x2
and v20.16b, v20.16b, v5.16b
adcs x21, x21, x8
adc x22, x16, x10
ushr v26.2d, v21.2d, #51
adds x21, x21, x9
and v21.16b, v21.16b, v5.16b
adc x22, x22, x10
mul x2, x14, x15
ushr v27.2d, v22.2d, #51
umulh x8, x14, x15
adds x22, x22, x2
and v22.16b, v22.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v28.2d, v23.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v23.16b, v23.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v29.2d, v24.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v24.16b, v24.16b, v5.16b
mul x4, x12, x12
umulh x2, x12, x12
add v21.2d, v21.2d, v25.2d
mul x8, x13, x13
umulh x9, x13, x13
add v22.2d, v22.2d, v26.2d
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v27.2d
mul x3, x15, x15
umulh x11, x15, x15
add v24.2d, v24.2d, v28.2d
adds x5, x5, x2
adcs x6, x6, x8
add v20.2d, v20.2d, v29.2d
adcs x7, x7, x9
adcs x21, x21, x16
shl v0.2d, v29.2d, #1
adcs x22, x22, x17
adcs x23, x23, x3
shl v2.2d, v29.2d, #4
adc x24, x24, x11
add v20.2d, v20.2d, v0.2d
movz w11, #38, lsl #0
mul x2, x11, x21
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
mul x8, x11, x22
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
mul x9, x11, x23
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
str q0, [x0, #1024]
adcs x7, x7, x16
adc x20, x10, x10
str q1, [x0, #1072]
umulh x2, x11, x21
umulh x8, x11, x22
trn1 v0.2d, v22.2d, v23.2d
umulh x9, x11, x23
umulh x16, x11, x24
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x9
adc x20, x20, x16
str q0, [x0, #1040]
adds x16, x7, x7
adc x9, x20, x20
str q1, [x0, #1088]
lsr x7, x16, #1
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
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
.globl lab_xh
lab_xh:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #272]
ldr q30, [x0, #736]
ldr x3, [x0, #288]
mul x4, x3, x12
ldr q20, [x0, #224]
mul x5, x3, x13
mul x6, x3, x14
ldr q21, [x0, #256]
mul x7, x3, x15
umulh x2, x3, x12
ldr q22, [x0, #240]
umulh x8, x3, x13
umulh x9, x3, x14
ldr q23, [x0, #272]
umulh x16, x3, x15
adds x5, x5, x2
trn1 v24.2d, v20.2d, v21.2d
adcs x6, x6, x8
adcs x7, x7, x9
trn2 v25.2d, v20.2d, v21.2d
adc x21, x16, x10
ldr x3, [x0, #296]
trn1 v26.2d, v22.2d, v23.2d
mul x2, x3, x12
mul x8, x3, x13
trn2 v27.2d, v22.2d, v23.2d
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v24.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v24.2d, #26
adcs x7, x7, x9
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
umulh x16, x3, x15
sri v20.2d, v24.2d, #51
adds x6, x6, x2
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
adc x22, x22, x16
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #304]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v25.2d, #38
adcs x7, x7, x8
adcs x21, x21, x9
and v21.16b, v26.16b, v30.16b
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v2.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v26.2d, #25
umulh x9, x3, x14
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x7, x7, x2
adcs x21, x21, x8
shl v21.2d, v27.2d, #13
adcs x22, x22, x9
adc x23, x23, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #312]
mul x2, x3, x12
and v21.16b, v21.16b, v30.16b
mul x8, x3, x13
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x7, x7, x2
adcs x21, x21, x8
and v20.16b, v20.16b, v31.16b
adcs x22, x22, x9
adcs x23, x23, x16
ushr v21.2d, v27.2d, #38
adc x24, x10, x10
umulh x2, x3, x12
uzp1 v4.4s, v20.4s, v21.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v10.4s, v0.4s, v0.4s
umulh x16, x3, x15
adds x21, x21, x2
add v11.4s, v1.4s, v1.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v12.4s, v2.4s, v2.4s
adc x24, x24, x16
movz w11, #38, lsl #0
add v13.4s, v3.4s, v3.4s
mul x2, x11, x21
adds x4, x4, x2
add v14.4s, v4.4s, v4.4s
mul x8, x11, x22
adcs x5, x5, x8
ext v5.16b, v10.16b, v10.16b, #8
mul x9, x11, x23
adcs x6, x6, x9
ext v6.16b, v11.16b, v11.16b, #8
mul x16, x11, x24
adcs x7, x7, x16
ext v7.16b, v12.16b, v12.16b, #8
adc x20, x10, x10
umulh x2, x11, x21
ext v8.16b, v13.16b, v13.16b, #8
umulh x8, x11, x22
umulh x9, x11, x23
ext v9.16b, v14.16b, v14.16b, #8
umulh x16, x11, x24
adds x7, x7, x9
ldr q31, [x0, #752]
adc x20, x20, x16
mul v15.4s, v0.4s, v31.4s
adds x16, x7, x7
adc x9, x20, x20
mul v16.4s, v1.4s, v31.4s
lsr x7, x16, #1
movz w11, #19, lsl #0
mul v17.4s, v2.4s, v31.4s
mul x9, x9, x11
adds x4, x4, x9
mul v18.4s, v3.4s, v31.4s
adcs x5, x5, x2
adcs x6, x6, x8
mul v19.4s, v4.4s, v31.4s
adc x7, x7, x10
stp x4, x5, [x0, #480]
umull2 v20.2d, v10.4s, v19.4s
stp x6, x7, [x0, #496]
ldp x12, x13, [x0, #224]
umlal2 v20.2d, v11.4s, v18.4s
ldp x14, x15, [x0, #240]
ldr x3, [x0, #320]
umlal2 v20.2d, v2.4s, v17.4s
mul x4, x3, x12
mul x5, x3, x13
add v20.2d, v20.2d, v20.2d
mul x6, x3, x14
mul x7, x3, x15
umlal v20.2d, v0.2s, v0.2s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v20.2d, v12.2s, v18.2s
adds x5, x5, x2
adcs x6, x6, x8
umull v25.2d, v5.2s, v0.2s
adcs x7, x7, x9
adc x21, x16, x10
umlal v25.2d, v6.2s, v19.2s
ldr x3, [x0, #328]
umlal2 v25.2d, v6.4s, v19.4s
mul x2, x3, x12
mul x8, x3, x13
umlal v25.2d, v7.2s, v18.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v25.2d, v7.4s, v18.4s
adds x5, x5, x2
adcs x6, x6, x8
umull2 v21.2d, v0.4s, v0.4s
adcs x7, x7, x9
adcs x21, x21, x16
umlal2 v21.2d, v11.4s, v19.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v21.2d, v21.2d, v21.2d
umulh x16, x3, x15
adds x6, x6, x2
umlal v21.2d, v10.2s, v1.2s
adcs x7, x7, x8
adcs x21, x21, x9
umlal v21.2d, v12.2s, v19.2s
adc x22, x22, x16
ldr x3, [x0, #336]
umlal v21.2d, v3.2s, v18.2s
mul x2, x3, x12
mul x8, x3, x13
umull v26.2d, v5.2s, v1.2s
mul x9, x3, x14
mul x16, x3, x15
umlal2 v26.2d, v5.4s, v1.4s
adds x6, x6, x2
adcs x7, x7, x8
umlal v26.2d, v7.2s, v19.2s
adcs x21, x21, x9
adcs x22, x22, x16
umlal2 v26.2d, v7.4s, v19.4s
adc x23, x10, x10
umlal v26.2d, v8.2s, v18.2s
umulh x2, x3, x12
umulh x8, x3, x13
umull2 v22.2d, v10.4s, v1.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v22.2d, v12.4s, v19.4s
adds x7, x7, x2
adcs x21, x21, x8
umlal2 v22.2d, v3.4s, v18.4s
adcs x22, x22, x9
adc x23, x23, x16
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #344]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
mul x9, x3, x14
umlal v22.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x7, x7, x2
umlal v22.2d, v13.2s, v19.2s
adcs x21, x21, x8
adcs x22, x22, x9
umull v27.2d, v5.2s, v2.2s
adcs x23, x23, x16
adc x24, x10, x10
umlal2 v27.2d, v5.4s, v2.4s
umulh x2, x3, x12
umulh x8, x3, x13
umlal v27.2d, v6.2s, v1.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v8.2s, v19.2s
adds x21, x21, x2
adcs x22, x22, x8
umlal2 v27.2d, v8.4s, v19.4s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v23.2d, v10.4s, v2.4s
movz w11, #38, lsl #0
mul x2, x11, x21
umlal2 v23.2d, v1.4s, v1.4s
adds x4, x4, x2
umlal2 v23.2d, v13.4s, v19.4s
mul x8, x11, x22
adcs x5, x5, x8
add v23.2d, v23.2d, v23.2d
mul x9, x11, x23
adcs x6, x6, x9
umlal v23.2d, v10.2s, v3.2s
mul x16, x11, x24
adcs x7, x7, x16
umlal v23.2d, v11.2s, v2.2s
adc x20, x10, x10
umulh x2, x11, x21
umlal v23.2d, v4.2s, v19.2s
umulh x8, x11, x22
umulh x9, x11, x23
umull v28.2d, v5.2s, v3.2s
umulh x16, x11, x24
adds x7, x7, x9
umlal2 v28.2d, v5.4s, v3.4s
adc x20, x20, x16
adds x16, x7, x7
umlal v28.2d, v6.2s, v2.2s
adc x9, x20, x20
lsr x7, x16, #1
umlal2 v28.2d, v6.4s, v2.4s
movz w11, #19, lsl #0
mul x9, x9, x11
umlal v28.2d, v9.2s, v19.2s
adds x4, x4, x9
adcs x5, x5, x2
umull2 v24.2d, v10.4s, v3.4s
adcs x6, x6, x8
adc x7, x7, x10
umlal2 v24.2d, v11.4s, v2.4s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal2 v24.2d, v4.4s, v19.4s
ldp x4, x5, [x0, #448]
ldp x6, x7, [x0, #464]
add v24.2d, v24.2d, v24.2d
ldp x21, x22, [x0, #480]
umlal v24.2d, v10.2s, v4.2s
ldp x23, x24, [x0, #496]
subs x12, x4, x21
umlal v24.2d, v11.2s, v3.2s
sbcs x13, x5, x22
movz w2, #38, lsl #0
umlal v24.2d, v2.2s, v2.2s
sbcs x14, x6, x23
sbcs x15, x7, x24
umull v29.2d, v5.2s, v4.2s
csel x3, x10, x2, hs
subs x12, x12, x3
umlal2 v29.2d, v5.4s, v4.4s
sbcs x13, x13, x10
sbcs x14, x14, x10
umlal v29.2d, v6.2s, v3.2s
sbc x15, x15, x10
mul x5, x12, x13
umlal2 v29.2d, v6.4s, v3.4s
mul x6, x12, x14
mul x7, x12, x15
umlal v29.2d, v7.2s, v2.2s
umulh x2, x12, x13
umulh x8, x12, x14
ldr q3, [x0, #720]
umulh x9, x12, x15
adds x6, x6, x2
ldr q4, [x0, #736]
adcs x7, x7, x8
adc x21, x9, x10
ushr v2.2d, v29.2d, #25
mul x2, x13, x14
mul x8, x13, x15
and v29.16b, v29.16b, v4.16b
umulh x9, x13, x14
umulh x16, x13, x15
ushr v0.2d, v24.2d, #26
adds x7, x7, x2
adcs x21, x21, x8
and v24.16b, v24.16b, v3.16b
adc x22, x16, x10
adds x21, x21, x9
add v29.2d, v29.2d, v0.2d
adc x22, x22, x10
ushr v1.2d, v28.2d, #25
mul x2, x14, x15
umulh x8, x14, x15
and v28.16b, v28.16b, v4.16b
adds x22, x22, x2
adc x23, x8, x10
add v24.2d, v24.2d, v1.2d
adds x5, x5, x5
adcs x6, x6, x6
ushr v0.2d, v23.2d, #26
adcs x7, x7, x7
adcs x21, x21, x21
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x22
adcs x23, x23, x23
add v28.2d, v28.2d, v0.2d
adc x24, x10, x10
mul x4, x12, x12
ushr v1.2d, v27.2d, #25
umulh x2, x12, x12
mul x8, x13, x13
and v27.16b, v27.16b, v4.16b
umulh x9, x13, x13
mul x16, x14, x14
add v23.2d, v23.2d, v1.2d
umulh x17, x14, x14
mul x3, x15, x15
ushr v0.2d, v22.2d, #26
umulh x11, x15, x15
adds x5, x5, x2
and v22.16b, v22.16b, v3.16b
adcs x6, x6, x8
adcs x7, x7, x9
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x16
adcs x22, x22, x17
ushr v1.2d, v26.2d, #25
adcs x23, x23, x3
adc x24, x24, x11
and v26.16b, v26.16b, v4.16b
movz w11, #38, lsl #0
add v22.2d, v22.2d, v1.2d
mul x2, x11, x21
adds x4, x4, x2
ushr v0.2d, v21.2d, #26
mul x8, x11, x22
adcs x5, x5, x8
and v21.16b, v21.16b, v3.16b
mul x9, x11, x23
adcs x6, x6, x9
add v26.2d, v26.2d, v0.2d
mul x16, x11, x24
adcs x7, x7, x16
ushr v1.2d, v25.2d, #25
adc x20, x10, x10
umulh x2, x11, x21
and v25.16b, v25.16b, v4.16b
umulh x8, x11, x22
umulh x9, x11, x23
add v21.2d, v21.2d, v1.2d
umulh x16, x11, x24
adds x7, x7, x9
ushr v0.2d, v20.2d, #26
adc x20, x20, x16
adds x16, x7, x7
and v20.16b, v20.16b, v3.16b
adc x9, x20, x20
lsr x7, x16, #1
add v25.2d, v25.2d, v0.2d
movz w11, #19, lsl #0
mul x9, x9, x11
add v20.2d, v20.2d, v2.2d
adds x4, x4, x9
adcs x5, x5, x2
shl v0.2d, v2.2d, #1
adcs x6, x6, x8
adc x7, x7, x10
shl v2.2d, v2.2d, #4
stp x4, x5, [x0, #192]
stp x6, x7, [x0, #208]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
shl v25.2d, v25.2d, #26
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v20.2d, v20.2d, v25.2d
adcs x13, x5, x22
movz w2, #38, lsl #0
shl v26.2d, v26.2d, #26
adcs x14, x6, x23
adcs x15, x7, x24
add v21.2d, v21.2d, v26.2d
csel x3, x2, x10, hs
adds x12, x12, x3
shl v27.2d, v27.2d, #26
adcs x13, x13, x10
adc x14, x14, x10
add v22.2d, v22.2d, v27.2d
mul x5, x12, x13
mul x6, x12, x14
shl v28.2d, v28.2d, #26
mul x7, x12, x15
umulh x2, x12, x13
add v23.2d, v23.2d, v28.2d
umulh x8, x12, x14
umulh x9, x12, x15
shl v29.2d, v29.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v24.2d, v24.2d, v29.2d
adc x21, x9, x10
mul x2, x13, x14
ldr q5, [x0, #704]
mul x8, x13, x15
umulh x9, x13, x14
ushr v25.2d, v20.2d, #51
umulh x16, x13, x15
adds x7, x7, x2
and v20.16b, v20.16b, v5.16b
adcs x21, x21, x8
adc x22, x16, x10
ushr v26.2d, v21.2d, #51
adds x21, x21, x9
and v21.16b, v21.16b, v5.16b
adc x22, x22, x10
mul x2, x14, x15
ushr v27.2d, v22.2d, #51
umulh x8, x14, x15
adds x22, x22, x2
and v22.16b, v22.16b, v5.16b
adc x23, x8, x10
adds x5, x5, x5
ushr v28.2d, v23.2d, #51
adcs x6, x6, x6
adcs x7, x7, x7
and v23.16b, v23.16b, v5.16b
adcs x21, x21, x21
adcs x22, x22, x22
ushr v29.2d, v24.2d, #51
adcs x23, x23, x23
adc x24, x10, x10
and v24.16b, v24.16b, v5.16b
mul x4, x12, x12
umulh x2, x12, x12
add v21.2d, v21.2d, v25.2d
mul x8, x13, x13
umulh x9, x13, x13
add v22.2d, v22.2d, v26.2d
mul x16, x14, x14
umulh x17, x14, x14
add v23.2d, v23.2d, v27.2d
mul x3, x15, x15
umulh x11, x15, x15
add v24.2d, v24.2d, v28.2d
adds x5, x5, x2
adcs x6, x6, x8
add v20.2d, v20.2d, v29.2d
adcs x7, x7, x9
adcs x21, x21, x16
shl v0.2d, v29.2d, #1
adcs x22, x22, x17
adcs x23, x23, x3
shl v2.2d, v29.2d, #4
adc x24, x24, x11
add v20.2d, v20.2d, v0.2d
movz w11, #38, lsl #0
mul x2, x11, x21
add v20.2d, v20.2d, v2.2d
adds x4, x4, x2
mul x8, x11, x22
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
mul x9, x11, x23
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
mul x16, x11, x24
str q0, [x0, #1024]
adcs x7, x7, x16
adc x20, x10, x10
str q1, [x0, #1072]
umulh x2, x11, x21
umulh x8, x11, x22
trn1 v0.2d, v22.2d, v23.2d
umulh x9, x11, x23
umulh x16, x11, x24
trn2 v1.2d, v22.2d, v23.2d
adds x7, x7, x9
adc x20, x20, x16
str q0, [x0, #1040]
adds x16, x7, x7
adc x9, x20, x20
str q1, [x0, #1088]
lsr x7, x16, #1
movz w11, #19, lsl #0
trn1 v0.2d, v24.2d, v24.2d
mul x9, x9, x11
adds x4, x4, x9
trn2 v1.2d, v24.2d, v24.2d
adcs x5, x5, x2
adcs x6, x6, x8
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
fn lab_ue(p: *mut u64, n: u64);fn lab_xe(p: *mut u64, n: u64);fn lab_xE(p: *mut u64, n: u64);fn lab_xc(p: *mut u64, n: u64);fn lab_xi(p: *mut u64, n: u64);fn lab_xf(p: *mut u64, n: u64);fn lab_xg(p: *mut u64, n: u64);fn lab_xh(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_ue"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ue(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xe"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xe(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xE"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xE(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xc"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xc(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xi"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xi(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xf"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xf(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xg"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xg(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_xh"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_xh(p, 100) })); g.finish();
}