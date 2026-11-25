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
.globl lab_ta
lab_ta:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tb
lab_tb:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
adc x7, x7, x10
str q0, [x0, #1056]
stp x4, x5, [x0, #192]
str q1, [x0, #1104]
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
.globl lab_tc
lab_tc:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
adc x7, x7, x10
str q0, [x0, #1056]
stp x4, x5, [x0, #192]
str q1, [x0, #1104]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_td
lab_td:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
adc x7, x7, x10
str q0, [x0, #1056]
stp x4, x5, [x0, #192]
str q1, [x0, #1104]
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
.globl lab_te
lab_te:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
.globl lab_tf
lab_tf:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tg
lab_tg:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
and v20.16b, v20.16b, v31.16b
adcs x6, x6, x8
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
uzp1 v1.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
uzp1 v4.4s, v20.4s, v21.4s
adc x23, x10, x10
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
ext v7.16b, v2.16b, v2.16b, #8
umulh x16, x3, x15
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
add v10.4s, v0.4s, v0.4s
adc x23, x23, x16
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
mul v19.4s, v4.4s, v31.4s
umulh x9, x3, x14
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
umlal2 v20.2d, v2.4s, v17.4s
adcs x23, x23, x9
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
umlal v20.2d, v11.2s, v19.2s
mul x9, x27, x23
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umull v25.2d, v30.2s, v0.2s
umulh x23, x27, x23
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
umlal2 v25.2d, v30.4s, v19.4s
adcs x6, x6, x9
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
umull2 v21.2d, v0.4s, v0.4s
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
add v21.2d, v21.2d, v21.2d
adcs x5, x5, x21
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
umlal v21.2d, v3.2s, v18.2s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
umlal2 v26.2d, v30.4s, v1.4s
mul x4, x3, x12
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umlal2 v26.2d, v30.4s, v19.4s
umulh x2, x3, x12
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
umull2 v22.2d, v10.4s, v1.4s
adds x5, x5, x2
umlal2 v22.2d, v12.4s, v19.4s
adcs x6, x6, x8
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
umlal v22.2d, v10.2s, v2.2s
mul x2, x3, x12
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
add v30.4s, v5.4s, v5.4s
adds x5, x5, x2
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
add v30.4s, v6.4s, v6.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v27.2d, v30.2s, v19.2s
umulh x16, x3, x15
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
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
umlal v23.2d, v11.2s, v2.2s
mul x16, x3, x15
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
add v30.4s, v5.4s, v5.4s
adcs x21, x21, x9
umull v28.2d, v30.2s, v3.2s
adcs x22, x22, x16
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umlal v28.2d, v30.2s, v2.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
umlal v28.2d, v30.2s, v19.2s
adcs x22, x22, x9
umull2 v24.2d, v10.4s, v3.4s
adc x23, x23, x16
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
umlal2 v24.2d, v4.4s, v19.4s
mul x8, x3, x13
add v24.2d, v24.2d, v24.2d
mul x9, x3, x14
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
umlal v24.2d, v11.2s, v3.2s
adcs x21, x21, x8
umlal v24.2d, v2.2s, v2.2s
adcs x22, x22, x9
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umull v29.2d, v30.2s, v4.2s
umulh x2, x3, x12
umlal2 v29.2d, v30.4s, v4.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v29.2d, v30.2s, v3.2s
adds x21, x21, x2
umlal2 v29.2d, v30.4s, v3.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
ldr q3, [x0, #720]
mul x8, x27, x22
ldr q4, [x0, #736]
mul x9, x27, x23
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
and v29.16b, v29.16b, v4.16b
umulh x22, x27, x22
ushr v0.2d, v24.2d, #26
umulh x23, x27, x23
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
add v29.2d, v29.2d, v0.2d
adcs x5, x5, x8
ushr v1.2d, v28.2d, #25
adcs x6, x6, x9
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
add v24.2d, v24.2d, v1.2d
adds x7, x7, x23
ushr v0.2d, v23.2d, #26
adc x24, x24, x10
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
add v28.2d, v28.2d, v0.2d
mul x17, x17, x26
ushr v1.2d, v27.2d, #25
adds x4, x4, x17
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
add v23.2d, v23.2d, v1.2d
adc x7, x7, x10
ushr v0.2d, v22.2d, #26
stp x4, x5, [x0, #480]
and v22.16b, v22.16b, v3.16b
stp x6, x7, [x0, #496]
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ushr v1.2d, v26.2d, #25
ldp x21, x22, [x0, #480]
and v26.16b, v26.16b, v4.16b
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v22.2d, v22.2d, v1.2d
adcs x13, x5, x22
ushr v0.2d, v21.2d, #26
adcs x14, x6, x23
and v21.16b, v21.16b, v3.16b
adcs x15, x7, x24
csel x3, x27, x10, hs
add v26.2d, v26.2d, v0.2d
adds x12, x12, x3
ushr v1.2d, v25.2d, #25
adcs x13, x13, x10
and v25.16b, v25.16b, v4.16b
adc x14, x14, x10
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
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
adc x22, x11, x10
shl v27.2d, v27.2d, #26
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
lsr x24, x23, #63
add v23.2d, v23.2d, v28.2d
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
extr x7, x7, x6, #63
ldr q5, [x0, #704]
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
adc x24, x24, x11
add v23.2d, v23.2d, v27.2d
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
mul x16, x27, x24
shl v0.2d, v29.2d, #1
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_th
lab_th:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
and v20.16b, v20.16b, v31.16b
adcs x6, x6, x8
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
uzp1 v1.4s, v20.4s, v21.4s
umulh x2, x3, x12
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
uzp1 v4.4s, v20.4s, v21.4s
adc x23, x10, x10
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
ext v7.16b, v2.16b, v2.16b, #8
umulh x16, x3, x15
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
add v10.4s, v0.4s, v0.4s
adc x23, x23, x16
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
mul v19.4s, v4.4s, v31.4s
umulh x9, x3, x14
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
umlal2 v20.2d, v2.4s, v17.4s
adcs x23, x23, x9
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
umlal v20.2d, v11.2s, v19.2s
mul x9, x27, x23
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umull v25.2d, v30.2s, v0.2s
umulh x23, x27, x23
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
umlal2 v25.2d, v30.4s, v19.4s
adcs x6, x6, x9
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
umull2 v21.2d, v0.4s, v0.4s
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
add v21.2d, v21.2d, v21.2d
adcs x5, x5, x21
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
umlal v21.2d, v3.2s, v18.2s
stp x6, x7, [x0, #464]
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
umlal2 v26.2d, v30.4s, v1.4s
mul x4, x3, x12
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umlal2 v26.2d, v30.4s, v19.4s
umulh x2, x3, x12
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
umull2 v22.2d, v10.4s, v1.4s
adds x5, x5, x2
umlal2 v22.2d, v12.4s, v19.4s
adcs x6, x6, x8
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
umlal v22.2d, v10.2s, v2.2s
mul x2, x3, x12
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
add v30.4s, v5.4s, v5.4s
adds x5, x5, x2
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
add v30.4s, v6.4s, v6.4s
adc x22, x10, x10
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v27.2d, v30.2s, v19.2s
umulh x16, x3, x15
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
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
umlal v23.2d, v11.2s, v2.2s
mul x16, x3, x15
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
add v30.4s, v5.4s, v5.4s
adcs x21, x21, x9
umull v28.2d, v30.2s, v3.2s
adcs x22, x22, x16
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umlal v28.2d, v30.2s, v2.2s
umulh x9, x3, x14
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
umlal v28.2d, v30.2s, v19.2s
adcs x22, x22, x9
umull2 v24.2d, v10.4s, v3.4s
adc x23, x23, x16
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
umlal2 v24.2d, v4.4s, v19.4s
mul x8, x3, x13
add v24.2d, v24.2d, v24.2d
mul x9, x3, x14
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
umlal v24.2d, v11.2s, v3.2s
adcs x21, x21, x8
umlal v24.2d, v2.2s, v2.2s
adcs x22, x22, x9
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umull v29.2d, v30.2s, v4.2s
umulh x2, x3, x12
umlal2 v29.2d, v30.4s, v4.4s
umulh x8, x3, x13
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v29.2d, v30.2s, v3.2s
adds x21, x21, x2
umlal2 v29.2d, v30.4s, v3.4s
adcs x22, x22, x8
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
ldr q3, [x0, #720]
mul x8, x27, x22
ldr q4, [x0, #736]
mul x9, x27, x23
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
and v29.16b, v29.16b, v4.16b
umulh x22, x27, x22
ushr v0.2d, v24.2d, #26
umulh x23, x27, x23
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
add v29.2d, v29.2d, v0.2d
adcs x5, x5, x8
ushr v1.2d, v28.2d, #25
adcs x6, x6, x9
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
add v24.2d, v24.2d, v1.2d
adds x7, x7, x23
ushr v0.2d, v23.2d, #26
adc x24, x24, x10
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
add v28.2d, v28.2d, v0.2d
mul x17, x17, x26
ushr v1.2d, v27.2d, #25
adds x4, x4, x17
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
add v23.2d, v23.2d, v1.2d
adc x7, x7, x10
ushr v0.2d, v22.2d, #26
stp x4, x5, [x0, #480]
and v22.16b, v22.16b, v3.16b
stp x6, x7, [x0, #496]
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ushr v1.2d, v26.2d, #25
ldp x21, x22, [x0, #480]
and v26.16b, v26.16b, v4.16b
ldp x23, x24, [x0, #496]
adds x12, x4, x21
add v22.2d, v22.2d, v1.2d
adcs x13, x5, x22
ushr v0.2d, v21.2d, #26
adcs x14, x6, x23
and v21.16b, v21.16b, v3.16b
adcs x15, x7, x24
csel x3, x27, x10, hs
add v26.2d, v26.2d, v0.2d
adds x12, x12, x3
ushr v1.2d, v25.2d, #25
adcs x13, x13, x10
and v25.16b, v25.16b, v4.16b
adc x14, x14, x10
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
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
adc x22, x11, x10
shl v27.2d, v27.2d, #26
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
lsr x24, x23, #63
add v23.2d, v23.2d, v28.2d
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
extr x7, x7, x6, #63
ldr q5, [x0, #704]
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
adc x24, x24, x11
add v23.2d, v23.2d, v27.2d
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
mul x16, x27, x24
shl v0.2d, v29.2d, #1
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_ti
lab_ti:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
.globl lab_tj
lab_tj:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
lsr x24, x23, #63
extr x23, x23, x22, #63
shl v29.2d, v29.2d, #26
extr x22, x22, x21, #63
add v24.2d, v24.2d, v29.2d
extr x21, x21, x7, #63
ldr q5, [x0, #704]
extr x7, x7, x6, #63
extr x6, x6, x5, #63
ushr v25.2d, v20.2d, #51
lsl x5, x5, #1
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_ta32
lab_ta32:
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
trn2 v27.2d, v22.2d, v23.2d
umulh x8, x3, x13
and v20.16b, v24.16b, v31.16b
umulh x9, x3, x14
ushr v21.2d, v24.2d, #26
umulh x16, x3, x15
and v21.16b, v21.16b, v30.16b
adds x5, x5, x2
uzp1 v0.4s, v20.4s, v21.4s
adcs x6, x6, x8
shl v20.2d, v25.2d, #13
adcs x7, x7, x9
sri v20.2d, v24.2d, #51
adc x21, x16, x10
and v20.16b, v20.16b, v31.16b
ushr v21.2d, v25.2d, #13
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
mul x8, x3, x13
ushr v20.2d, v25.2d, #38
mul x9, x3, x14
and v21.16b, v26.16b, v30.16b
mul x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x5, x5, x2
ushr v20.2d, v26.2d, #25
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
shl v21.2d, v27.2d, #13
adcs x7, x7, x9
sri v21.2d, v26.2d, #51
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
uzp1 v3.4s, v20.4s, v21.4s
umulh x2, x3, x12
ushr v20.2d, v27.2d, #12
umulh x8, x3, x13
and v20.16b, v20.16b, v31.16b
umulh x9, x3, x14
ushr v21.2d, v27.2d, #38
umulh x16, x3, x15
uzp1 v4.4s, v20.4s, v21.4s
ext v5.16b, v0.16b, v0.16b, #8
adds x6, x6, x2
ext v6.16b, v1.16b, v1.16b, #8
adcs x7, x7, x8
ext v7.16b, v2.16b, v2.16b, #8
adcs x21, x21, x9
ext v8.16b, v3.16b, v3.16b, #8
adc x22, x22, x16
ext v9.16b, v4.16b, v4.16b, #8
ldr x3, [x0, #336]
add v10.4s, v0.4s, v0.4s
mul x2, x3, x12
add v11.4s, v1.4s, v1.4s
mul x8, x3, x13
add v12.4s, v2.4s, v2.4s
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
add v14.4s, v4.4s, v4.4s
mul x16, x3, x15
ldr q31, [x0, #752]
adds x6, x6, x2
mul v15.4s, v0.4s, v31.4s
adcs x7, x7, x8
mul v16.4s, v1.4s, v31.4s
adcs x21, x21, x9
mul v17.4s, v2.4s, v31.4s
adcs x22, x22, x16
mul v18.4s, v3.4s, v31.4s
adc x23, x10, x10
mul v19.4s, v4.4s, v31.4s
umulh x2, x3, x12
umull2 v20.2d, v10.4s, v19.4s
umlal2 v20.2d, v11.4s, v18.4s
umulh x8, x3, x13
umlal2 v20.2d, v2.4s, v17.4s
umulh x9, x3, x14
add v20.2d, v20.2d, v20.2d
umulh x16, x3, x15
umlal v20.2d, v0.2s, v0.2s
adds x7, x7, x2
umlal v20.2d, v11.2s, v19.2s
adcs x21, x21, x8
umlal v20.2d, v12.2s, v18.2s
adcs x22, x22, x9
add v30.4s, v5.4s, v5.4s
adc x23, x23, x16
umull v25.2d, v30.2s, v0.2s
add v30.4s, v6.4s, v6.4s
ldr x3, [x0, #344]
umlal v25.2d, v30.2s, v19.2s
mul x2, x3, x12
umlal2 v25.2d, v30.4s, v19.4s
mul x8, x3, x13
add v30.4s, v7.4s, v7.4s
mul x9, x3, x14
umlal v25.2d, v30.2s, v18.2s
mul x16, x3, x15
umlal2 v25.2d, v30.4s, v18.4s
adds x7, x7, x2
umull2 v21.2d, v0.4s, v0.4s
adcs x21, x21, x8
umlal2 v21.2d, v11.4s, v19.4s
umlal2 v21.2d, v12.4s, v18.4s
adcs x22, x22, x9
add v21.2d, v21.2d, v21.2d
adcs x23, x23, x16
umlal v21.2d, v10.2s, v1.2s
adc x24, x10, x10
umlal v21.2d, v12.2s, v19.2s
umulh x2, x3, x12
umlal v21.2d, v3.2s, v18.2s
umulh x8, x3, x13
add v30.4s, v5.4s, v5.4s
umulh x9, x3, x14
umull v26.2d, v30.2s, v1.2s
umulh x16, x3, x15
umlal2 v26.2d, v30.4s, v1.4s
add v30.4s, v7.4s, v7.4s
adds x21, x21, x2
umlal v26.2d, v30.2s, v19.2s
adcs x22, x22, x8
umlal2 v26.2d, v30.4s, v19.4s
adcs x23, x23, x9
add v30.4s, v8.4s, v8.4s
adc x24, x24, x16
umlal v26.2d, v30.2s, v18.2s
mul x2, x27, x21
umull2 v22.2d, v10.4s, v1.4s
mul x8, x27, x22
umlal2 v22.2d, v12.4s, v19.4s
mul x9, x27, x23
umlal2 v22.2d, v3.4s, v18.4s
add v22.2d, v22.2d, v22.2d
mul x16, x27, x24
umlal v22.2d, v10.2s, v2.2s
umulh x21, x27, x21
umlal v22.2d, v1.2s, v1.2s
umulh x22, x27, x22
umlal v22.2d, v13.2s, v19.2s
umulh x23, x27, x23
add v30.4s, v5.4s, v5.4s
umulh x24, x27, x24
umull v27.2d, v30.2s, v2.2s
adds x4, x4, x2
umlal2 v27.2d, v30.4s, v2.4s
adcs x5, x5, x8
add v30.4s, v6.4s, v6.4s
adcs x6, x6, x9
umlal v27.2d, v30.2s, v1.2s
add v30.4s, v8.4s, v8.4s
adcs x7, x7, x16
umlal v27.2d, v30.2s, v19.2s
adc x24, x24, x10
umlal2 v27.2d, v30.4s, v19.4s
adds x7, x7, x23
umull2 v23.2d, v10.4s, v2.4s
adc x24, x24, x10
umlal2 v23.2d, v1.4s, v1.4s
extr x17, x24, x7, #63
umlal2 v23.2d, v13.4s, v19.4s
and x7, x7, #0x7fffffffffffffff
add v23.2d, v23.2d, v23.2d
mul x17, x17, x26
umlal v23.2d, v10.2s, v3.2s
umlal v23.2d, v11.2s, v2.2s
adds x4, x4, x17
umlal v23.2d, v4.2s, v19.2s
adcs x5, x5, x21
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x22
umull v28.2d, v30.2s, v3.2s
adc x7, x7, x10
umlal2 v28.2d, v30.4s, v3.4s
stp x4, x5, [x0, #448]
add v30.4s, v6.4s, v6.4s
stp x6, x7, [x0, #464]
umlal v28.2d, v30.2s, v2.2s
ldp x12, x13, [x0, #256]
umlal2 v28.2d, v30.4s, v2.4s
add v30.4s, v9.4s, v9.4s
ldp x14, x15, [x0, #272]
umlal v28.2d, v30.2s, v19.2s
ldr x3, [x0, #288]
umull2 v24.2d, v10.4s, v3.4s
mul x4, x3, x12
umlal2 v24.2d, v11.4s, v2.4s
mul x5, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x6, x3, x14
add v24.2d, v24.2d, v24.2d
mul x7, x3, x15
umlal v24.2d, v10.2s, v4.2s
umulh x2, x3, x12
umlal v24.2d, v11.2s, v3.2s
umlal v24.2d, v2.2s, v2.2s
umulh x8, x3, x13
add v30.4s, v5.4s, v5.4s
umulh x9, x3, x14
umull v29.2d, v30.2s, v4.2s
umulh x16, x3, x15
umlal2 v29.2d, v30.4s, v4.4s
adds x5, x5, x2
add v30.4s, v6.4s, v6.4s
adcs x6, x6, x8
umlal v29.2d, v30.2s, v3.2s
adcs x7, x7, x9
umlal2 v29.2d, v30.4s, v3.4s
adc x21, x16, x10
add v30.4s, v7.4s, v7.4s
umlal v29.2d, v30.2s, v2.2s
ldr x3, [x0, #296]
ldr q3, [x0, #720]
mul x2, x3, x12
ldr q4, [x0, #736]
mul x8, x3, x13
ushr v2.2d, v29.2d, #25
mul x9, x3, x14
and v29.16b, v29.16b, v4.16b
mul x16, x3, x15
ushr v0.2d, v24.2d, #26
adds x5, x5, x2
and v24.16b, v24.16b, v3.16b
adcs x6, x6, x8
add v29.2d, v29.2d, v0.2d
adcs x7, x7, x9
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
adcs x21, x21, x16
add v24.2d, v24.2d, v1.2d
adc x22, x10, x10
ushr v0.2d, v23.2d, #26
umulh x2, x3, x12
and v23.16b, v23.16b, v3.16b
umulh x8, x3, x13
add v28.2d, v28.2d, v0.2d
umulh x9, x3, x14
ushr v1.2d, v27.2d, #25
umulh x16, x3, x15
and v27.16b, v27.16b, v4.16b
adds x6, x6, x2
add v23.2d, v23.2d, v1.2d
ushr v0.2d, v22.2d, #26
adcs x7, x7, x8
and v22.16b, v22.16b, v3.16b
adcs x21, x21, x9
add v27.2d, v27.2d, v0.2d
adc x22, x22, x16
ushr v1.2d, v26.2d, #25
ldr x3, [x0, #304]
and v26.16b, v26.16b, v4.16b
mul x2, x3, x12
add v22.2d, v22.2d, v1.2d
mul x8, x3, x13
ushr v0.2d, v21.2d, #26
mul x9, x3, x14
and v21.16b, v21.16b, v3.16b
add v26.2d, v26.2d, v0.2d
mul x16, x3, x15
ushr v1.2d, v25.2d, #25
adds x6, x6, x2
and v25.16b, v25.16b, v4.16b
adcs x7, x7, x8
add v21.2d, v21.2d, v1.2d
adcs x21, x21, x9
ushr v0.2d, v20.2d, #26
adcs x22, x22, x16
and v20.16b, v20.16b, v3.16b
adc x23, x10, x10
add v25.2d, v25.2d, v0.2d
umulh x2, x3, x12
add v20.2d, v20.2d, v2.2d
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
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
ldr x3, [x0, #312]
add v22.2d, v22.2d, v27.2d
mul x2, x3, x12
shl v28.2d, v28.2d, #26
mul x8, x3, x13
add v23.2d, v23.2d, v28.2d
mul x9, x3, x14
shl v29.2d, v29.2d, #26
mul x16, x3, x15
add v24.2d, v24.2d, v29.2d
adds x7, x7, x2
ldr q5, [x0, #704]
adcs x21, x21, x8
ushr v25.2d, v20.2d, #51
and v20.16b, v20.16b, v5.16b
adcs x22, x22, x9
ushr v26.2d, v21.2d, #51
adcs x23, x23, x16
and v21.16b, v21.16b, v5.16b
adc x24, x10, x10
ushr v27.2d, v22.2d, #51
umulh x2, x3, x12
and v22.16b, v22.16b, v5.16b
umulh x8, x3, x13
ushr v28.2d, v23.2d, #51
umulh x9, x3, x14
and v23.16b, v23.16b, v5.16b
umulh x16, x3, x15
ushr v29.2d, v24.2d, #51
adds x21, x21, x2
and v24.16b, v24.16b, v5.16b
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x8
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x9
add v23.2d, v23.2d, v27.2d
adc x24, x24, x16
add v24.2d, v24.2d, v28.2d
mul x2, x27, x21
add v20.2d, v20.2d, v29.2d
mul x8, x27, x22
shl v0.2d, v29.2d, #1
mul x9, x27, x23
shl v2.2d, v29.2d, #4
mul x16, x27, x24
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
umulh x21, x27, x21
trn1 v0.2d, v20.2d, v21.2d
umulh x22, x27, x22
trn2 v1.2d, v20.2d, v21.2d
umulh x23, x27, x23
str q0, [x0, #1024]
umulh x24, x27, x24
str q1, [x0, #1072]
adds x4, x4, x2
trn1 v0.2d, v22.2d, v23.2d
adcs x5, x5, x8
trn2 v1.2d, v22.2d, v23.2d
adcs x6, x6, x9
str q0, [x0, #1040]
str q1, [x0, #1088]
adcs x7, x7, x16
trn1 v0.2d, v24.2d, v24.2d
adc x24, x24, x10
trn2 v1.2d, v24.2d, v24.2d
adds x7, x7, x23
str q0, [x0, #1056]
adc x24, x24, x10
str q1, [x0, #1104]
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
adds x4, x4, x17
adcs x5, x5, x21
adcs x6, x6, x22
adc x7, x7, x10
stp x4, x5, [x0, #480]
stp x6, x7, [x0, #496]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_ta43
lab_ta43:
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
mul x2, x3, x12
ushr v21.2d, v25.2d, #13
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v25.2d, #38
adds x5, x5, x2
and v21.16b, v26.16b, v30.16b
adcs x6, x6, x8
uzp1 v2.4s, v20.4s, v21.4s
adcs x7, x7, x9
ushr v20.2d, v26.2d, #25
adcs x21, x21, x16
and v20.16b, v20.16b, v31.16b
adc x22, x10, x10
shl v21.2d, v27.2d, #13
umulh x2, x3, x12
sri v21.2d, v26.2d, #51
umulh x8, x3, x13
and v21.16b, v21.16b, v30.16b
umulh x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
umulh x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x6, x6, x2
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x8
ushr v21.2d, v27.2d, #38
adcs x21, x21, x9
uzp1 v4.4s, v20.4s, v21.4s
adc x22, x22, x16
ext v5.16b, v0.16b, v0.16b, #8
ldr x3, [x0, #336]
ext v6.16b, v1.16b, v1.16b, #8
mul x2, x3, x12
ext v7.16b, v2.16b, v2.16b, #8
mul x8, x3, x13
ext v8.16b, v3.16b, v3.16b, #8
mul x9, x3, x14
ext v9.16b, v4.16b, v4.16b, #8
mul x16, x3, x15
add v10.4s, v0.4s, v0.4s
adds x6, x6, x2
add v11.4s, v1.4s, v1.4s
adcs x7, x7, x8
add v12.4s, v2.4s, v2.4s
adcs x21, x21, x9
add v13.4s, v3.4s, v3.4s
adcs x22, x22, x16
add v14.4s, v4.4s, v4.4s
adc x23, x10, x10
ldr q31, [x0, #752]
umulh x2, x3, x12
mul v15.4s, v0.4s, v31.4s
umulh x8, x3, x13
mul v16.4s, v1.4s, v31.4s
umulh x9, x3, x14
mul v17.4s, v2.4s, v31.4s
umulh x16, x3, x15
mul v18.4s, v3.4s, v31.4s
adds x7, x7, x2
mul v19.4s, v4.4s, v31.4s
adcs x21, x21, x8
umull2 v20.2d, v10.4s, v19.4s
adcs x22, x22, x9
umlal2 v20.2d, v11.4s, v18.4s
adc x23, x23, x16
umlal2 v20.2d, v2.4s, v17.4s
ldr x3, [x0, #344]
add v20.2d, v20.2d, v20.2d
mul x2, x3, x12
umlal v20.2d, v0.2s, v0.2s
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
umlal v25.2d, v30.2s, v18.2s
umulh x8, x3, x13
umlal2 v25.2d, v30.4s, v18.4s
umulh x9, x3, x14
umull2 v21.2d, v0.4s, v0.4s
umulh x16, x3, x15
umlal2 v21.2d, v11.4s, v19.4s
adds x21, x21, x2
umlal2 v21.2d, v12.4s, v18.4s
adcs x22, x22, x8
add v21.2d, v21.2d, v21.2d
adcs x23, x23, x9
umlal v21.2d, v10.2s, v1.2s
adc x24, x24, x16
umlal v21.2d, v12.2s, v19.2s
mul x2, x27, x21
umlal v21.2d, v3.2s, v18.2s
mul x8, x27, x22
add v30.4s, v5.4s, v5.4s
mul x9, x27, x23
umull v26.2d, v30.2s, v1.2s
mul x16, x27, x24
umlal2 v26.2d, v30.4s, v1.4s
umulh x21, x27, x21
add v30.4s, v7.4s, v7.4s
umulh x22, x27, x22
umlal v26.2d, v30.2s, v19.2s
umulh x23, x27, x23
umlal2 v26.2d, v30.4s, v19.4s
umulh x24, x27, x24
add v30.4s, v8.4s, v8.4s
adds x4, x4, x2
umlal v26.2d, v30.2s, v18.2s
adcs x5, x5, x8
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x9
umlal2 v22.2d, v12.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
adcs x7, x7, x16
add v22.2d, v22.2d, v22.2d
adc x24, x24, x10
umlal v22.2d, v10.2s, v2.2s
adds x7, x7, x23
umlal v22.2d, v1.2s, v1.2s
adc x24, x24, x10
umlal v22.2d, v13.2s, v19.2s
extr x17, x24, x7, #63
add v30.4s, v5.4s, v5.4s
and x7, x7, #0x7fffffffffffffff
umull v27.2d, v30.2s, v2.2s
mul x17, x17, x26
umlal2 v27.2d, v30.4s, v2.4s
adds x4, x4, x17
add v30.4s, v6.4s, v6.4s
adcs x5, x5, x21
umlal v27.2d, v30.2s, v1.2s
adcs x6, x6, x22
add v30.4s, v8.4s, v8.4s
adc x7, x7, x10
umlal v27.2d, v30.2s, v19.2s
stp x4, x5, [x0, #448]
umlal2 v27.2d, v30.4s, v19.4s
stp x6, x7, [x0, #464]
umull2 v23.2d, v10.4s, v2.4s
ldp x12, x13, [x0, #256]
umlal2 v23.2d, v1.4s, v1.4s
ldp x14, x15, [x0, #272]
umlal2 v23.2d, v13.4s, v19.4s
ldr x3, [x0, #288]
add v23.2d, v23.2d, v23.2d
mul x4, x3, x12
umlal v23.2d, v10.2s, v3.2s
mul x5, x3, x13
umlal v23.2d, v11.2s, v2.2s
mul x6, x3, x14
umlal v23.2d, v4.2s, v19.2s
mul x7, x3, x15
add v30.4s, v5.4s, v5.4s
umulh x2, x3, x12
umull v28.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v28.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v28.2d, v30.2s, v2.2s
adds x5, x5, x2
umlal2 v28.2d, v30.4s, v2.4s
adcs x6, x6, x8
add v30.4s, v9.4s, v9.4s
adcs x7, x7, x9
umlal v28.2d, v30.2s, v19.2s
adc x21, x16, x10
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #296]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
umlal2 v24.2d, v4.4s, v19.4s
mul x8, x3, x13
add v24.2d, v24.2d, v24.2d
mul x9, x3, x14
umlal v24.2d, v10.2s, v4.2s
mul x16, x3, x15
umlal v24.2d, v11.2s, v3.2s
adds x5, x5, x2
umlal v24.2d, v2.2s, v2.2s
adcs x6, x6, x8
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x9
umull v29.2d, v30.2s, v4.2s
adcs x21, x21, x16
umlal2 v29.2d, v30.4s, v4.4s
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v29.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v7.4s, v7.4s
umulh x16, x3, x15
umlal v29.2d, v30.2s, v2.2s
adds x6, x6, x2
ldr q3, [x0, #720]
adcs x7, x7, x8
ldr q4, [x0, #736]
adcs x21, x21, x9
ushr v2.2d, v29.2d, #25
adc x22, x22, x16
and v29.16b, v29.16b, v4.16b
ldr x3, [x0, #304]
ushr v0.2d, v24.2d, #26
mul x2, x3, x12
and v24.16b, v24.16b, v3.16b
mul x8, x3, x13
add v29.2d, v29.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v28.2d, #25
mul x16, x3, x15
and v28.16b, v28.16b, v4.16b
adds x6, x6, x2
add v24.2d, v24.2d, v1.2d
adcs x7, x7, x8
ushr v0.2d, v23.2d, #26
adcs x21, x21, x9
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x16
add v28.2d, v28.2d, v0.2d
adc x23, x10, x10
ushr v1.2d, v27.2d, #25
umulh x2, x3, x12
and v27.16b, v27.16b, v4.16b
umulh x8, x3, x13
add v23.2d, v23.2d, v1.2d
umulh x9, x3, x14
ushr v0.2d, v22.2d, #26
umulh x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x7, x7, x2
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x8
ushr v1.2d, v26.2d, #25
adcs x22, x22, x9
and v26.16b, v26.16b, v4.16b
adc x23, x23, x16
add v22.2d, v22.2d, v1.2d
ldr x3, [x0, #312]
ushr v0.2d, v21.2d, #26
mul x2, x3, x12
and v21.16b, v21.16b, v3.16b
mul x8, x3, x13
add v26.2d, v26.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v25.2d, #25
mul x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
adcs x21, x21, x8
ushr v0.2d, v20.2d, #26
adcs x22, x22, x9
and v20.16b, v20.16b, v3.16b
adcs x23, x23, x16
add v25.2d, v25.2d, v0.2d
adc x24, x10, x10
add v20.2d, v20.2d, v2.2d
umulh x2, x3, x12
shl v0.2d, v2.2d, #1
umulh x8, x3, x13
shl v2.2d, v2.2d, #4
umulh x9, x3, x14
add v20.2d, v20.2d, v0.2d
umulh x16, x3, x15
add v20.2d, v20.2d, v2.2d
adds x21, x21, x2
shl v25.2d, v25.2d, #26
adcs x22, x22, x8
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
adcs x23, x23, x9
add v21.2d, v21.2d, v26.2d
adc x24, x24, x16
shl v27.2d, v27.2d, #26
mul x2, x27, x21
add v22.2d, v22.2d, v27.2d
mul x8, x27, x22
shl v28.2d, v28.2d, #26
mul x9, x27, x23
add v23.2d, v23.2d, v28.2d
mul x16, x27, x24
shl v29.2d, v29.2d, #26
umulh x21, x27, x21
add v24.2d, v24.2d, v29.2d
umulh x22, x27, x22
ldr q5, [x0, #704]
umulh x23, x27, x23
ushr v25.2d, v20.2d, #51
umulh x24, x27, x24
and v20.16b, v20.16b, v5.16b
adds x4, x4, x2
ushr v26.2d, v21.2d, #51
adcs x5, x5, x8
and v21.16b, v21.16b, v5.16b
adcs x6, x6, x9
ushr v27.2d, v22.2d, #51
adcs x7, x7, x16
and v22.16b, v22.16b, v5.16b
adc x24, x24, x10
ushr v28.2d, v23.2d, #51
adds x7, x7, x23
and v23.16b, v23.16b, v5.16b
adc x24, x24, x10
ushr v29.2d, v24.2d, #51
extr x17, x24, x7, #63
and v24.16b, v24.16b, v5.16b
and x7, x7, #0x7fffffffffffffff
add v21.2d, v21.2d, v25.2d
mul x17, x17, x26
add v22.2d, v22.2d, v26.2d
adds x4, x4, x17
add v23.2d, v23.2d, v27.2d
adcs x5, x5, x21
add v24.2d, v24.2d, v28.2d
adcs x6, x6, x22
add v20.2d, v20.2d, v29.2d
adc x7, x7, x10
shl v0.2d, v29.2d, #1
stp x4, x5, [x0, #480]
shl v2.2d, v29.2d, #4
stp x6, x7, [x0, #496]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
trn1 v0.2d, v20.2d, v21.2d
ldp x21, x22, [x0, #480]
trn2 v1.2d, v20.2d, v21.2d
ldp x23, x24, [x0, #496]
str q0, [x0, #1024]
subs x12, x4, x21
str q1, [x0, #1072]
sbcs x13, x5, x22
trn1 v0.2d, v22.2d, v23.2d
sbcs x14, x6, x23
trn2 v1.2d, v22.2d, v23.2d
sbcs x15, x7, x24
str q0, [x0, #1040]
csel x3, x10, x27, hs
str q1, [x0, #1088]
subs x12, x12, x3
trn1 v0.2d, v24.2d, v24.2d
sbcs x13, x13, x10
trn2 v1.2d, v24.2d, v24.2d
sbcs x14, x14, x10
str q0, [x0, #1056]
sbc x15, x15, x10
str q1, [x0, #1104]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_ta2
lab_ta2:
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
ldr q31, [x0, #720]
ldr q30, [x0, #736]
ldp x14, x15, [x0, #240]
ldr q20, [x0, #224]
ldr q21, [x0, #256]
ldr x3, [x0, #320]
ldr q22, [x0, #240]
mul x4, x3, x12
ldr q23, [x0, #272]
trn1 v24.2d, v20.2d, v21.2d
mul x5, x3, x13
trn2 v25.2d, v20.2d, v21.2d
mul x6, x3, x14
trn1 v26.2d, v22.2d, v23.2d
trn2 v27.2d, v22.2d, v23.2d
mul x7, x3, x15
and v20.16b, v24.16b, v31.16b
umulh x2, x3, x12
ushr v21.2d, v24.2d, #26
and v21.16b, v21.16b, v30.16b
umulh x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
umulh x9, x3, x14
shl v20.2d, v25.2d, #13
sri v20.2d, v24.2d, #51
umulh x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x5, x5, x2
ushr v21.2d, v25.2d, #13
and v21.16b, v21.16b, v30.16b
adcs x6, x6, x8
uzp1 v1.4s, v20.4s, v21.4s
adcs x7, x7, x9
ushr v20.2d, v25.2d, #38
and v21.16b, v26.16b, v30.16b
adc x21, x16, x10
uzp1 v2.4s, v20.4s, v21.4s
ldr x3, [x0, #328]
ushr v20.2d, v26.2d, #25
and v20.16b, v20.16b, v31.16b
mul x2, x3, x12
shl v21.2d, v27.2d, #13
mul x8, x3, x13
sri v21.2d, v26.2d, #51
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v27.2d, #12
and v20.16b, v20.16b, v31.16b
adds x5, x5, x2
ushr v21.2d, v27.2d, #38
adcs x6, x6, x8
uzp1 v4.4s, v20.4s, v21.4s
ext v5.16b, v0.16b, v0.16b, #8
adcs x7, x7, x9
ext v6.16b, v1.16b, v1.16b, #8
adcs x21, x21, x16
ext v7.16b, v2.16b, v2.16b, #8
ext v8.16b, v3.16b, v3.16b, #8
adc x22, x10, x10
ext v9.16b, v4.16b, v4.16b, #8
umulh x2, x3, x12
add v10.4s, v0.4s, v0.4s
add v11.4s, v1.4s, v1.4s
umulh x8, x3, x13
add v12.4s, v2.4s, v2.4s
add v13.4s, v3.4s, v3.4s
umulh x9, x3, x14
add v14.4s, v4.4s, v4.4s
umulh x16, x3, x15
ldr q31, [x0, #752]
mul v15.4s, v0.4s, v31.4s
adds x6, x6, x2
mul v16.4s, v1.4s, v31.4s
adcs x7, x7, x8
mul v17.4s, v2.4s, v31.4s
mul v18.4s, v3.4s, v31.4s
adcs x21, x21, x9
mul v19.4s, v4.4s, v31.4s
adc x22, x22, x16
umull2 v20.2d, v10.4s, v19.4s
umlal2 v20.2d, v11.4s, v18.4s
ldr x3, [x0, #336]
umlal2 v20.2d, v2.4s, v17.4s
mul x2, x3, x12
add v20.2d, v20.2d, v20.2d
umlal v20.2d, v0.2s, v0.2s
mul x8, x3, x13
umlal v20.2d, v11.2s, v19.2s
mul x9, x3, x14
umlal v20.2d, v12.2s, v18.2s
add v30.4s, v5.4s, v5.4s
mul x16, x3, x15
umull v25.2d, v30.2s, v0.2s
adds x6, x6, x2
add v30.4s, v6.4s, v6.4s
umlal v25.2d, v30.2s, v19.2s
adcs x7, x7, x8
umlal2 v25.2d, v30.4s, v19.4s
adcs x21, x21, x9
add v30.4s, v7.4s, v7.4s
umlal v25.2d, v30.2s, v18.2s
adcs x22, x22, x16
umlal2 v25.2d, v30.4s, v18.4s
adc x23, x10, x10
umull2 v21.2d, v0.4s, v0.4s
umlal2 v21.2d, v11.4s, v19.4s
umulh x2, x3, x12
umlal2 v21.2d, v12.4s, v18.4s
umulh x8, x3, x13
add v21.2d, v21.2d, v21.2d
umlal v21.2d, v10.2s, v1.2s
umulh x9, x3, x14
umlal v21.2d, v12.2s, v19.2s
umulh x16, x3, x15
umlal v21.2d, v3.2s, v18.2s
add v30.4s, v5.4s, v5.4s
adds x7, x7, x2
umull v26.2d, v30.2s, v1.2s
adcs x21, x21, x8
umlal2 v26.2d, v30.4s, v1.4s
add v30.4s, v7.4s, v7.4s
adcs x22, x22, x9
umlal v26.2d, v30.2s, v19.2s
adc x23, x23, x16
umlal2 v26.2d, v30.4s, v19.4s
add v30.4s, v8.4s, v8.4s
ldr x3, [x0, #344]
umlal v26.2d, v30.2s, v18.2s
mul x2, x3, x12
umull2 v22.2d, v10.4s, v1.4s
umlal2 v22.2d, v12.4s, v19.4s
mul x8, x3, x13
umlal2 v22.2d, v3.4s, v18.4s
add v22.2d, v22.2d, v22.2d
mul x9, x3, x14
umlal v22.2d, v10.2s, v2.2s
mul x16, x3, x15
umlal v22.2d, v1.2s, v1.2s
umlal v22.2d, v13.2s, v19.2s
adds x7, x7, x2
add v30.4s, v5.4s, v5.4s
adcs x21, x21, x8
umull v27.2d, v30.2s, v2.2s
umlal2 v27.2d, v30.4s, v2.4s
adcs x22, x22, x9
add v30.4s, v6.4s, v6.4s
adcs x23, x23, x16
umlal v27.2d, v30.2s, v1.2s
add v30.4s, v8.4s, v8.4s
adc x24, x10, x10
umlal v27.2d, v30.2s, v19.2s
umulh x2, x3, x12
umlal2 v27.2d, v30.4s, v19.4s
umull2 v23.2d, v10.4s, v2.4s
umulh x8, x3, x13
umlal2 v23.2d, v1.4s, v1.4s
umulh x9, x3, x14
umlal2 v23.2d, v13.4s, v19.4s
add v23.2d, v23.2d, v23.2d
umulh x16, x3, x15
umlal v23.2d, v10.2s, v3.2s
adds x21, x21, x2
umlal v23.2d, v11.2s, v2.2s
umlal v23.2d, v4.2s, v19.2s
adcs x22, x22, x8
add v30.4s, v5.4s, v5.4s
adcs x23, x23, x9
umull v28.2d, v30.2s, v3.2s
umlal2 v28.2d, v30.4s, v3.4s
adc x24, x24, x16
add v30.4s, v6.4s, v6.4s
mul x2, x27, x21
umlal v28.2d, v30.2s, v2.2s
umlal2 v28.2d, v30.4s, v2.4s
mul x8, x27, x22
add v30.4s, v9.4s, v9.4s
mul x9, x27, x23
umlal v28.2d, v30.2s, v19.2s
umull2 v24.2d, v10.4s, v3.4s
mul x16, x27, x24
umlal2 v24.2d, v11.4s, v2.4s
umulh x21, x27, x21
umlal2 v24.2d, v4.4s, v19.4s
add v24.2d, v24.2d, v24.2d
umulh x22, x27, x22
umlal v24.2d, v10.2s, v4.2s
umulh x23, x27, x23
umlal v24.2d, v11.2s, v3.2s
umlal v24.2d, v2.2s, v2.2s
umulh x24, x27, x24
add v30.4s, v5.4s, v5.4s
adds x4, x4, x2
umull v29.2d, v30.2s, v4.2s
umlal2 v29.2d, v30.4s, v4.4s
adcs x5, x5, x8
add v30.4s, v6.4s, v6.4s
adcs x6, x6, x9
umlal v29.2d, v30.2s, v3.2s
umlal2 v29.2d, v30.4s, v3.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
umlal v29.2d, v30.2s, v2.2s
adc x24, x24, x10
ldr q3, [x0, #720]
adds x7, x7, x23
ldr q4, [x0, #736]
ushr v2.2d, v29.2d, #25
adc x24, x24, x10
and v29.16b, v29.16b, v4.16b
extr x17, x24, x7, #63
ushr v0.2d, v24.2d, #26
and v24.16b, v24.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
add v29.2d, v29.2d, v0.2d
mul x17, x17, x26
ushr v1.2d, v28.2d, #25
and v28.16b, v28.16b, v4.16b
adds x4, x4, x17
add v24.2d, v24.2d, v1.2d
adcs x5, x5, x21
ushr v0.2d, v23.2d, #26
and v23.16b, v23.16b, v3.16b
adcs x6, x6, x22
add v28.2d, v28.2d, v0.2d
adc x7, x7, x10
ushr v1.2d, v27.2d, #25
and v27.16b, v27.16b, v4.16b
stp x4, x5, [x0, #448]
add v23.2d, v23.2d, v1.2d
stp x6, x7, [x0, #464]
ushr v0.2d, v22.2d, #26
and v22.16b, v22.16b, v3.16b
ldp x12, x13, [x0, #256]
add v27.2d, v27.2d, v0.2d
ldp x14, x15, [x0, #272]
ushr v1.2d, v26.2d, #25
and v26.16b, v26.16b, v4.16b
ldr x3, [x0, #288]
add v22.2d, v22.2d, v1.2d
mul x4, x3, x12
ushr v0.2d, v21.2d, #26
and v21.16b, v21.16b, v3.16b
mul x5, x3, x13
add v26.2d, v26.2d, v0.2d
mul x6, x3, x14
ushr v1.2d, v25.2d, #25
and v25.16b, v25.16b, v4.16b
mul x7, x3, x15
add v21.2d, v21.2d, v1.2d
umulh x2, x3, x12
ushr v0.2d, v20.2d, #26
and v20.16b, v20.16b, v3.16b
umulh x8, x3, x13
add v25.2d, v25.2d, v0.2d
umulh x9, x3, x14
add v20.2d, v20.2d, v2.2d
shl v0.2d, v2.2d, #1
umulh x16, x3, x15
shl v2.2d, v2.2d, #4
adds x5, x5, x2
add v20.2d, v20.2d, v0.2d
add v20.2d, v20.2d, v2.2d
adcs x6, x6, x8
shl v25.2d, v25.2d, #26
adcs x7, x7, x9
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
adc x21, x16, x10
add v21.2d, v21.2d, v26.2d
shl v27.2d, v27.2d, #26
ldr x3, [x0, #296]
add v22.2d, v22.2d, v27.2d
mul x2, x3, x12
shl v28.2d, v28.2d, #26
add v23.2d, v23.2d, v28.2d
mul x8, x3, x13
shl v29.2d, v29.2d, #26
mul x9, x3, x14
add v24.2d, v24.2d, v29.2d
ldr q5, [x0, #704]
mul x16, x3, x15
ushr v25.2d, v20.2d, #51
adds x5, x5, x2
and v20.16b, v20.16b, v5.16b
ushr v26.2d, v21.2d, #51
adcs x6, x6, x8
and v21.16b, v21.16b, v5.16b
adcs x7, x7, x9
ushr v27.2d, v22.2d, #51
and v22.16b, v22.16b, v5.16b
adcs x21, x21, x16
ushr v28.2d, v23.2d, #51
adc x22, x10, x10
and v23.16b, v23.16b, v5.16b
ushr v29.2d, v24.2d, #51
umulh x2, x3, x12
and v24.16b, v24.16b, v5.16b
umulh x8, x3, x13
add v21.2d, v21.2d, v25.2d
add v22.2d, v22.2d, v26.2d
umulh x9, x3, x14
add v23.2d, v23.2d, v27.2d
umulh x16, x3, x15
add v24.2d, v24.2d, v28.2d
add v20.2d, v20.2d, v29.2d
adds x6, x6, x2
shl v0.2d, v29.2d, #1
adcs x7, x7, x8
shl v2.2d, v29.2d, #4
add v20.2d, v20.2d, v0.2d
adcs x21, x21, x9
add v20.2d, v20.2d, v2.2d
adc x22, x22, x16
trn1 v0.2d, v20.2d, v21.2d
trn2 v1.2d, v20.2d, v21.2d
ldr x3, [x0, #304]
str q0, [x0, #1024]
mul x2, x3, x12
str q1, [x0, #1072]
trn1 v0.2d, v22.2d, v23.2d
mul x8, x3, x13
trn2 v1.2d, v22.2d, v23.2d
mul x9, x3, x14
str q0, [x0, #1040]
str q1, [x0, #1088]
mul x16, x3, x15
trn1 v0.2d, v24.2d, v24.2d
adds x6, x6, x2
trn2 v1.2d, v24.2d, v24.2d
str q0, [x0, #1056]
adcs x7, x7, x8
str q1, [x0, #1104]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tak
lab_tak:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
ldr q22, [x0, #240]
mul x6, x3, x14
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
trn2 v25.2d, v20.2d, v21.2d
umulh x9, x3, x14
trn1 v26.2d, v22.2d, v23.2d
umulh x16, x3, x15
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
and v20.16b, v24.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v24.2d, #26
adc x21, x16, x10
and v21.16b, v21.16b, v30.16b
ldr x3, [x0, #328]
mul x2, x3, x12
uzp1 v0.4s, v20.4s, v21.4s
mul x8, x3, x13
shl v20.2d, v25.2d, #13
mul x9, x3, x14
sri v20.2d, v24.2d, #51
mul x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x5, x5, x2
adcs x6, x6, x8
ushr v21.2d, v25.2d, #13
adcs x7, x7, x9
and v21.16b, v21.16b, v30.16b
adcs x21, x21, x16
uzp1 v1.4s, v20.4s, v21.4s
adc x22, x10, x10
ushr v20.2d, v25.2d, #38
umulh x2, x3, x12
and v21.16b, v26.16b, v30.16b
umulh x8, x3, x13
umulh x9, x3, x14
uzp1 v2.4s, v20.4s, v21.4s
umulh x16, x3, x15
ushr v20.2d, v26.2d, #25
adds x6, x6, x2
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x8
shl v21.2d, v27.2d, #13
adcs x21, x21, x9
adc x22, x22, x16
sri v21.2d, v26.2d, #51
ldr x3, [x0, #336]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
uzp1 v3.4s, v20.4s, v21.4s
mul x8, x3, x13
ushr v20.2d, v27.2d, #12
mul x9, x3, x14
mul x16, x3, x15
and v20.16b, v20.16b, v31.16b
adds x6, x6, x2
ushr v21.2d, v27.2d, #38
adcs x7, x7, x8
uzp1 v4.4s, v20.4s, v21.4s
adcs x21, x21, x9
add v5.4s, v0.4s, v0.4s
adcs x22, x22, x16
adc x23, x10, x10
add v6.4s, v1.4s, v1.4s
umulh x2, x3, x12
add v7.4s, v2.4s, v2.4s
umulh x8, x3, x13
add v8.4s, v3.4s, v3.4s
umulh x9, x3, x14
ldr q31, [x0, #752]
umulh x16, x3, x15
adds x7, x7, x2
mul v9.4s, v1.4s, v31.4s
adcs x21, x21, x8
mul v10.4s, v2.4s, v31.4s
adcs x22, x22, x9
mul v11.4s, v3.4s, v31.4s
adc x23, x23, x16
mul v12.4s, v4.4s, v31.4s
ldr x3, [x0, #344]
umull v14.2d, v0.2s, v0.2s
mul x2, x3, x12
mul x8, x3, x13
umull2 v19.2d, v0.4s, v0.4s
mul x9, x3, x14
umlal v14.2d, v6.2s, v12.2s
mul x16, x3, x15
umlal2 v19.2d, v6.4s, v12.4s
adds x7, x7, x2
umlal v14.2d, v7.2s, v11.2s
adcs x21, x21, x8
adcs x22, x22, x9
umlal2 v19.2d, v7.4s, v11.4s
adcs x23, x23, x16
umull v15.2d, v5.2s, v1.2s
adc x24, x10, x10
umull2 v20.2d, v5.4s, v1.4s
umulh x2, x3, x12
umlal v15.2d, v7.2s, v12.2s
umulh x8, x3, x13
umulh x9, x3, x14
umlal2 v20.2d, v7.4s, v12.4s
umulh x16, x3, x15
umlal v15.2d, v3.2s, v11.2s
adds x21, x21, x2
umlal2 v20.2d, v3.4s, v11.4s
adcs x22, x22, x8
umull v16.2d, v5.2s, v2.2s
adcs x23, x23, x9
adc x24, x24, x16
umull2 v21.2d, v5.4s, v2.4s
mul x2, x27, x21
umlal v16.2d, v1.2s, v1.2s
mul x8, x27, x22
umlal2 v21.2d, v1.4s, v1.4s
mul x9, x27, x23
umlal v16.2d, v8.2s, v12.2s
mul x16, x27, x24
umlal2 v21.2d, v8.4s, v12.4s
umulh x21, x27, x21
umulh x22, x27, x22
umull v17.2d, v5.2s, v3.2s
umulh x23, x27, x23
umull2 v22.2d, v5.4s, v3.4s
umulh x24, x27, x24
umlal v17.2d, v6.2s, v2.2s
adds x4, x4, x2
umlal2 v22.2d, v6.4s, v2.4s
adcs x5, x5, x8
adcs x6, x6, x9
umlal v17.2d, v4.2s, v12.2s
adcs x7, x7, x16
umlal2 v22.2d, v4.4s, v12.4s
adc x24, x24, x10
umull v18.2d, v5.2s, v4.2s
adds x7, x7, x23
umull2 v23.2d, v5.4s, v4.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umlal v18.2d, v6.2s, v3.2s
and x7, x7, #0x7fffffffffffffff
umlal2 v23.2d, v6.4s, v3.4s
mul x17, x17, x26
umlal v18.2d, v2.2s, v2.2s
adds x4, x4, x17
umlal2 v23.2d, v2.4s, v2.4s
adcs x5, x5, x21
adcs x6, x6, x22
ext v31.16b, v0.16b, v0.16b, #8
adc x7, x7, x10
add v0.4s, v0.4s, v31.4s
stp x4, x5, [x0, #448]
ext v31.16b, v1.16b, v1.16b, #8
stp x6, x7, [x0, #464]
add v1.4s, v1.4s, v31.4s
ldp x12, x13, [x0, #256]
ldp x14, x15, [x0, #272]
ext v31.16b, v2.16b, v2.16b, #8
ldr x3, [x0, #288]
add v2.4s, v2.4s, v31.4s
mul x4, x3, x12
ext v31.16b, v3.16b, v3.16b, #8
mul x5, x3, x13
add v3.4s, v3.4s, v31.4s
mul x6, x3, x14
ext v31.16b, v4.16b, v4.16b, #8
mul x7, x3, x15
umulh x2, x3, x12
add v4.4s, v4.4s, v31.4s
umulh x8, x3, x13
ext v31.16b, v5.16b, v5.16b, #8
umulh x9, x3, x14
add v5.4s, v5.4s, v31.4s
umulh x16, x3, x15
ext v31.16b, v6.16b, v6.16b, #8
adds x5, x5, x2
adcs x6, x6, x8
add v6.4s, v6.4s, v31.4s
adcs x7, x7, x9
ext v31.16b, v7.16b, v7.16b, #8
adc x21, x16, x10
add v7.4s, v7.4s, v31.4s
ldr x3, [x0, #296]
ext v31.16b, v8.16b, v8.16b, #8
mul x2, x3, x12
mul x8, x3, x13
add v8.4s, v8.4s, v31.4s
mul x9, x3, x14
ext v31.16b, v9.16b, v9.16b, #8
mul x16, x3, x15
add v9.4s, v9.4s, v31.4s
adds x5, x5, x2
ext v31.16b, v10.16b, v10.16b, #8
adcs x6, x6, x8
adcs x7, x7, x9
add v10.4s, v10.4s, v31.4s
adcs x21, x21, x16
ext v31.16b, v11.16b, v11.16b, #8
adc x22, x10, x10
add v11.4s, v11.4s, v31.4s
umulh x2, x3, x12
ext v31.16b, v12.16b, v12.16b, #8
umulh x8, x3, x13
umulh x9, x3, x14
add v12.4s, v12.4s, v31.4s
umulh x16, x3, x15
umull v24.2d, v0.2s, v0.2s
adds x6, x6, x2
umlal v24.2d, v6.2s, v12.2s
adcs x7, x7, x8
umlal v24.2d, v7.2s, v11.2s
adcs x21, x21, x9
umull v25.2d, v5.2s, v1.2s
adc x22, x22, x16
ldr x3, [x0, #304]
umlal v25.2d, v7.2s, v12.2s
mul x2, x3, x12
umlal v25.2d, v3.2s, v11.2s
mul x8, x3, x13
umull v26.2d, v5.2s, v2.2s
mul x9, x3, x14
umlal v26.2d, v1.2s, v1.2s
mul x16, x3, x15
adds x6, x6, x2
umlal v26.2d, v8.2s, v12.2s
adcs x7, x7, x8
umull v27.2d, v5.2s, v3.2s
adcs x21, x21, x9
umlal v27.2d, v6.2s, v2.2s
adcs x22, x22, x16
umlal v27.2d, v4.2s, v12.2s
adc x23, x10, x10
umulh x2, x3, x12
umull v28.2d, v5.2s, v4.2s
umulh x8, x3, x13
umlal v28.2d, v6.2s, v3.2s
umulh x9, x3, x14
umlal v28.2d, v2.2s, v2.2s
umulh x16, x3, x15
sub v24.2d, v24.2d, v14.2d
adds x7, x7, x2
adcs x21, x21, x8
sub v24.2d, v24.2d, v19.2d
adcs x22, x22, x9
sub v25.2d, v25.2d, v15.2d
adc x23, x23, x16
sub v25.2d, v25.2d, v20.2d
ldr x3, [x0, #312]
sub v26.2d, v26.2d, v16.2d
mul x2, x3, x12
sub v26.2d, v26.2d, v21.2d
mul x8, x3, x13
mul x9, x3, x14
sub v27.2d, v27.2d, v17.2d
mul x16, x3, x15
sub v27.2d, v27.2d, v22.2d
adds x7, x7, x2
sub v28.2d, v28.2d, v18.2d
adcs x21, x21, x8
sub v28.2d, v28.2d, v23.2d
adcs x22, x22, x9
adcs x23, x23, x16
add v15.2d, v15.2d, v19.2d
adc x24, x10, x10
add v15.2d, v15.2d, v19.2d
umulh x2, x3, x12
add v16.2d, v16.2d, v20.2d
umulh x8, x3, x13
add v16.2d, v16.2d, v20.2d
umulh x9, x3, x14
umulh x16, x3, x15
add v17.2d, v17.2d, v21.2d
adds x21, x21, x2
add v17.2d, v17.2d, v21.2d
adcs x22, x22, x8
add v18.2d, v18.2d, v22.2d
adcs x23, x23, x9
add v18.2d, v18.2d, v22.2d
adc x24, x24, x16
mul x2, x27, x21
shl v0.2d, v23.2d, #1
mul x8, x27, x22
shl v1.2d, v23.2d, #2
mul x9, x27, x23
shl v2.2d, v23.2d, #5
mul x16, x27, x24
add v14.2d, v14.2d, v0.2d
umulh x21, x27, x21
umulh x22, x27, x22
add v1.2d, v1.2d, v2.2d
umulh x23, x27, x23
add v14.2d, v14.2d, v1.2d
umulh x24, x27, x24
ldr q3, [x0, #720]
adds x4, x4, x2
ldr q4, [x0, #736]
adcs x5, x5, x8
ushr v2.2d, v28.2d, #25
adcs x6, x6, x9
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
ushr v0.2d, v18.2d, #26
adds x7, x7, x23
and v18.16b, v18.16b, v3.16b
adc x24, x24, x10
add v28.2d, v28.2d, v0.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
ushr v1.2d, v27.2d, #25
mul x17, x17, x26
and v27.16b, v27.16b, v4.16b
adds x4, x4, x17
add v18.2d, v18.2d, v1.2d
adcs x5, x5, x21
ushr v0.2d, v17.2d, #26
adcs x6, x6, x22
adc x7, x7, x10
and v17.16b, v17.16b, v3.16b
stp x4, x5, [x0, #480]
add v27.2d, v27.2d, v0.2d
stp x6, x7, [x0, #496]
ushr v1.2d, v26.2d, #25
ldp x4, x5, [x0, #448]
and v26.16b, v26.16b, v4.16b
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
add v17.2d, v17.2d, v1.2d
ldp x23, x24, [x0, #496]
ushr v0.2d, v16.2d, #26
subs x12, x4, x21
and v16.16b, v16.16b, v3.16b
sbcs x13, x5, x22
add v26.2d, v26.2d, v0.2d
sbcs x14, x6, x23
sbcs x15, x7, x24
ushr v1.2d, v25.2d, #25
csel x3, x10, x27, hs
and v25.16b, v25.16b, v4.16b
subs x12, x12, x3
add v16.2d, v16.2d, v1.2d
sbcs x13, x13, x10
ushr v0.2d, v15.2d, #26
sbcs x14, x14, x10
and v15.16b, v15.16b, v3.16b
sbc x15, x15, x10
mul x5, x12, x13
add v25.2d, v25.2d, v0.2d
mul x6, x12, x14
ushr v1.2d, v24.2d, #25
mul x7, x12, x15
and v24.16b, v24.16b, v4.16b
umulh x2, x12, x13
add v15.2d, v15.2d, v1.2d
umulh x8, x12, x14
umulh x9, x12, x15
ushr v0.2d, v14.2d, #26
mul x16, x13, x14
and v14.16b, v14.16b, v3.16b
mul x17, x13, x15
add v24.2d, v24.2d, v0.2d
umulh x3, x13, x14
add v14.2d, v14.2d, v2.2d
umulh x11, x13, x15
mul x20, x14, x15
shl v0.2d, v2.2d, #1
umulh x23, x14, x15
shl v2.2d, v2.2d, #4
adds x6, x6, x2
add v14.2d, v14.2d, v0.2d
adcs x7, x7, x8
add v14.2d, v14.2d, v2.2d
adc x21, x9, x10
adds x7, x7, x16
shl v24.2d, v24.2d, #26
adcs x21, x21, x17
add v14.2d, v14.2d, v24.2d
adc x22, x11, x10
shl v25.2d, v25.2d, #26
adds x21, x21, x3
add v15.2d, v15.2d, v25.2d
adcs x22, x22, x20
shl v26.2d, v26.2d, #26
adc x23, x23, x10
lsr x24, x23, #63
add v16.2d, v16.2d, v26.2d
extr x23, x23, x22, #63
shl v27.2d, v27.2d, #26
extr x22, x22, x21, #63
add v17.2d, v17.2d, v27.2d
extr x21, x21, x7, #63
shl v28.2d, v28.2d, #26
extr x7, x7, x6, #63
extr x6, x6, x5, #63
add v18.2d, v18.2d, v28.2d
lsl x5, x5, #1
ldr q5, [x0, #704]
mul x4, x12, x12
ushr v24.2d, v14.2d, #51
umulh x2, x12, x12
and v14.16b, v14.16b, v5.16b
mul x8, x13, x13
umulh x9, x13, x13
ushr v25.2d, v15.2d, #51
mul x16, x14, x14
and v15.16b, v15.16b, v5.16b
umulh x17, x14, x14
ushr v26.2d, v16.2d, #51
mul x3, x15, x15
and v16.16b, v16.16b, v5.16b
umulh x11, x15, x15
adds x5, x5, x2
ushr v27.2d, v17.2d, #51
adcs x6, x6, x8
and v17.16b, v17.16b, v5.16b
adcs x7, x7, x9
ushr v28.2d, v18.2d, #51
adcs x21, x21, x16
and v18.16b, v18.16b, v5.16b
adcs x22, x22, x17
adcs x23, x23, x3
add v15.2d, v15.2d, v24.2d
adc x24, x24, x11
add v16.2d, v16.2d, v25.2d
mul x2, x27, x21
add v17.2d, v17.2d, v26.2d
mul x8, x27, x22
add v18.2d, v18.2d, v27.2d
mul x9, x27, x23
add v14.2d, v14.2d, v28.2d
mul x16, x27, x24
umulh x21, x27, x21
shl v0.2d, v28.2d, #1
umulh x22, x27, x22
shl v2.2d, v28.2d, #4
umulh x23, x27, x23
add v14.2d, v14.2d, v0.2d
umulh x24, x27, x24
add v14.2d, v14.2d, v2.2d
adds x4, x4, x2
adcs x5, x5, x8
trn1 v0.2d, v14.2d, v15.2d
adcs x6, x6, x9
trn2 v1.2d, v14.2d, v15.2d
adcs x7, x7, x16
str q0, [x0, #1024]
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
adc x24, x24, x10
trn1 v0.2d, v16.2d, v17.2d
extr x17, x24, x7, #63
trn2 v1.2d, v16.2d, v17.2d
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
adcs x5, x5, x21
trn1 v0.2d, v18.2d, v18.2d
adcs x6, x6, x22
trn2 v1.2d, v18.2d, v18.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tan
lab_tan:
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
ldr q31, [x0, #720]
ldp x14, x15, [x0, #240]
ldr q30, [x0, #736]
ldr x3, [x0, #320]
ldr q20, [x0, #224]
mul x4, x3, x12
ldr q21, [x0, #256]
mul x5, x3, x13
mul x6, x3, x14
ldr q22, [x0, #240]
mul x7, x3, x15
ldr q23, [x0, #272]
umulh x2, x3, x12
trn1 v24.2d, v20.2d, v21.2d
umulh x8, x3, x13
umulh x9, x3, x14
trn2 v25.2d, v20.2d, v21.2d
umulh x16, x3, x15
trn1 v26.2d, v22.2d, v23.2d
adds x5, x5, x2
trn2 v27.2d, v22.2d, v23.2d
adcs x6, x6, x8
adcs x7, x7, x9
and v20.16b, v24.16b, v31.16b
adc x21, x16, x10
ushr v21.2d, v24.2d, #26
ldr x3, [x0, #328]
and v21.16b, v21.16b, v30.16b
mul x2, x3, x12
mul x8, x3, x13
uzp1 v0.4s, v20.4s, v21.4s
mul x9, x3, x14
shl v20.2d, v25.2d, #13
mul x16, x3, x15
sri v20.2d, v24.2d, #51
adds x5, x5, x2
adcs x6, x6, x8
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x9
ushr v21.2d, v25.2d, #13
adcs x21, x21, x16
and v21.16b, v21.16b, v30.16b
adc x22, x10, x10
umulh x2, x3, x12
uzp1 v1.4s, v20.4s, v21.4s
umulh x8, x3, x13
ushr v20.2d, v25.2d, #38
umulh x9, x3, x14
and v21.16b, v26.16b, v30.16b
umulh x16, x3, x15
uzp1 v2.4s, v20.4s, v21.4s
adds x6, x6, x2
adcs x7, x7, x8
ushr v20.2d, v26.2d, #25
adcs x21, x21, x9
and v20.16b, v20.16b, v31.16b
adc x22, x22, x16
shl v21.2d, v27.2d, #13
ldr x3, [x0, #336]
mul x2, x3, x12
sri v21.2d, v26.2d, #51
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
mul x16, x3, x15
adds x6, x6, x2
ushr v20.2d, v27.2d, #12
adcs x7, x7, x8
and v20.16b, v20.16b, v31.16b
adcs x21, x21, x9
ushr v21.2d, v27.2d, #38
adcs x22, x22, x16
adc x23, x10, x10
uzp1 v4.4s, v20.4s, v21.4s
umulh x2, x3, x12
ext v5.16b, v0.16b, v0.16b, #8
umulh x8, x3, x13
ext v6.16b, v1.16b, v1.16b, #8
umulh x9, x3, x14
umulh x16, x3, x15
ext v7.16b, v2.16b, v2.16b, #8
adds x7, x7, x2
ext v8.16b, v3.16b, v3.16b, #8
adcs x21, x21, x8
ext v9.16b, v4.16b, v4.16b, #8
adcs x22, x22, x9
adc x23, x23, x16
add v10.4s, v0.4s, v0.4s
ldr x3, [x0, #344]
add v11.4s, v1.4s, v1.4s
mul x2, x3, x12
add v12.4s, v2.4s, v2.4s
mul x8, x3, x13
add v13.4s, v3.4s, v3.4s
mul x9, x3, x14
mul x16, x3, x15
add v14.4s, v4.4s, v4.4s
adds x7, x7, x2
ldr q31, [x0, #752]
adcs x21, x21, x8
mul v15.4s, v0.4s, v31.4s
adcs x22, x22, x9
adcs x23, x23, x16
mul v16.4s, v1.4s, v31.4s
adc x24, x10, x10
mul v17.4s, v2.4s, v31.4s
umulh x2, x3, x12
mul v18.4s, v3.4s, v31.4s
umulh x8, x3, x13
umulh x9, x3, x14
mul v19.4s, v4.4s, v31.4s
umulh x16, x3, x15
umull2 v20.2d, v10.4s, v19.4s
adds x21, x21, x2
umlal2 v20.2d, v11.4s, v18.4s
adcs x22, x22, x8
adcs x23, x23, x9
umlal2 v20.2d, v2.4s, v17.4s
adc x24, x24, x16
add v20.2d, v20.2d, v20.2d
mul x2, x27, x21
umlal v20.2d, v0.2s, v0.2s
mul x8, x27, x22
mul x9, x27, x23
umlal v20.2d, v11.2s, v19.2s
mul x16, x27, x24
umlal v20.2d, v12.2s, v18.2s
umulh x21, x27, x21
add v30.4s, v5.4s, v5.4s
umulh x22, x27, x22
umulh x23, x27, x23
umull v25.2d, v30.2s, v0.2s
umulh x24, x27, x24
add v30.4s, v6.4s, v6.4s
adds x4, x4, x2
umlal v25.2d, v30.2s, v19.2s
adcs x5, x5, x8
adcs x6, x6, x9
umlal2 v25.2d, v30.4s, v19.4s
adcs x7, x7, x16
add v30.4s, v7.4s, v7.4s
adc x24, x24, x10
umlal v25.2d, v30.2s, v18.2s
adds x7, x7, x23
umlal2 v25.2d, v30.4s, v18.4s
adc x24, x24, x10
extr x17, x24, x7, #63
umull2 v21.2d, v0.4s, v0.4s
and x7, x7, #0x7fffffffffffffff
umlal2 v21.2d, v11.4s, v19.4s
mul x17, x17, x26
umlal2 v21.2d, v12.4s, v18.4s
adds x4, x4, x17
adcs x5, x5, x21
add v21.2d, v21.2d, v21.2d
adcs x6, x6, x22
umlal v21.2d, v10.2s, v1.2s
adc x7, x7, x10
umlal v21.2d, v12.2s, v19.2s
stp x4, x5, [x0, #448]
stp x6, x7, [x0, #464]
umlal v21.2d, v3.2s, v18.2s
ldp x12, x13, [x0, #256]
add v30.4s, v5.4s, v5.4s
ldp x14, x15, [x0, #272]
umull v26.2d, v30.2s, v1.2s
ldr x3, [x0, #288]
mul x4, x3, x12
umlal2 v26.2d, v30.4s, v1.4s
mul x5, x3, x13
add v30.4s, v7.4s, v7.4s
mul x6, x3, x14
umlal v26.2d, v30.2s, v19.2s
mul x7, x3, x15
umulh x2, x3, x12
umlal2 v26.2d, v30.4s, v19.4s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umlal v26.2d, v30.2s, v18.2s
umulh x16, x3, x15
adds x5, x5, x2
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x8
umlal2 v22.2d, v12.4s, v19.4s
adcs x7, x7, x9
umlal2 v22.2d, v3.4s, v18.4s
adc x21, x16, x10
add v22.2d, v22.2d, v22.2d
ldr x3, [x0, #296]
mul x2, x3, x12
umlal v22.2d, v10.2s, v2.2s
mul x8, x3, x13
umlal v22.2d, v1.2s, v1.2s
mul x9, x3, x14
umlal v22.2d, v13.2s, v19.2s
mul x16, x3, x15
adds x5, x5, x2
add v30.4s, v5.4s, v5.4s
adcs x6, x6, x8
umull v27.2d, v30.2s, v2.2s
adcs x7, x7, x9
umlal2 v27.2d, v30.4s, v2.4s
adcs x21, x21, x16
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v27.2d, v30.2s, v1.2s
umulh x8, x3, x13
add v30.4s, v8.4s, v8.4s
umulh x9, x3, x14
umulh x16, x3, x15
umlal v27.2d, v30.2s, v19.2s
adds x6, x6, x2
umlal2 v27.2d, v30.4s, v19.4s
adcs x7, x7, x8
umull2 v23.2d, v10.4s, v2.4s
adcs x21, x21, x9
adc x22, x22, x16
umlal2 v23.2d, v1.4s, v1.4s
ldr x3, [x0, #304]
umlal2 v23.2d, v13.4s, v19.4s
mul x2, x3, x12
add v23.2d, v23.2d, v23.2d
mul x8, x3, x13
mul x9, x3, x14
umlal v23.2d, v10.2s, v3.2s
mul x16, x3, x15
umlal v23.2d, v11.2s, v2.2s
adds x6, x6, x2
umlal v23.2d, v4.2s, v19.2s
adcs x7, x7, x8
adcs x21, x21, x9
add v30.4s, v5.4s, v5.4s
adcs x22, x22, x16
umull v28.2d, v30.2s, v3.2s
adc x23, x10, x10
umlal2 v28.2d, v30.4s, v3.4s
umulh x2, x3, x12
add v30.4s, v6.4s, v6.4s
umulh x8, x3, x13
umulh x9, x3, x14
umlal v28.2d, v30.2s, v2.2s
umulh x16, x3, x15
umlal2 v28.2d, v30.4s, v2.4s
adds x7, x7, x2
add v30.4s, v9.4s, v9.4s
adcs x21, x21, x8
adcs x22, x22, x9
umlal v28.2d, v30.2s, v19.2s
adc x23, x23, x16
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #312]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
mul x8, x3, x13
umlal2 v24.2d, v4.4s, v19.4s
mul x9, x3, x14
add v24.2d, v24.2d, v24.2d
mul x16, x3, x15
umlal v24.2d, v10.2s, v4.2s
adds x7, x7, x2
adcs x21, x21, x8
umlal v24.2d, v11.2s, v3.2s
adcs x22, x22, x9
umlal v24.2d, v2.2s, v2.2s
adcs x23, x23, x16
add v30.4s, v5.4s, v5.4s
adc x24, x10, x10
umulh x2, x3, x12
umull v29.2d, v30.2s, v4.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v4.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
adds x21, x21, x2
umlal v29.2d, v30.2s, v3.2s
adcs x22, x22, x8
umlal2 v29.2d, v30.4s, v3.4s
adcs x23, x23, x9
add v30.4s, v7.4s, v7.4s
adc x24, x24, x16
umlal v29.2d, v30.2s, v2.2s
mul x2, x27, x21
mul x8, x27, x22
ldr q3, [x0, #720]
mul x9, x27, x23
ldr q4, [x0, #736]
mul x16, x27, x24
ushr v2.2d, v29.2d, #25
umulh x21, x27, x21
umulh x22, x27, x22
and v29.16b, v29.16b, v4.16b
umulh x23, x27, x23
ushr v0.2d, v24.2d, #26
umulh x24, x27, x24
and v24.16b, v24.16b, v3.16b
adds x4, x4, x2
adcs x5, x5, x8
add v29.2d, v29.2d, v0.2d
adcs x6, x6, x9
ushr v1.2d, v28.2d, #25
adcs x7, x7, x16
and v28.16b, v28.16b, v4.16b
adc x24, x24, x10
adds x7, x7, x23
add v24.2d, v24.2d, v1.2d
adc x24, x24, x10
ushr v0.2d, v23.2d, #26
extr x17, x24, x7, #63
and v23.16b, v23.16b, v3.16b
and x7, x7, #0x7fffffffffffffff
mul x17, x17, x26
add v28.2d, v28.2d, v0.2d
adds x4, x4, x17
ushr v1.2d, v27.2d, #25
adcs x5, x5, x21
and v27.16b, v27.16b, v4.16b
adcs x6, x6, x22
adc x7, x7, x10
add v23.2d, v23.2d, v1.2d
stp x4, x5, [x0, #480]
ushr v0.2d, v22.2d, #26
stp x6, x7, [x0, #496]
and v22.16b, v22.16b, v3.16b
ldp x4, x5, [x0, #448]
add v27.2d, v27.2d, v0.2d
ldp x6, x7, [x0, #464]
ldp x21, x22, [x0, #480]
ushr v1.2d, v26.2d, #25
ldp x23, x24, [x0, #496]
and v26.16b, v26.16b, v4.16b
subs x12, x4, x21
add v22.2d, v22.2d, v1.2d
sbcs x13, x5, x22
sbcs x14, x6, x23
ushr v0.2d, v21.2d, #26
sbcs x15, x7, x24
and v21.16b, v21.16b, v3.16b
csel x3, x10, x27, hs
add v26.2d, v26.2d, v0.2d
subs x12, x12, x3
sbcs x13, x13, x10
ushr v1.2d, v25.2d, #25
sbcs x14, x14, x10
and v25.16b, v25.16b, v4.16b
sbc x15, x15, x10
add v21.2d, v21.2d, v1.2d
mul x5, x12, x13
mul x6, x12, x14
ushr v0.2d, v20.2d, #26
mul x7, x12, x15
and v20.16b, v20.16b, v3.16b
umulh x2, x12, x13
add v25.2d, v25.2d, v0.2d
umulh x8, x12, x14
umulh x9, x12, x15
add v20.2d, v20.2d, v2.2d
mul x16, x13, x14
shl v0.2d, v2.2d, #1
mul x17, x13, x15
shl v2.2d, v2.2d, #4
umulh x3, x13, x14
umulh x11, x13, x15
add v20.2d, v20.2d, v0.2d
mul x20, x14, x15
add v20.2d, v20.2d, v2.2d
umulh x23, x14, x15
shl v25.2d, v25.2d, #26
adds x6, x6, x2
adcs x7, x7, x8
add v20.2d, v20.2d, v25.2d
adc x21, x9, x10
shl v26.2d, v26.2d, #26
adds x7, x7, x16
add v21.2d, v21.2d, v26.2d
adcs x21, x21, x17
shl v27.2d, v27.2d, #26
adc x22, x11, x10
adds x21, x21, x3
add v22.2d, v22.2d, v27.2d
adcs x22, x22, x20
shl v28.2d, v28.2d, #26
adc x23, x23, x10
add v23.2d, v23.2d, v28.2d
adds x5, x5, x5
adcs x6, x6, x6
shl v29.2d, v29.2d, #26
adcs x7, x7, x7
add v24.2d, v24.2d, v29.2d
adcs x21, x21, x21
ldr q5, [x0, #704]
adcs x22, x22, x22
adcs x23, x23, x23
ushr v25.2d, v20.2d, #51
adc x24, x10, x10
and v20.16b, v20.16b, v5.16b
mul x4, x12, x12
ushr v26.2d, v21.2d, #51
umulh x2, x12, x12
mul x8, x13, x13
and v21.16b, v21.16b, v5.16b
umulh x9, x13, x13
ushr v27.2d, v22.2d, #51
mul x16, x14, x14
and v22.16b, v22.16b, v5.16b
umulh x17, x14, x14
mul x3, x15, x15
ushr v28.2d, v23.2d, #51
umulh x11, x15, x15
and v23.16b, v23.16b, v5.16b
adds x5, x5, x2
ushr v29.2d, v24.2d, #51
adcs x6, x6, x8
adcs x7, x7, x9
and v24.16b, v24.16b, v5.16b
adcs x21, x21, x16
add v21.2d, v21.2d, v25.2d
adcs x22, x22, x17
add v22.2d, v22.2d, v26.2d
adcs x23, x23, x3
add v23.2d, v23.2d, v27.2d
adc x24, x24, x11
mul x2, x27, x21
add v24.2d, v24.2d, v28.2d
mul x8, x27, x22
add v20.2d, v20.2d, v29.2d
mul x9, x27, x23
shl v0.2d, v29.2d, #1
mul x16, x27, x24
umulh x21, x27, x21
shl v2.2d, v29.2d, #4
umulh x22, x27, x22
add v20.2d, v20.2d, v0.2d
umulh x23, x27, x23
add v20.2d, v20.2d, v2.2d
umulh x24, x27, x24
adds x4, x4, x2
trn1 v0.2d, v20.2d, v21.2d
adcs x5, x5, x8
trn2 v1.2d, v20.2d, v21.2d
adcs x6, x6, x9
str q0, [x0, #1024]
adcs x7, x7, x16
adc x24, x24, x10
str q1, [x0, #1072]
adds x7, x7, x23
trn1 v0.2d, v22.2d, v23.2d
adc x24, x24, x10
trn2 v1.2d, v22.2d, v23.2d
extr x17, x24, x7, #63
and x7, x7, #0x7fffffffffffffff
str q0, [x0, #1040]
mul x17, x17, x26
str q1, [x0, #1088]
adds x4, x4, x17
trn1 v0.2d, v24.2d, v24.2d
adcs x5, x5, x21
adcs x6, x6, x22
trn2 v1.2d, v24.2d, v24.2d
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tj43
lab_tj43:
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
mul x2, x3, x12
ushr v21.2d, v25.2d, #13
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v25.2d, #38
adds x5, x5, x2
and v21.16b, v26.16b, v30.16b
adcs x6, x6, x8
uzp1 v2.4s, v20.4s, v21.4s
adcs x7, x7, x9
ushr v20.2d, v26.2d, #25
adcs x21, x21, x16
and v20.16b, v20.16b, v31.16b
adc x22, x10, x10
shl v21.2d, v27.2d, #13
umulh x2, x3, x12
sri v21.2d, v26.2d, #51
umulh x8, x3, x13
and v21.16b, v21.16b, v30.16b
umulh x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
umulh x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x6, x6, x2
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x8
ushr v21.2d, v27.2d, #38
adcs x21, x21, x9
uzp1 v4.4s, v20.4s, v21.4s
adc x22, x22, x16
ext v5.16b, v0.16b, v0.16b, #8
ldr x3, [x0, #336]
ext v6.16b, v1.16b, v1.16b, #8
mul x2, x3, x12
ext v7.16b, v2.16b, v2.16b, #8
mul x8, x3, x13
ext v8.16b, v3.16b, v3.16b, #8
mul x9, x3, x14
ext v9.16b, v4.16b, v4.16b, #8
mul x16, x3, x15
add v10.4s, v0.4s, v0.4s
adds x6, x6, x2
add v11.4s, v1.4s, v1.4s
adcs x7, x7, x8
add v12.4s, v2.4s, v2.4s
adcs x21, x21, x9
add v13.4s, v3.4s, v3.4s
adcs x22, x22, x16
add v14.4s, v4.4s, v4.4s
adc x23, x10, x10
ldr q31, [x0, #752]
umulh x2, x3, x12
mul v15.4s, v0.4s, v31.4s
umulh x8, x3, x13
mul v16.4s, v1.4s, v31.4s
umulh x9, x3, x14
mul v17.4s, v2.4s, v31.4s
umulh x16, x3, x15
mul v18.4s, v3.4s, v31.4s
adds x7, x7, x2
mul v19.4s, v4.4s, v31.4s
adcs x21, x21, x8
umull2 v20.2d, v10.4s, v19.4s
adcs x22, x22, x9
umlal2 v20.2d, v11.4s, v18.4s
adc x23, x23, x16
umlal2 v20.2d, v2.4s, v17.4s
ldr x3, [x0, #344]
add v20.2d, v20.2d, v20.2d
mul x2, x3, x12
umlal v20.2d, v0.2s, v0.2s
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
umlal v25.2d, v30.2s, v18.2s
umulh x8, x3, x13
umlal2 v25.2d, v30.4s, v18.4s
umulh x9, x3, x14
umull2 v21.2d, v0.4s, v0.4s
umulh x16, x3, x15
umlal2 v21.2d, v11.4s, v19.4s
adds x21, x21, x2
umlal2 v21.2d, v12.4s, v18.4s
adcs x22, x22, x8
add v21.2d, v21.2d, v21.2d
adcs x23, x23, x9
umlal v21.2d, v10.2s, v1.2s
adc x24, x24, x16
umlal v21.2d, v12.2s, v19.2s
mul x2, x27, x21
umlal v21.2d, v3.2s, v18.2s
mul x8, x27, x22
add v30.4s, v5.4s, v5.4s
mul x9, x27, x23
umull v26.2d, v30.2s, v1.2s
mul x16, x27, x24
umlal2 v26.2d, v30.4s, v1.4s
umulh x21, x27, x21
add v30.4s, v7.4s, v7.4s
umulh x22, x27, x22
umlal v26.2d, v30.2s, v19.2s
umulh x23, x27, x23
umlal2 v26.2d, v30.4s, v19.4s
umulh x24, x27, x24
add v30.4s, v8.4s, v8.4s
adds x4, x4, x2
umlal v26.2d, v30.2s, v18.2s
adcs x5, x5, x8
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x9
umlal2 v22.2d, v12.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
adcs x7, x7, x16
add v22.2d, v22.2d, v22.2d
adc x24, x24, x10
umlal v22.2d, v10.2s, v2.2s
adds x7, x7, x23
umlal v22.2d, v1.2s, v1.2s
adc x24, x24, x10
umlal v22.2d, v13.2s, v19.2s
extr x17, x24, x7, #63
add v30.4s, v5.4s, v5.4s
and x7, x7, #0x7fffffffffffffff
umull v27.2d, v30.2s, v2.2s
mul x17, x17, x26
umlal2 v27.2d, v30.4s, v2.4s
adds x4, x4, x17
add v30.4s, v6.4s, v6.4s
adcs x5, x5, x21
umlal v27.2d, v30.2s, v1.2s
adcs x6, x6, x22
add v30.4s, v8.4s, v8.4s
adc x7, x7, x10
umlal v27.2d, v30.2s, v19.2s
stp x4, x5, [x0, #448]
umlal2 v27.2d, v30.4s, v19.4s
stp x6, x7, [x0, #464]
umull2 v23.2d, v10.4s, v2.4s
ldp x12, x13, [x0, #256]
umlal2 v23.2d, v1.4s, v1.4s
ldp x14, x15, [x0, #272]
umlal2 v23.2d, v13.4s, v19.4s
ldr x3, [x0, #288]
add v23.2d, v23.2d, v23.2d
mul x4, x3, x12
umlal v23.2d, v10.2s, v3.2s
mul x5, x3, x13
umlal v23.2d, v11.2s, v2.2s
mul x6, x3, x14
umlal v23.2d, v4.2s, v19.2s
mul x7, x3, x15
add v30.4s, v5.4s, v5.4s
umulh x2, x3, x12
umull v28.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v28.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v28.2d, v30.2s, v2.2s
adds x5, x5, x2
umlal2 v28.2d, v30.4s, v2.4s
adcs x6, x6, x8
add v30.4s, v9.4s, v9.4s
adcs x7, x7, x9
umlal v28.2d, v30.2s, v19.2s
adc x21, x16, x10
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #296]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
umlal2 v24.2d, v4.4s, v19.4s
mul x8, x3, x13
add v24.2d, v24.2d, v24.2d
mul x9, x3, x14
umlal v24.2d, v10.2s, v4.2s
mul x16, x3, x15
umlal v24.2d, v11.2s, v3.2s
adds x5, x5, x2
umlal v24.2d, v2.2s, v2.2s
adcs x6, x6, x8
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x9
umull v29.2d, v30.2s, v4.2s
adcs x21, x21, x16
umlal2 v29.2d, v30.4s, v4.4s
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v29.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v7.4s, v7.4s
umulh x16, x3, x15
umlal v29.2d, v30.2s, v2.2s
adds x6, x6, x2
ldr q3, [x0, #720]
adcs x7, x7, x8
ldr q4, [x0, #736]
adcs x21, x21, x9
ushr v2.2d, v29.2d, #25
adc x22, x22, x16
and v29.16b, v29.16b, v4.16b
ldr x3, [x0, #304]
ushr v0.2d, v24.2d, #26
mul x2, x3, x12
and v24.16b, v24.16b, v3.16b
mul x8, x3, x13
add v29.2d, v29.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v28.2d, #25
mul x16, x3, x15
and v28.16b, v28.16b, v4.16b
adds x6, x6, x2
add v24.2d, v24.2d, v1.2d
adcs x7, x7, x8
ushr v0.2d, v23.2d, #26
adcs x21, x21, x9
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x16
add v28.2d, v28.2d, v0.2d
adc x23, x10, x10
ushr v1.2d, v27.2d, #25
umulh x2, x3, x12
and v27.16b, v27.16b, v4.16b
umulh x8, x3, x13
add v23.2d, v23.2d, v1.2d
umulh x9, x3, x14
ushr v0.2d, v22.2d, #26
umulh x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x7, x7, x2
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x8
ushr v1.2d, v26.2d, #25
adcs x22, x22, x9
and v26.16b, v26.16b, v4.16b
adc x23, x23, x16
add v22.2d, v22.2d, v1.2d
ldr x3, [x0, #312]
ushr v0.2d, v21.2d, #26
mul x2, x3, x12
and v21.16b, v21.16b, v3.16b
mul x8, x3, x13
add v26.2d, v26.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v25.2d, #25
mul x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
adcs x21, x21, x8
ushr v0.2d, v20.2d, #26
adcs x22, x22, x9
and v20.16b, v20.16b, v3.16b
adcs x23, x23, x16
add v25.2d, v25.2d, v0.2d
adc x24, x10, x10
add v20.2d, v20.2d, v2.2d
umulh x2, x3, x12
shl v0.2d, v2.2d, #1
umulh x8, x3, x13
shl v2.2d, v2.2d, #4
umulh x9, x3, x14
add v20.2d, v20.2d, v0.2d
umulh x16, x3, x15
add v20.2d, v20.2d, v2.2d
adds x21, x21, x2
shl v25.2d, v25.2d, #26
adcs x22, x22, x8
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
adcs x23, x23, x9
add v21.2d, v21.2d, v26.2d
adc x24, x24, x16
shl v27.2d, v27.2d, #26
mul x2, x27, x21
add v22.2d, v22.2d, v27.2d
mul x8, x27, x22
shl v28.2d, v28.2d, #26
mul x9, x27, x23
add v23.2d, v23.2d, v28.2d
mul x16, x27, x24
shl v29.2d, v29.2d, #26
umulh x21, x27, x21
add v24.2d, v24.2d, v29.2d
umulh x22, x27, x22
ldr q5, [x0, #704]
umulh x23, x27, x23
ushr v25.2d, v20.2d, #51
umulh x24, x27, x24
and v20.16b, v20.16b, v5.16b
adds x4, x4, x2
ushr v26.2d, v21.2d, #51
adcs x5, x5, x8
and v21.16b, v21.16b, v5.16b
adcs x6, x6, x9
ushr v27.2d, v22.2d, #51
adcs x7, x7, x16
and v22.16b, v22.16b, v5.16b
adc x24, x24, x10
ushr v28.2d, v23.2d, #51
adds x7, x7, x23
and v23.16b, v23.16b, v5.16b
adc x24, x24, x10
ushr v29.2d, v24.2d, #51
extr x17, x24, x7, #63
and v24.16b, v24.16b, v5.16b
and x7, x7, #0x7fffffffffffffff
add v21.2d, v21.2d, v25.2d
mul x17, x17, x26
add v22.2d, v22.2d, v26.2d
adds x4, x4, x17
add v23.2d, v23.2d, v27.2d
adcs x5, x5, x21
add v24.2d, v24.2d, v28.2d
adcs x6, x6, x22
add v20.2d, v20.2d, v29.2d
adc x7, x7, x10
shl v0.2d, v29.2d, #1
stp x4, x5, [x0, #480]
shl v2.2d, v29.2d, #4
stp x6, x7, [x0, #496]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
trn1 v0.2d, v20.2d, v21.2d
ldp x21, x22, [x0, #480]
trn2 v1.2d, v20.2d, v21.2d
ldp x23, x24, [x0, #496]
str q0, [x0, #1024]
subs x12, x4, x21
str q1, [x0, #1072]
sbcs x13, x5, x22
trn1 v0.2d, v22.2d, v23.2d
sbcs x14, x6, x23
trn2 v1.2d, v22.2d, v23.2d
sbcs x15, x7, x24
str q0, [x0, #1040]
csel x3, x10, x27, hs
str q1, [x0, #1088]
subs x12, x12, x3
trn1 v0.2d, v24.2d, v24.2d
sbcs x13, x13, x10
trn2 v1.2d, v24.2d, v24.2d
sbcs x14, x14, x10
str q0, [x0, #1056]
sbc x15, x15, x10
str q1, [x0, #1104]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
.globl lab_tf43
lab_tf43:
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
mul x2, x3, x12
ushr v21.2d, v25.2d, #13
mul x8, x3, x13
and v21.16b, v21.16b, v30.16b
mul x9, x3, x14
uzp1 v1.4s, v20.4s, v21.4s
mul x16, x3, x15
ushr v20.2d, v25.2d, #38
adds x5, x5, x2
and v21.16b, v26.16b, v30.16b
adcs x6, x6, x8
uzp1 v2.4s, v20.4s, v21.4s
adcs x7, x7, x9
ushr v20.2d, v26.2d, #25
adcs x21, x21, x16
and v20.16b, v20.16b, v31.16b
adc x22, x10, x10
shl v21.2d, v27.2d, #13
umulh x2, x3, x12
sri v21.2d, v26.2d, #51
umulh x8, x3, x13
and v21.16b, v21.16b, v30.16b
umulh x9, x3, x14
uzp1 v3.4s, v20.4s, v21.4s
umulh x16, x3, x15
ushr v20.2d, v27.2d, #12
adds x6, x6, x2
and v20.16b, v20.16b, v31.16b
adcs x7, x7, x8
ushr v21.2d, v27.2d, #38
adcs x21, x21, x9
uzp1 v4.4s, v20.4s, v21.4s
adc x22, x22, x16
ext v5.16b, v0.16b, v0.16b, #8
ldr x3, [x0, #336]
ext v6.16b, v1.16b, v1.16b, #8
mul x2, x3, x12
ext v7.16b, v2.16b, v2.16b, #8
mul x8, x3, x13
ext v8.16b, v3.16b, v3.16b, #8
mul x9, x3, x14
ext v9.16b, v4.16b, v4.16b, #8
mul x16, x3, x15
add v10.4s, v0.4s, v0.4s
adds x6, x6, x2
add v11.4s, v1.4s, v1.4s
adcs x7, x7, x8
add v12.4s, v2.4s, v2.4s
adcs x21, x21, x9
add v13.4s, v3.4s, v3.4s
adcs x22, x22, x16
add v14.4s, v4.4s, v4.4s
adc x23, x10, x10
ldr q31, [x0, #752]
umulh x2, x3, x12
mul v15.4s, v0.4s, v31.4s
umulh x8, x3, x13
mul v16.4s, v1.4s, v31.4s
umulh x9, x3, x14
mul v17.4s, v2.4s, v31.4s
umulh x16, x3, x15
mul v18.4s, v3.4s, v31.4s
adds x7, x7, x2
mul v19.4s, v4.4s, v31.4s
adcs x21, x21, x8
umull2 v20.2d, v10.4s, v19.4s
adcs x22, x22, x9
umlal2 v20.2d, v11.4s, v18.4s
adc x23, x23, x16
umlal2 v20.2d, v2.4s, v17.4s
ldr x3, [x0, #344]
add v20.2d, v20.2d, v20.2d
mul x2, x3, x12
umlal v20.2d, v0.2s, v0.2s
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
umlal v25.2d, v30.2s, v18.2s
umulh x8, x3, x13
umlal2 v25.2d, v30.4s, v18.4s
umulh x9, x3, x14
umull2 v21.2d, v0.4s, v0.4s
umulh x16, x3, x15
umlal2 v21.2d, v11.4s, v19.4s
adds x21, x21, x2
umlal2 v21.2d, v12.4s, v18.4s
adcs x22, x22, x8
add v21.2d, v21.2d, v21.2d
adcs x23, x23, x9
umlal v21.2d, v10.2s, v1.2s
adc x24, x24, x16
umlal v21.2d, v12.2s, v19.2s
mul x2, x27, x21
umlal v21.2d, v3.2s, v18.2s
mul x8, x27, x22
add v30.4s, v5.4s, v5.4s
mul x9, x27, x23
umull v26.2d, v30.2s, v1.2s
mul x16, x27, x24
umlal2 v26.2d, v30.4s, v1.4s
umulh x21, x27, x21
add v30.4s, v7.4s, v7.4s
umulh x22, x27, x22
umlal v26.2d, v30.2s, v19.2s
umulh x23, x27, x23
umlal2 v26.2d, v30.4s, v19.4s
umulh x24, x27, x24
add v30.4s, v8.4s, v8.4s
adds x4, x4, x2
umlal v26.2d, v30.2s, v18.2s
adcs x5, x5, x8
umull2 v22.2d, v10.4s, v1.4s
adcs x6, x6, x9
umlal2 v22.2d, v12.4s, v19.4s
umlal2 v22.2d, v3.4s, v18.4s
adcs x7, x7, x16
add v22.2d, v22.2d, v22.2d
adc x24, x24, x10
umlal v22.2d, v10.2s, v2.2s
adds x7, x7, x23
umlal v22.2d, v1.2s, v1.2s
adc x24, x24, x10
umlal v22.2d, v13.2s, v19.2s
extr x17, x24, x7, #63
add v30.4s, v5.4s, v5.4s
and x7, x7, #0x7fffffffffffffff
umull v27.2d, v30.2s, v2.2s
mul x17, x17, x26
umlal2 v27.2d, v30.4s, v2.4s
adds x4, x4, x17
add v30.4s, v6.4s, v6.4s
adcs x5, x5, x21
umlal v27.2d, v30.2s, v1.2s
adcs x6, x6, x22
add v30.4s, v8.4s, v8.4s
adc x7, x7, x10
umlal v27.2d, v30.2s, v19.2s
stp x4, x5, [x0, #448]
umlal2 v27.2d, v30.4s, v19.4s
stp x6, x7, [x0, #464]
umull2 v23.2d, v10.4s, v2.4s
ldp x12, x13, [x0, #256]
umlal2 v23.2d, v1.4s, v1.4s
ldp x14, x15, [x0, #272]
umlal2 v23.2d, v13.4s, v19.4s
ldr x3, [x0, #288]
add v23.2d, v23.2d, v23.2d
mul x4, x3, x12
umlal v23.2d, v10.2s, v3.2s
mul x5, x3, x13
umlal v23.2d, v11.2s, v2.2s
mul x6, x3, x14
umlal v23.2d, v4.2s, v19.2s
mul x7, x3, x15
add v30.4s, v5.4s, v5.4s
umulh x2, x3, x12
umull v28.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v28.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v6.4s, v6.4s
umulh x16, x3, x15
umlal v28.2d, v30.2s, v2.2s
adds x5, x5, x2
umlal2 v28.2d, v30.4s, v2.4s
adcs x6, x6, x8
add v30.4s, v9.4s, v9.4s
adcs x7, x7, x9
umlal v28.2d, v30.2s, v19.2s
adc x21, x16, x10
umull2 v24.2d, v10.4s, v3.4s
ldr x3, [x0, #296]
umlal2 v24.2d, v11.4s, v2.4s
mul x2, x3, x12
umlal2 v24.2d, v4.4s, v19.4s
mul x8, x3, x13
add v24.2d, v24.2d, v24.2d
mul x9, x3, x14
umlal v24.2d, v10.2s, v4.2s
mul x16, x3, x15
umlal v24.2d, v11.2s, v3.2s
adds x5, x5, x2
umlal v24.2d, v2.2s, v2.2s
adcs x6, x6, x8
add v30.4s, v5.4s, v5.4s
adcs x7, x7, x9
umull v29.2d, v30.2s, v4.2s
adcs x21, x21, x16
umlal2 v29.2d, v30.4s, v4.4s
adc x22, x10, x10
add v30.4s, v6.4s, v6.4s
umulh x2, x3, x12
umlal v29.2d, v30.2s, v3.2s
umulh x8, x3, x13
umlal2 v29.2d, v30.4s, v3.4s
umulh x9, x3, x14
add v30.4s, v7.4s, v7.4s
umulh x16, x3, x15
umlal v29.2d, v30.2s, v2.2s
adds x6, x6, x2
ldr q3, [x0, #720]
adcs x7, x7, x8
ldr q4, [x0, #736]
adcs x21, x21, x9
ushr v2.2d, v29.2d, #25
adc x22, x22, x16
and v29.16b, v29.16b, v4.16b
ldr x3, [x0, #304]
ushr v0.2d, v24.2d, #26
mul x2, x3, x12
and v24.16b, v24.16b, v3.16b
mul x8, x3, x13
add v29.2d, v29.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v28.2d, #25
mul x16, x3, x15
and v28.16b, v28.16b, v4.16b
adds x6, x6, x2
add v24.2d, v24.2d, v1.2d
adcs x7, x7, x8
ushr v0.2d, v23.2d, #26
adcs x21, x21, x9
and v23.16b, v23.16b, v3.16b
adcs x22, x22, x16
add v28.2d, v28.2d, v0.2d
adc x23, x10, x10
ushr v1.2d, v27.2d, #25
umulh x2, x3, x12
and v27.16b, v27.16b, v4.16b
umulh x8, x3, x13
add v23.2d, v23.2d, v1.2d
umulh x9, x3, x14
ushr v0.2d, v22.2d, #26
umulh x16, x3, x15
and v22.16b, v22.16b, v3.16b
adds x7, x7, x2
add v27.2d, v27.2d, v0.2d
adcs x21, x21, x8
ushr v1.2d, v26.2d, #25
adcs x22, x22, x9
and v26.16b, v26.16b, v4.16b
adc x23, x23, x16
add v22.2d, v22.2d, v1.2d
ldr x3, [x0, #312]
ushr v0.2d, v21.2d, #26
mul x2, x3, x12
and v21.16b, v21.16b, v3.16b
mul x8, x3, x13
add v26.2d, v26.2d, v0.2d
mul x9, x3, x14
ushr v1.2d, v25.2d, #25
mul x16, x3, x15
and v25.16b, v25.16b, v4.16b
adds x7, x7, x2
add v21.2d, v21.2d, v1.2d
adcs x21, x21, x8
ushr v0.2d, v20.2d, #26
adcs x22, x22, x9
and v20.16b, v20.16b, v3.16b
adcs x23, x23, x16
add v25.2d, v25.2d, v0.2d
adc x24, x10, x10
add v20.2d, v20.2d, v2.2d
umulh x2, x3, x12
shl v0.2d, v2.2d, #1
umulh x8, x3, x13
shl v2.2d, v2.2d, #4
umulh x9, x3, x14
add v20.2d, v20.2d, v0.2d
umulh x16, x3, x15
add v20.2d, v20.2d, v2.2d
adds x21, x21, x2
shl v25.2d, v25.2d, #26
adcs x22, x22, x8
add v20.2d, v20.2d, v25.2d
shl v26.2d, v26.2d, #26
adcs x23, x23, x9
add v21.2d, v21.2d, v26.2d
adc x24, x24, x16
shl v27.2d, v27.2d, #26
mul x2, x27, x21
add v22.2d, v22.2d, v27.2d
mul x8, x27, x22
shl v28.2d, v28.2d, #26
mul x9, x27, x23
add v23.2d, v23.2d, v28.2d
mul x16, x27, x24
shl v29.2d, v29.2d, #26
umulh x21, x27, x21
add v24.2d, v24.2d, v29.2d
umulh x22, x27, x22
ldr q5, [x0, #704]
umulh x23, x27, x23
ushr v25.2d, v20.2d, #51
umulh x24, x27, x24
and v20.16b, v20.16b, v5.16b
adds x4, x4, x2
ushr v26.2d, v21.2d, #51
adcs x5, x5, x8
and v21.16b, v21.16b, v5.16b
adcs x6, x6, x9
ushr v27.2d, v22.2d, #51
adcs x7, x7, x16
and v22.16b, v22.16b, v5.16b
adc x24, x24, x10
ushr v28.2d, v23.2d, #51
adds x7, x7, x23
and v23.16b, v23.16b, v5.16b
adc x24, x24, x10
ushr v29.2d, v24.2d, #51
extr x17, x24, x7, #63
and v24.16b, v24.16b, v5.16b
and x7, x7, #0x7fffffffffffffff
add v21.2d, v21.2d, v25.2d
mul x17, x17, x26
add v22.2d, v22.2d, v26.2d
adds x4, x4, x17
add v23.2d, v23.2d, v27.2d
adcs x5, x5, x21
add v24.2d, v24.2d, v28.2d
adcs x6, x6, x22
add v20.2d, v20.2d, v29.2d
adc x7, x7, x10
shl v0.2d, v29.2d, #1
stp x4, x5, [x0, #480]
shl v2.2d, v29.2d, #4
stp x6, x7, [x0, #496]
add v20.2d, v20.2d, v0.2d
ldp x4, x5, [x0, #448]
add v20.2d, v20.2d, v2.2d
ldp x6, x7, [x0, #464]
trn1 v0.2d, v20.2d, v21.2d
ldp x21, x22, [x0, #480]
trn2 v1.2d, v20.2d, v21.2d
ldp x23, x24, [x0, #496]
str q0, [x0, #1024]
subs x12, x4, x21
str q1, [x0, #1072]
sbcs x13, x5, x22
trn1 v0.2d, v22.2d, v23.2d
sbcs x14, x6, x23
trn2 v1.2d, v22.2d, v23.2d
sbcs x15, x7, x24
str q0, [x0, #1040]
csel x3, x10, x27, hs
str q1, [x0, #1088]
subs x12, x12, x3
trn1 v0.2d, v24.2d, v24.2d
sbcs x13, x13, x10
trn2 v1.2d, v24.2d, v24.2d
sbcs x14, x14, x10
str q0, [x0, #1056]
sbc x15, x15, x10
str q1, [x0, #1104]
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
sbcs x14, x6, x23
sbcs x15, x7, x24
csel x3, x10, x27, hs
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
fn lab_clk_add100(p: *mut u64, n: u64);fn lab_h2(p: *mut u64, n: u64);fn lab_ta(p: *mut u64, n: u64);fn lab_tb(p: *mut u64, n: u64);fn lab_tc(p: *mut u64, n: u64);fn lab_td(p: *mut u64, n: u64);fn lab_te(p: *mut u64, n: u64);fn lab_tf(p: *mut u64, n: u64);fn lab_tg(p: *mut u64, n: u64);fn lab_th(p: *mut u64, n: u64);fn lab_ti(p: *mut u64, n: u64);fn lab_tj(p: *mut u64, n: u64);fn lab_ta32(p: *mut u64, n: u64);fn lab_ta43(p: *mut u64, n: u64);fn lab_ta2(p: *mut u64, n: u64);fn lab_tak(p: *mut u64, n: u64);fn lab_tan(p: *mut u64, n: u64);fn lab_tj43(p: *mut u64, n: u64);fn lab_tf43(p: *mut u64, n: u64);}
pub fn bench(c: &mut Criterion) { let mut buf = vec![0x1234_5678_9abc_def1u64; 2048]; let p = buf.as_mut_ptr();
let mut g = c.benchmark_group("lab_clk_add100"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_clk_add100(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_h2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_h2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ta"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ta(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tb"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tb(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tc"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tc(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_td"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_td(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_te"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_te(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tf"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tf(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tg"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tg(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_th"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_th(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ti"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ti(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tj"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tj(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ta32"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ta32(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ta43"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ta43(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_ta2"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_ta2(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tak"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tak(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tan"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tan(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tj43"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tj43(p, 100) })); g.finish();
let mut g = c.benchmark_group("lab_tf43"); g.bench(BenchmarkId::new(VG, 1), |b| b.iter(|| unsafe { lab_tf43(p, 100) })); g.finish();
}