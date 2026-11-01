// The functions of `src/internal/vg_argon2_compress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_compress:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #0]
	str q0, [x3, #1024]
	ldr q0, [x0, #16]
	ldr q1, [x1, #16]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #16]
	str q0, [x3, #1040]
	ldr q0, [x0, #32]
	ldr q1, [x1, #32]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #32]
	str q0, [x3, #1056]
	ldr q0, [x0, #48]
	ldr q1, [x1, #48]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #48]
	str q0, [x3, #1072]
	ldr q0, [x0, #64]
	ldr q1, [x1, #64]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #64]
	str q0, [x3, #1088]
	ldr q0, [x0, #80]
	ldr q1, [x1, #80]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #80]
	str q0, [x3, #1104]
	ldr q0, [x0, #96]
	ldr q1, [x1, #96]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #96]
	str q0, [x3, #1120]
	ldr q0, [x0, #112]
	ldr q1, [x1, #112]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #112]
	str q0, [x3, #1136]
	ldr q0, [x0, #128]
	ldr q1, [x1, #128]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #128]
	str q0, [x3, #1152]
	ldr q0, [x0, #144]
	ldr q1, [x1, #144]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #144]
	str q0, [x3, #1168]
	ldr q0, [x0, #160]
	ldr q1, [x1, #160]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #160]
	str q0, [x3, #1184]
	ldr q0, [x0, #176]
	ldr q1, [x1, #176]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #176]
	str q0, [x3, #1200]
	ldr q0, [x0, #192]
	ldr q1, [x1, #192]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #192]
	str q0, [x3, #1216]
	ldr q0, [x0, #208]
	ldr q1, [x1, #208]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #208]
	str q0, [x3, #1232]
	ldr q0, [x0, #224]
	ldr q1, [x1, #224]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #224]
	str q0, [x3, #1248]
	ldr q0, [x0, #240]
	ldr q1, [x1, #240]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #240]
	str q0, [x3, #1264]
	ldr q0, [x0, #256]
	ldr q1, [x1, #256]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #256]
	str q0, [x3, #1280]
	ldr q0, [x0, #272]
	ldr q1, [x1, #272]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #272]
	str q0, [x3, #1296]
	ldr q0, [x0, #288]
	ldr q1, [x1, #288]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #288]
	str q0, [x3, #1312]
	ldr q0, [x0, #304]
	ldr q1, [x1, #304]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #304]
	str q0, [x3, #1328]
	ldr q0, [x0, #320]
	ldr q1, [x1, #320]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #320]
	str q0, [x3, #1344]
	ldr q0, [x0, #336]
	ldr q1, [x1, #336]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #336]
	str q0, [x3, #1360]
	ldr q0, [x0, #352]
	ldr q1, [x1, #352]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #352]
	str q0, [x3, #1376]
	ldr q0, [x0, #368]
	ldr q1, [x1, #368]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #368]
	str q0, [x3, #1392]
	ldr q0, [x0, #384]
	ldr q1, [x1, #384]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #384]
	str q0, [x3, #1408]
	ldr q0, [x0, #400]
	ldr q1, [x1, #400]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #400]
	str q0, [x3, #1424]
	ldr q0, [x0, #416]
	ldr q1, [x1, #416]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #416]
	str q0, [x3, #1440]
	ldr q0, [x0, #432]
	ldr q1, [x1, #432]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #432]
	str q0, [x3, #1456]
	ldr q0, [x0, #448]
	ldr q1, [x1, #448]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #448]
	str q0, [x3, #1472]
	ldr q0, [x0, #464]
	ldr q1, [x1, #464]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #464]
	str q0, [x3, #1488]
	ldr q0, [x0, #480]
	ldr q1, [x1, #480]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #480]
	str q0, [x3, #1504]
	ldr q0, [x0, #496]
	ldr q1, [x1, #496]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #496]
	str q0, [x3, #1520]
	ldr q0, [x0, #512]
	ldr q1, [x1, #512]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #512]
	str q0, [x3, #1536]
	ldr q0, [x0, #528]
	ldr q1, [x1, #528]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #528]
	str q0, [x3, #1552]
	ldr q0, [x0, #544]
	ldr q1, [x1, #544]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #544]
	str q0, [x3, #1568]
	ldr q0, [x0, #560]
	ldr q1, [x1, #560]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #560]
	str q0, [x3, #1584]
	ldr q0, [x0, #576]
	ldr q1, [x1, #576]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #576]
	str q0, [x3, #1600]
	ldr q0, [x0, #592]
	ldr q1, [x1, #592]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #592]
	str q0, [x3, #1616]
	ldr q0, [x0, #608]
	ldr q1, [x1, #608]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #608]
	str q0, [x3, #1632]
	ldr q0, [x0, #624]
	ldr q1, [x1, #624]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #624]
	str q0, [x3, #1648]
	ldr q0, [x0, #640]
	ldr q1, [x1, #640]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #640]
	str q0, [x3, #1664]
	ldr q0, [x0, #656]
	ldr q1, [x1, #656]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #656]
	str q0, [x3, #1680]
	ldr q0, [x0, #672]
	ldr q1, [x1, #672]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #672]
	str q0, [x3, #1696]
	ldr q0, [x0, #688]
	ldr q1, [x1, #688]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #688]
	str q0, [x3, #1712]
	ldr q0, [x0, #704]
	ldr q1, [x1, #704]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #704]
	str q0, [x3, #1728]
	ldr q0, [x0, #720]
	ldr q1, [x1, #720]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #720]
	str q0, [x3, #1744]
	ldr q0, [x0, #736]
	ldr q1, [x1, #736]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #736]
	str q0, [x3, #1760]
	ldr q0, [x0, #752]
	ldr q1, [x1, #752]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #752]
	str q0, [x3, #1776]
	ldr q0, [x0, #768]
	ldr q1, [x1, #768]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #768]
	str q0, [x3, #1792]
	ldr q0, [x0, #784]
	ldr q1, [x1, #784]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #784]
	str q0, [x3, #1808]
	ldr q0, [x0, #800]
	ldr q1, [x1, #800]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #800]
	str q0, [x3, #1824]
	ldr q0, [x0, #816]
	ldr q1, [x1, #816]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #816]
	str q0, [x3, #1840]
	ldr q0, [x0, #832]
	ldr q1, [x1, #832]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #832]
	str q0, [x3, #1856]
	ldr q0, [x0, #848]
	ldr q1, [x1, #848]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #848]
	str q0, [x3, #1872]
	ldr q0, [x0, #864]
	ldr q1, [x1, #864]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #864]
	str q0, [x3, #1888]
	ldr q0, [x0, #880]
	ldr q1, [x1, #880]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #880]
	str q0, [x3, #1904]
	ldr q0, [x0, #896]
	ldr q1, [x1, #896]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #896]
	str q0, [x3, #1920]
	ldr q0, [x0, #912]
	ldr q1, [x1, #912]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #912]
	str q0, [x3, #1936]
	ldr q0, [x0, #928]
	ldr q1, [x1, #928]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #928]
	str q0, [x3, #1952]
	ldr q0, [x0, #944]
	ldr q1, [x1, #944]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #944]
	str q0, [x3, #1968]
	ldr q0, [x0, #960]
	ldr q1, [x1, #960]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #960]
	str q0, [x3, #1984]
	ldr q0, [x0, #976]
	ldr q1, [x1, #976]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #976]
	str q0, [x3, #2000]
	ldr q0, [x0, #992]
	ldr q1, [x1, #992]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #992]
	str q0, [x3, #2016]
	ldr q0, [x0, #1008]
	ldr q1, [x1, #1008]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #1008]
	str q0, [x3, #2032]
	dup v16.2d, x2
	ldr x0, [x3, #1024]
	ldr x1, [x3, #1032]
	ldr x2, [x3, #1040]
	ldr x4, [x3, #1048]
	ldr x5, [x3, #1056]
	ldr x6, [x3, #1064]
	ldr x7, [x3, #1072]
	ldr x8, [x3, #1080]
	ldr x9, [x3, #1088]
	ldr x10, [x3, #1096]
	ldr x11, [x3, #1104]
	ldr x12, [x3, #1112]
	ldr x13, [x3, #1120]
	ldr x14, [x3, #1128]
	ldr x15, [x3, #1136]
	ldr x16, [x3, #1144]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1024]
	str x1, [x3, #1032]
	str x2, [x3, #1040]
	str x4, [x3, #1048]
	str x5, [x3, #1056]
	str x6, [x3, #1064]
	str x7, [x3, #1072]
	str x8, [x3, #1080]
	str x9, [x3, #1088]
	str x10, [x3, #1096]
	str x11, [x3, #1104]
	str x12, [x3, #1112]
	str x13, [x3, #1120]
	str x14, [x3, #1128]
	str x15, [x3, #1136]
	str x16, [x3, #1144]
	ldr x0, [x3, #1152]
	ldr x1, [x3, #1160]
	ldr x2, [x3, #1168]
	ldr x4, [x3, #1176]
	ldr x5, [x3, #1184]
	ldr x6, [x3, #1192]
	ldr x7, [x3, #1200]
	ldr x8, [x3, #1208]
	ldr x9, [x3, #1216]
	ldr x10, [x3, #1224]
	ldr x11, [x3, #1232]
	ldr x12, [x3, #1240]
	ldr x13, [x3, #1248]
	ldr x14, [x3, #1256]
	ldr x15, [x3, #1264]
	ldr x16, [x3, #1272]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1152]
	str x1, [x3, #1160]
	str x2, [x3, #1168]
	str x4, [x3, #1176]
	str x5, [x3, #1184]
	str x6, [x3, #1192]
	str x7, [x3, #1200]
	str x8, [x3, #1208]
	str x9, [x3, #1216]
	str x10, [x3, #1224]
	str x11, [x3, #1232]
	str x12, [x3, #1240]
	str x13, [x3, #1248]
	str x14, [x3, #1256]
	str x15, [x3, #1264]
	str x16, [x3, #1272]
	ldr x0, [x3, #1280]
	ldr x1, [x3, #1288]
	ldr x2, [x3, #1296]
	ldr x4, [x3, #1304]
	ldr x5, [x3, #1312]
	ldr x6, [x3, #1320]
	ldr x7, [x3, #1328]
	ldr x8, [x3, #1336]
	ldr x9, [x3, #1344]
	ldr x10, [x3, #1352]
	ldr x11, [x3, #1360]
	ldr x12, [x3, #1368]
	ldr x13, [x3, #1376]
	ldr x14, [x3, #1384]
	ldr x15, [x3, #1392]
	ldr x16, [x3, #1400]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1280]
	str x1, [x3, #1288]
	str x2, [x3, #1296]
	str x4, [x3, #1304]
	str x5, [x3, #1312]
	str x6, [x3, #1320]
	str x7, [x3, #1328]
	str x8, [x3, #1336]
	str x9, [x3, #1344]
	str x10, [x3, #1352]
	str x11, [x3, #1360]
	str x12, [x3, #1368]
	str x13, [x3, #1376]
	str x14, [x3, #1384]
	str x15, [x3, #1392]
	str x16, [x3, #1400]
	ldr x0, [x3, #1408]
	ldr x1, [x3, #1416]
	ldr x2, [x3, #1424]
	ldr x4, [x3, #1432]
	ldr x5, [x3, #1440]
	ldr x6, [x3, #1448]
	ldr x7, [x3, #1456]
	ldr x8, [x3, #1464]
	ldr x9, [x3, #1472]
	ldr x10, [x3, #1480]
	ldr x11, [x3, #1488]
	ldr x12, [x3, #1496]
	ldr x13, [x3, #1504]
	ldr x14, [x3, #1512]
	ldr x15, [x3, #1520]
	ldr x16, [x3, #1528]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1408]
	str x1, [x3, #1416]
	str x2, [x3, #1424]
	str x4, [x3, #1432]
	str x5, [x3, #1440]
	str x6, [x3, #1448]
	str x7, [x3, #1456]
	str x8, [x3, #1464]
	str x9, [x3, #1472]
	str x10, [x3, #1480]
	str x11, [x3, #1488]
	str x12, [x3, #1496]
	str x13, [x3, #1504]
	str x14, [x3, #1512]
	str x15, [x3, #1520]
	str x16, [x3, #1528]
	ldr x0, [x3, #1536]
	ldr x1, [x3, #1544]
	ldr x2, [x3, #1552]
	ldr x4, [x3, #1560]
	ldr x5, [x3, #1568]
	ldr x6, [x3, #1576]
	ldr x7, [x3, #1584]
	ldr x8, [x3, #1592]
	ldr x9, [x3, #1600]
	ldr x10, [x3, #1608]
	ldr x11, [x3, #1616]
	ldr x12, [x3, #1624]
	ldr x13, [x3, #1632]
	ldr x14, [x3, #1640]
	ldr x15, [x3, #1648]
	ldr x16, [x3, #1656]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1536]
	str x1, [x3, #1544]
	str x2, [x3, #1552]
	str x4, [x3, #1560]
	str x5, [x3, #1568]
	str x6, [x3, #1576]
	str x7, [x3, #1584]
	str x8, [x3, #1592]
	str x9, [x3, #1600]
	str x10, [x3, #1608]
	str x11, [x3, #1616]
	str x12, [x3, #1624]
	str x13, [x3, #1632]
	str x14, [x3, #1640]
	str x15, [x3, #1648]
	str x16, [x3, #1656]
	ldr x0, [x3, #1664]
	ldr x1, [x3, #1672]
	ldr x2, [x3, #1680]
	ldr x4, [x3, #1688]
	ldr x5, [x3, #1696]
	ldr x6, [x3, #1704]
	ldr x7, [x3, #1712]
	ldr x8, [x3, #1720]
	ldr x9, [x3, #1728]
	ldr x10, [x3, #1736]
	ldr x11, [x3, #1744]
	ldr x12, [x3, #1752]
	ldr x13, [x3, #1760]
	ldr x14, [x3, #1768]
	ldr x15, [x3, #1776]
	ldr x16, [x3, #1784]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1664]
	str x1, [x3, #1672]
	str x2, [x3, #1680]
	str x4, [x3, #1688]
	str x5, [x3, #1696]
	str x6, [x3, #1704]
	str x7, [x3, #1712]
	str x8, [x3, #1720]
	str x9, [x3, #1728]
	str x10, [x3, #1736]
	str x11, [x3, #1744]
	str x12, [x3, #1752]
	str x13, [x3, #1760]
	str x14, [x3, #1768]
	str x15, [x3, #1776]
	str x16, [x3, #1784]
	ldr x0, [x3, #1792]
	ldr x1, [x3, #1800]
	ldr x2, [x3, #1808]
	ldr x4, [x3, #1816]
	ldr x5, [x3, #1824]
	ldr x6, [x3, #1832]
	ldr x7, [x3, #1840]
	ldr x8, [x3, #1848]
	ldr x9, [x3, #1856]
	ldr x10, [x3, #1864]
	ldr x11, [x3, #1872]
	ldr x12, [x3, #1880]
	ldr x13, [x3, #1888]
	ldr x14, [x3, #1896]
	ldr x15, [x3, #1904]
	ldr x16, [x3, #1912]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1792]
	str x1, [x3, #1800]
	str x2, [x3, #1808]
	str x4, [x3, #1816]
	str x5, [x3, #1824]
	str x6, [x3, #1832]
	str x7, [x3, #1840]
	str x8, [x3, #1848]
	str x9, [x3, #1856]
	str x10, [x3, #1864]
	str x11, [x3, #1872]
	str x12, [x3, #1880]
	str x13, [x3, #1888]
	str x14, [x3, #1896]
	str x15, [x3, #1904]
	str x16, [x3, #1912]
	ldr x0, [x3, #1920]
	ldr x1, [x3, #1928]
	ldr x2, [x3, #1936]
	ldr x4, [x3, #1944]
	ldr x5, [x3, #1952]
	ldr x6, [x3, #1960]
	ldr x7, [x3, #1968]
	ldr x8, [x3, #1976]
	ldr x9, [x3, #1984]
	ldr x10, [x3, #1992]
	ldr x11, [x3, #2000]
	ldr x12, [x3, #2008]
	ldr x13, [x3, #2016]
	ldr x14, [x3, #2024]
	ldr x15, [x3, #2032]
	ldr x16, [x3, #2040]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1920]
	str x1, [x3, #1928]
	str x2, [x3, #1936]
	str x4, [x3, #1944]
	str x5, [x3, #1952]
	str x6, [x3, #1960]
	str x7, [x3, #1968]
	str x8, [x3, #1976]
	str x9, [x3, #1984]
	str x10, [x3, #1992]
	str x11, [x3, #2000]
	str x12, [x3, #2008]
	str x13, [x3, #2016]
	str x14, [x3, #2024]
	str x15, [x3, #2032]
	str x16, [x3, #2040]
	ldr x0, [x3, #1024]
	ldr x1, [x3, #1032]
	ldr x2, [x3, #1152]
	ldr x4, [x3, #1160]
	ldr x5, [x3, #1280]
	ldr x6, [x3, #1288]
	ldr x7, [x3, #1408]
	ldr x8, [x3, #1416]
	ldr x9, [x3, #1536]
	ldr x10, [x3, #1544]
	ldr x11, [x3, #1664]
	ldr x12, [x3, #1672]
	ldr x13, [x3, #1792]
	ldr x14, [x3, #1800]
	ldr x15, [x3, #1920]
	ldr x16, [x3, #1928]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1024]
	str x1, [x3, #1032]
	str x2, [x3, #1152]
	str x4, [x3, #1160]
	str x5, [x3, #1280]
	str x6, [x3, #1288]
	str x7, [x3, #1408]
	str x8, [x3, #1416]
	str x9, [x3, #1536]
	str x10, [x3, #1544]
	str x11, [x3, #1664]
	str x12, [x3, #1672]
	str x13, [x3, #1792]
	str x14, [x3, #1800]
	str x15, [x3, #1920]
	str x16, [x3, #1928]
	ldr x0, [x3, #1040]
	ldr x1, [x3, #1048]
	ldr x2, [x3, #1168]
	ldr x4, [x3, #1176]
	ldr x5, [x3, #1296]
	ldr x6, [x3, #1304]
	ldr x7, [x3, #1424]
	ldr x8, [x3, #1432]
	ldr x9, [x3, #1552]
	ldr x10, [x3, #1560]
	ldr x11, [x3, #1680]
	ldr x12, [x3, #1688]
	ldr x13, [x3, #1808]
	ldr x14, [x3, #1816]
	ldr x15, [x3, #1936]
	ldr x16, [x3, #1944]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1040]
	str x1, [x3, #1048]
	str x2, [x3, #1168]
	str x4, [x3, #1176]
	str x5, [x3, #1296]
	str x6, [x3, #1304]
	str x7, [x3, #1424]
	str x8, [x3, #1432]
	str x9, [x3, #1552]
	str x10, [x3, #1560]
	str x11, [x3, #1680]
	str x12, [x3, #1688]
	str x13, [x3, #1808]
	str x14, [x3, #1816]
	str x15, [x3, #1936]
	str x16, [x3, #1944]
	ldr x0, [x3, #1056]
	ldr x1, [x3, #1064]
	ldr x2, [x3, #1184]
	ldr x4, [x3, #1192]
	ldr x5, [x3, #1312]
	ldr x6, [x3, #1320]
	ldr x7, [x3, #1440]
	ldr x8, [x3, #1448]
	ldr x9, [x3, #1568]
	ldr x10, [x3, #1576]
	ldr x11, [x3, #1696]
	ldr x12, [x3, #1704]
	ldr x13, [x3, #1824]
	ldr x14, [x3, #1832]
	ldr x15, [x3, #1952]
	ldr x16, [x3, #1960]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1056]
	str x1, [x3, #1064]
	str x2, [x3, #1184]
	str x4, [x3, #1192]
	str x5, [x3, #1312]
	str x6, [x3, #1320]
	str x7, [x3, #1440]
	str x8, [x3, #1448]
	str x9, [x3, #1568]
	str x10, [x3, #1576]
	str x11, [x3, #1696]
	str x12, [x3, #1704]
	str x13, [x3, #1824]
	str x14, [x3, #1832]
	str x15, [x3, #1952]
	str x16, [x3, #1960]
	ldr x0, [x3, #1072]
	ldr x1, [x3, #1080]
	ldr x2, [x3, #1200]
	ldr x4, [x3, #1208]
	ldr x5, [x3, #1328]
	ldr x6, [x3, #1336]
	ldr x7, [x3, #1456]
	ldr x8, [x3, #1464]
	ldr x9, [x3, #1584]
	ldr x10, [x3, #1592]
	ldr x11, [x3, #1712]
	ldr x12, [x3, #1720]
	ldr x13, [x3, #1840]
	ldr x14, [x3, #1848]
	ldr x15, [x3, #1968]
	ldr x16, [x3, #1976]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1072]
	str x1, [x3, #1080]
	str x2, [x3, #1200]
	str x4, [x3, #1208]
	str x5, [x3, #1328]
	str x6, [x3, #1336]
	str x7, [x3, #1456]
	str x8, [x3, #1464]
	str x9, [x3, #1584]
	str x10, [x3, #1592]
	str x11, [x3, #1712]
	str x12, [x3, #1720]
	str x13, [x3, #1840]
	str x14, [x3, #1848]
	str x15, [x3, #1968]
	str x16, [x3, #1976]
	ldr x0, [x3, #1088]
	ldr x1, [x3, #1096]
	ldr x2, [x3, #1216]
	ldr x4, [x3, #1224]
	ldr x5, [x3, #1344]
	ldr x6, [x3, #1352]
	ldr x7, [x3, #1472]
	ldr x8, [x3, #1480]
	ldr x9, [x3, #1600]
	ldr x10, [x3, #1608]
	ldr x11, [x3, #1728]
	ldr x12, [x3, #1736]
	ldr x13, [x3, #1856]
	ldr x14, [x3, #1864]
	ldr x15, [x3, #1984]
	ldr x16, [x3, #1992]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1088]
	str x1, [x3, #1096]
	str x2, [x3, #1216]
	str x4, [x3, #1224]
	str x5, [x3, #1344]
	str x6, [x3, #1352]
	str x7, [x3, #1472]
	str x8, [x3, #1480]
	str x9, [x3, #1600]
	str x10, [x3, #1608]
	str x11, [x3, #1728]
	str x12, [x3, #1736]
	str x13, [x3, #1856]
	str x14, [x3, #1864]
	str x15, [x3, #1984]
	str x16, [x3, #1992]
	ldr x0, [x3, #1104]
	ldr x1, [x3, #1112]
	ldr x2, [x3, #1232]
	ldr x4, [x3, #1240]
	ldr x5, [x3, #1360]
	ldr x6, [x3, #1368]
	ldr x7, [x3, #1488]
	ldr x8, [x3, #1496]
	ldr x9, [x3, #1616]
	ldr x10, [x3, #1624]
	ldr x11, [x3, #1744]
	ldr x12, [x3, #1752]
	ldr x13, [x3, #1872]
	ldr x14, [x3, #1880]
	ldr x15, [x3, #2000]
	ldr x16, [x3, #2008]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1104]
	str x1, [x3, #1112]
	str x2, [x3, #1232]
	str x4, [x3, #1240]
	str x5, [x3, #1360]
	str x6, [x3, #1368]
	str x7, [x3, #1488]
	str x8, [x3, #1496]
	str x9, [x3, #1616]
	str x10, [x3, #1624]
	str x11, [x3, #1744]
	str x12, [x3, #1752]
	str x13, [x3, #1872]
	str x14, [x3, #1880]
	str x15, [x3, #2000]
	str x16, [x3, #2008]
	ldr x0, [x3, #1120]
	ldr x1, [x3, #1128]
	ldr x2, [x3, #1248]
	ldr x4, [x3, #1256]
	ldr x5, [x3, #1376]
	ldr x6, [x3, #1384]
	ldr x7, [x3, #1504]
	ldr x8, [x3, #1512]
	ldr x9, [x3, #1632]
	ldr x10, [x3, #1640]
	ldr x11, [x3, #1760]
	ldr x12, [x3, #1768]
	ldr x13, [x3, #1888]
	ldr x14, [x3, #1896]
	ldr x15, [x3, #2016]
	ldr x16, [x3, #2024]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1120]
	str x1, [x3, #1128]
	str x2, [x3, #1248]
	str x4, [x3, #1256]
	str x5, [x3, #1376]
	str x6, [x3, #1384]
	str x7, [x3, #1504]
	str x8, [x3, #1512]
	str x9, [x3, #1632]
	str x10, [x3, #1640]
	str x11, [x3, #1760]
	str x12, [x3, #1768]
	str x13, [x3, #1888]
	str x14, [x3, #1896]
	str x15, [x3, #2016]
	str x16, [x3, #2024]
	ldr x0, [x3, #1136]
	ldr x1, [x3, #1144]
	ldr x2, [x3, #1264]
	ldr x4, [x3, #1272]
	ldr x5, [x3, #1392]
	ldr x6, [x3, #1400]
	ldr x7, [x3, #1520]
	ldr x8, [x3, #1528]
	ldr x9, [x3, #1648]
	ldr x10, [x3, #1656]
	ldr x11, [x3, #1776]
	ldr x12, [x3, #1784]
	ldr x13, [x3, #1904]
	ldr x14, [x3, #1912]
	ldr x15, [x3, #2032]
	ldr x16, [x3, #2040]
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #32
	eor x14, x14, x1
	ror x14, x14, #32
	eor x15, x15, x2
	ror x15, x15, #32
	eor x16, x16, x4
	ror x16, x16, #32
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #24
	eor x6, x6, x10
	ror x6, x6, #24
	eor x7, x7, x11
	ror x7, x7, #24
	eor x8, x8, x12
	ror x8, x8, #24
	umaddl x17, w0, w5, x5
	umaddl x0, w0, w5, x0
	add x0, x0, x17
	umull x17, w1, w6
	add x1, x1, x6
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w7, x7
	umaddl x2, w2, w7, x2
	add x2, x2, x17
	umull x17, w4, w8
	add x4, x4, x8
	add x4, x4, x17
	add x4, x4, x17
	eor x13, x13, x0
	ror x13, x13, #16
	eor x14, x14, x1
	ror x14, x14, #16
	eor x15, x15, x2
	ror x15, x15, #16
	eor x16, x16, x4
	ror x16, x16, #16
	umaddl x17, w9, w13, x13
	umaddl x9, w9, w13, x9
	add x9, x9, x17
	umull x17, w10, w14
	add x10, x10, x14
	add x10, x10, x17
	add x10, x10, x17
	umaddl x17, w11, w15, x15
	umaddl x11, w11, w15, x11
	add x11, x11, x17
	umull x17, w12, w16
	add x12, x12, x16
	add x12, x12, x17
	add x12, x12, x17
	eor x5, x5, x9
	ror x5, x5, #63
	eor x6, x6, x10
	ror x6, x6, #63
	eor x7, x7, x11
	ror x7, x7, #63
	eor x8, x8, x12
	ror x8, x8, #63
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #32
	eor x13, x13, x1
	ror x13, x13, #32
	eor x14, x14, x2
	ror x14, x14, #32
	eor x15, x15, x4
	ror x15, x15, #32
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #24
	eor x7, x7, x12
	ror x7, x7, #24
	eor x8, x8, x9
	ror x8, x8, #24
	eor x5, x5, x10
	ror x5, x5, #24
	umaddl x17, w0, w6, x6
	umaddl x0, w0, w6, x0
	add x0, x0, x17
	umull x17, w1, w7
	add x1, x1, x7
	add x1, x1, x17
	add x1, x1, x17
	umaddl x17, w2, w8, x8
	umaddl x2, w2, w8, x2
	add x2, x2, x17
	umull x17, w4, w5
	add x4, x4, x5
	add x4, x4, x17
	add x4, x4, x17
	eor x16, x16, x0
	ror x16, x16, #16
	eor x13, x13, x1
	ror x13, x13, #16
	eor x14, x14, x2
	ror x14, x14, #16
	eor x15, x15, x4
	ror x15, x15, #16
	umaddl x17, w11, w16, x16
	umaddl x11, w11, w16, x11
	add x11, x11, x17
	umull x17, w12, w13
	add x12, x12, x13
	add x12, x12, x17
	add x12, x12, x17
	umaddl x17, w9, w14, x14
	umaddl x9, w9, w14, x9
	add x9, x9, x17
	umull x17, w10, w15
	add x10, x10, x15
	add x10, x10, x17
	add x10, x10, x17
	eor x6, x6, x11
	ror x6, x6, #63
	eor x7, x7, x12
	ror x7, x7, #63
	eor x8, x8, x9
	ror x8, x8, #63
	eor x5, x5, x10
	ror x5, x5, #63
	str x0, [x3, #1136]
	str x1, [x3, #1144]
	str x2, [x3, #1264]
	str x4, [x3, #1272]
	str x5, [x3, #1392]
	str x6, [x3, #1400]
	str x7, [x3, #1520]
	str x8, [x3, #1528]
	str x9, [x3, #1648]
	str x10, [x3, #1656]
	str x11, [x3, #1776]
	str x12, [x3, #1784]
	str x13, [x3, #1904]
	str x14, [x3, #1912]
	str x15, [x3, #2032]
	str x16, [x3, #2040]
	umov x2, v16.d[0]
	ldr q0, [x3, #1024]
	ldr q1, [x3, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #0]
	ldr q0, [x3, #1040]
	ldr q1, [x3, #16]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #16]
	ldr q0, [x3, #1056]
	ldr q1, [x3, #32]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #32]
	ldr q0, [x3, #1072]
	ldr q1, [x3, #48]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #48]
	ldr q0, [x3, #1088]
	ldr q1, [x3, #64]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #64]
	ldr q0, [x3, #1104]
	ldr q1, [x3, #80]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #80]
	ldr q0, [x3, #1120]
	ldr q1, [x3, #96]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #96]
	ldr q0, [x3, #1136]
	ldr q1, [x3, #112]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #112]
	ldr q0, [x3, #1152]
	ldr q1, [x3, #128]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #128]
	ldr q0, [x3, #1168]
	ldr q1, [x3, #144]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #144]
	ldr q0, [x3, #1184]
	ldr q1, [x3, #160]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #160]
	ldr q0, [x3, #1200]
	ldr q1, [x3, #176]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #176]
	ldr q0, [x3, #1216]
	ldr q1, [x3, #192]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #192]
	ldr q0, [x3, #1232]
	ldr q1, [x3, #208]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #208]
	ldr q0, [x3, #1248]
	ldr q1, [x3, #224]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #224]
	ldr q0, [x3, #1264]
	ldr q1, [x3, #240]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #240]
	ldr q0, [x3, #1280]
	ldr q1, [x3, #256]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #256]
	ldr q0, [x3, #1296]
	ldr q1, [x3, #272]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #272]
	ldr q0, [x3, #1312]
	ldr q1, [x3, #288]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #288]
	ldr q0, [x3, #1328]
	ldr q1, [x3, #304]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #304]
	ldr q0, [x3, #1344]
	ldr q1, [x3, #320]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #320]
	ldr q0, [x3, #1360]
	ldr q1, [x3, #336]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #336]
	ldr q0, [x3, #1376]
	ldr q1, [x3, #352]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #352]
	ldr q0, [x3, #1392]
	ldr q1, [x3, #368]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #368]
	ldr q0, [x3, #1408]
	ldr q1, [x3, #384]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #384]
	ldr q0, [x3, #1424]
	ldr q1, [x3, #400]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #400]
	ldr q0, [x3, #1440]
	ldr q1, [x3, #416]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #416]
	ldr q0, [x3, #1456]
	ldr q1, [x3, #432]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #432]
	ldr q0, [x3, #1472]
	ldr q1, [x3, #448]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #448]
	ldr q0, [x3, #1488]
	ldr q1, [x3, #464]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #464]
	ldr q0, [x3, #1504]
	ldr q1, [x3, #480]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #480]
	ldr q0, [x3, #1520]
	ldr q1, [x3, #496]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #496]
	ldr q0, [x3, #1536]
	ldr q1, [x3, #512]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #512]
	ldr q0, [x3, #1552]
	ldr q1, [x3, #528]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #528]
	ldr q0, [x3, #1568]
	ldr q1, [x3, #544]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #544]
	ldr q0, [x3, #1584]
	ldr q1, [x3, #560]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #560]
	ldr q0, [x3, #1600]
	ldr q1, [x3, #576]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #576]
	ldr q0, [x3, #1616]
	ldr q1, [x3, #592]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #592]
	ldr q0, [x3, #1632]
	ldr q1, [x3, #608]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #608]
	ldr q0, [x3, #1648]
	ldr q1, [x3, #624]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #624]
	ldr q0, [x3, #1664]
	ldr q1, [x3, #640]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #640]
	ldr q0, [x3, #1680]
	ldr q1, [x3, #656]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #656]
	ldr q0, [x3, #1696]
	ldr q1, [x3, #672]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #672]
	ldr q0, [x3, #1712]
	ldr q1, [x3, #688]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #688]
	ldr q0, [x3, #1728]
	ldr q1, [x3, #704]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #704]
	ldr q0, [x3, #1744]
	ldr q1, [x3, #720]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #720]
	ldr q0, [x3, #1760]
	ldr q1, [x3, #736]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #736]
	ldr q0, [x3, #1776]
	ldr q1, [x3, #752]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #752]
	ldr q0, [x3, #1792]
	ldr q1, [x3, #768]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #768]
	ldr q0, [x3, #1808]
	ldr q1, [x3, #784]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #784]
	ldr q0, [x3, #1824]
	ldr q1, [x3, #800]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #800]
	ldr q0, [x3, #1840]
	ldr q1, [x3, #816]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #816]
	ldr q0, [x3, #1856]
	ldr q1, [x3, #832]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #832]
	ldr q0, [x3, #1872]
	ldr q1, [x3, #848]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #848]
	ldr q0, [x3, #1888]
	ldr q1, [x3, #864]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #864]
	ldr q0, [x3, #1904]
	ldr q1, [x3, #880]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #880]
	ldr q0, [x3, #1920]
	ldr q1, [x3, #896]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #896]
	ldr q0, [x3, #1936]
	ldr q1, [x3, #912]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #912]
	ldr q0, [x3, #1952]
	ldr q1, [x3, #928]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #928]
	ldr q0, [x3, #1968]
	ldr q1, [x3, #944]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #944]
	ldr q0, [x3, #1984]
	ldr q1, [x3, #960]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #960]
	ldr q0, [x3, #2000]
	ldr q1, [x3, #976]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #976]
	ldr q0, [x3, #2016]
	ldr q1, [x3, #992]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #992]
	ldr q0, [x3, #2032]
	ldr q1, [x3, #1008]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #1008]
	ret
	.p2align 6
