// The functions of `src/internal/vg_p224_comb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p224_comb:
	add x14, x30, #0
	ldr x1, [x0, #288]
	str x1, [x0, #1344]
	ldr x1, [x0, #296]
	str x1, [x0, #1352]
	ldr x1, [x0, #304]
	str x1, [x0, #1360]
	ldr x1, [x0, #312]
	str x1, [x0, #1368]
	movz x1, #62856, lsl #0
	movk x1, #27387, lsl #16
	movk x1, #58071, lsl #32
	movk x1, #61189, lsl #48
	str x1, [x0, #512]
	movz x1, #20932, lsl #0
	movk x1, #62748, lsl #16
	movk x1, #13005, lsl #32
	movk x1, #23827, lsl #48
	str x1, [x0, #520]
	movz x1, #48691, lsl #0
	movk x1, #28946, lsl #16
	movk x1, #62854, lsl #32
	movk x1, #59839, lsl #48
	str x1, [x0, #528]
	movz x1, #40775, lsl #0
	movk x1, #51478, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #536]
	movz x1, #27774, lsl #0
	movk x1, #41811, lsl #16
	movk x1, #19422, lsl #32
	movk x1, #41013, lsl #48
	str x1, [x0, #544]
	movz x1, #29324, lsl #0
	movk x1, #29120, lsl #16
	movk x1, #4503, lsl #32
	movk x1, #8918, lsl #48
	str x1, [x0, #552]
	movz x1, #13878, lsl #0
	movk x1, #29309, lsl #16
	movk x1, #45942, lsl #32
	movk x1, #17055, lsl #48
	str x1, [x0, #560]
	movz x1, #36546, lsl #0
	movk x1, #17537, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #568]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #576]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #584]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #592]
	movz x1, #0, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #600]
	movz x7, #0, lsl #0
	str x7, [x0, #1760]
	movz x19, #37, lsl #0
20:
	sub x19, x19, #1
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	movz x2, #0, lsl #0
	add x2, x2, x2
	ldrb w4, [x16, #1510]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1509]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1508]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1507]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1506]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1505]
	add x2, x2, x4
	add x2, x2, x2
	ldrb w4, [x16, #1504]
	add x2, x2, x4
	sub x3, x2, #64
	lsr x4, x3, #63
	movz x9, #0, lsl #0
	sub x4, x9, x4
	eor x2, x3, x4
	sub x2, x2, x4
	movz x7, #0, lsl #0
	adrp x16, {VG_P224_COMB}
	add x16, x16, {VG_P224_COMB}
	movz x17, #4096, lsl #0
	mul x17, x19, x17
	add x16, x16, x17
	movz x5, #1, lsl #0
	movz x1, #0, lsl #0
	dup v19.2d, x2
	dup v28.2d, x5
	add v18.2d, v28.2d, v28.2d
	movi v17.2d, #0
	sub v17.2d, v17.2d, v28.2d
	movi v30.2d, #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #0]
	ldr q21, [x16, #16]
	ldr q22, [x16, #32]
	ldr q23, [x16, #48]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #64]
	ldr q25, [x16, #80]
	ldr q26, [x16, #96]
	ldr q27, [x16, #112]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #128]
	ldr q21, [x16, #144]
	ldr q22, [x16, #160]
	ldr q23, [x16, #176]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #192]
	ldr q25, [x16, #208]
	ldr q26, [x16, #224]
	ldr q27, [x16, #240]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #256]
	ldr q21, [x16, #272]
	ldr q22, [x16, #288]
	ldr q23, [x16, #304]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #320]
	ldr q25, [x16, #336]
	ldr q26, [x16, #352]
	ldr q27, [x16, #368]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #384]
	ldr q21, [x16, #400]
	ldr q22, [x16, #416]
	ldr q23, [x16, #432]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #448]
	ldr q25, [x16, #464]
	ldr q26, [x16, #480]
	ldr q27, [x16, #496]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #512]
	ldr q21, [x16, #528]
	ldr q22, [x16, #544]
	ldr q23, [x16, #560]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #576]
	ldr q25, [x16, #592]
	ldr q26, [x16, #608]
	ldr q27, [x16, #624]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #640]
	ldr q21, [x16, #656]
	ldr q22, [x16, #672]
	ldr q23, [x16, #688]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #704]
	ldr q25, [x16, #720]
	ldr q26, [x16, #736]
	ldr q27, [x16, #752]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #768]
	ldr q21, [x16, #784]
	ldr q22, [x16, #800]
	ldr q23, [x16, #816]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #832]
	ldr q25, [x16, #848]
	ldr q26, [x16, #864]
	ldr q27, [x16, #880]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #896]
	ldr q21, [x16, #912]
	ldr q22, [x16, #928]
	ldr q23, [x16, #944]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #960]
	ldr q25, [x16, #976]
	ldr q26, [x16, #992]
	ldr q27, [x16, #1008]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1024]
	ldr q21, [x16, #1040]
	ldr q22, [x16, #1056]
	ldr q23, [x16, #1072]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1088]
	ldr q25, [x16, #1104]
	ldr q26, [x16, #1120]
	ldr q27, [x16, #1136]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1152]
	ldr q21, [x16, #1168]
	ldr q22, [x16, #1184]
	ldr q23, [x16, #1200]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1216]
	ldr q25, [x16, #1232]
	ldr q26, [x16, #1248]
	ldr q27, [x16, #1264]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1280]
	ldr q21, [x16, #1296]
	ldr q22, [x16, #1312]
	ldr q23, [x16, #1328]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1344]
	ldr q25, [x16, #1360]
	ldr q26, [x16, #1376]
	ldr q27, [x16, #1392]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1408]
	ldr q21, [x16, #1424]
	ldr q22, [x16, #1440]
	ldr q23, [x16, #1456]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1472]
	ldr q25, [x16, #1488]
	ldr q26, [x16, #1504]
	ldr q27, [x16, #1520]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1536]
	ldr q21, [x16, #1552]
	ldr q22, [x16, #1568]
	ldr q23, [x16, #1584]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1600]
	ldr q25, [x16, #1616]
	ldr q26, [x16, #1632]
	ldr q27, [x16, #1648]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1664]
	ldr q21, [x16, #1680]
	ldr q22, [x16, #1696]
	ldr q23, [x16, #1712]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1728]
	ldr q25, [x16, #1744]
	ldr q26, [x16, #1760]
	ldr q27, [x16, #1776]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1792]
	ldr q21, [x16, #1808]
	ldr q22, [x16, #1824]
	ldr q23, [x16, #1840]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1856]
	ldr q25, [x16, #1872]
	ldr q26, [x16, #1888]
	ldr q27, [x16, #1904]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #1920]
	ldr q21, [x16, #1936]
	ldr q22, [x16, #1952]
	ldr q23, [x16, #1968]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #1984]
	ldr q25, [x16, #2000]
	ldr q26, [x16, #2016]
	ldr q27, [x16, #2032]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2048]
	ldr q21, [x16, #2064]
	ldr q22, [x16, #2080]
	ldr q23, [x16, #2096]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2112]
	ldr q25, [x16, #2128]
	ldr q26, [x16, #2144]
	ldr q27, [x16, #2160]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2176]
	ldr q21, [x16, #2192]
	ldr q22, [x16, #2208]
	ldr q23, [x16, #2224]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2240]
	ldr q25, [x16, #2256]
	ldr q26, [x16, #2272]
	ldr q27, [x16, #2288]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2304]
	ldr q21, [x16, #2320]
	ldr q22, [x16, #2336]
	ldr q23, [x16, #2352]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2368]
	ldr q25, [x16, #2384]
	ldr q26, [x16, #2400]
	ldr q27, [x16, #2416]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2432]
	ldr q21, [x16, #2448]
	ldr q22, [x16, #2464]
	ldr q23, [x16, #2480]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2496]
	ldr q25, [x16, #2512]
	ldr q26, [x16, #2528]
	ldr q27, [x16, #2544]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2560]
	ldr q21, [x16, #2576]
	ldr q22, [x16, #2592]
	ldr q23, [x16, #2608]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2624]
	ldr q25, [x16, #2640]
	ldr q26, [x16, #2656]
	ldr q27, [x16, #2672]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2688]
	ldr q21, [x16, #2704]
	ldr q22, [x16, #2720]
	ldr q23, [x16, #2736]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2752]
	ldr q25, [x16, #2768]
	ldr q26, [x16, #2784]
	ldr q27, [x16, #2800]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2816]
	ldr q21, [x16, #2832]
	ldr q22, [x16, #2848]
	ldr q23, [x16, #2864]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #2880]
	ldr q25, [x16, #2896]
	ldr q26, [x16, #2912]
	ldr q27, [x16, #2928]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #2944]
	ldr q21, [x16, #2960]
	ldr q22, [x16, #2976]
	ldr q23, [x16, #2992]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3008]
	ldr q25, [x16, #3024]
	ldr q26, [x16, #3040]
	ldr q27, [x16, #3056]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3072]
	ldr q21, [x16, #3088]
	ldr q22, [x16, #3104]
	ldr q23, [x16, #3120]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3136]
	ldr q25, [x16, #3152]
	ldr q26, [x16, #3168]
	ldr q27, [x16, #3184]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3200]
	ldr q21, [x16, #3216]
	ldr q22, [x16, #3232]
	ldr q23, [x16, #3248]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3264]
	ldr q25, [x16, #3280]
	ldr q26, [x16, #3296]
	ldr q27, [x16, #3312]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3328]
	ldr q21, [x16, #3344]
	ldr q22, [x16, #3360]
	ldr q23, [x16, #3376]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3392]
	ldr q25, [x16, #3408]
	ldr q26, [x16, #3424]
	ldr q27, [x16, #3440]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3456]
	ldr q21, [x16, #3472]
	ldr q22, [x16, #3488]
	ldr q23, [x16, #3504]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3520]
	ldr q25, [x16, #3536]
	ldr q26, [x16, #3552]
	ldr q27, [x16, #3568]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3584]
	ldr q21, [x16, #3600]
	ldr q22, [x16, #3616]
	ldr q23, [x16, #3632]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3648]
	ldr q25, [x16, #3664]
	ldr q26, [x16, #3680]
	ldr q27, [x16, #3696]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3712]
	ldr q21, [x16, #3728]
	ldr q22, [x16, #3744]
	ldr q23, [x16, #3760]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3776]
	ldr q25, [x16, #3792]
	ldr q26, [x16, #3808]
	ldr q27, [x16, #3824]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3840]
	ldr q21, [x16, #3856]
	ldr q22, [x16, #3872]
	ldr q23, [x16, #3888]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #3904]
	ldr q25, [x16, #3920]
	ldr q26, [x16, #3936]
	ldr q27, [x16, #3952]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	add v17.2d, v17.2d, v18.2d
	cmeq v16.2d, v17.2d, v19.2d
	ldr q20, [x16, #3968]
	ldr q21, [x16, #3984]
	ldr q22, [x16, #4000]
	ldr q23, [x16, #4016]
	bit v0.16b, v20.16b, v16.16b
	bit v1.16b, v21.16b, v16.16b
	bit v2.16b, v22.16b, v16.16b
	bit v3.16b, v23.16b, v16.16b
	add v30.2d, v30.2d, v18.2d
	cmeq v31.2d, v30.2d, v19.2d
	ldr q24, [x16, #4032]
	ldr q25, [x16, #4048]
	ldr q26, [x16, #4064]
	ldr q27, [x16, #4080]
	bit v4.16b, v24.16b, v31.16b
	bit v5.16b, v25.16b, v31.16b
	bit v6.16b, v26.16b, v31.16b
	bit v7.16b, v27.16b, v31.16b
	orr v0.16b, v0.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	orr v2.16b, v2.16b, v6.16b
	orr v3.16b, v3.16b, v7.16b
	movi v16.2d, #0
	cmeq v16.2d, v16.2d, v19.2d
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[0], x6
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	mov v20.d[1], x6
	bit v2.16b, v20.16b, v16.16b
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[0], x6
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	mov v20.d[1], x6
	bit v3.16b, v20.16b, v16.16b
	str q0, [x0, #704]
	str q1, [x0, #720]
	str q2, [x0, #736]
	str q3, [x0, #752]
	subs x4, x2, x5
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #768]
	movz x6, #65535, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #65535, lsl #32
	movk x6, #65535, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #776]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #784]
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	csel x6, x6, x7, hs
	str x6, [x0, #792]
	movz x7, #0, lsl #0
	ldr x8, [x0, #160]
	ldr x9, [x0, #168]
	ldr x10, [x0, #176]
	ldr x11, [x0, #184]
	ldr x2, [x0, #736]
	subs x8, x8, x2
	ldr x2, [x0, #744]
	sbcs x9, x9, x2
	ldr x2, [x0, #752]
	sbcs x10, x10, x2
	ldr x2, [x0, #760]
	sbcs x11, x11, x2
	sbc x17, x7, x7
	ldr x2, [x0, #64]
	and x2, x2, x17
	adds x8, x8, x2
	ldr x2, [x0, #72]
	and x2, x2, x17
	adcs x9, x9, x2
	ldr x2, [x0, #80]
	and x2, x2, x17
	adcs x10, x10, x2
	ldr x2, [x0, #88]
	and x2, x2, x17
	adcs x11, x11, x2
	str x8, [x0, #1024]
	str x9, [x0, #1032]
	str x10, [x0, #1040]
	str x11, [x0, #1048]
	movz x16, #7, lsl #0
	mul x16, x19, x16
	add x16, x0, x16
	ldrb w3, [x16, #1510]
	sub x3, x3, #1
	ldr x1, [x0, #736]
	ldr x2, [x0, #1024]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #736]
	ldr x1, [x0, #744]
	ldr x2, [x0, #1032]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #744]
	ldr x1, [x0, #752]
	ldr x2, [x0, #1040]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #752]
	ldr x1, [x0, #760]
	ldr x2, [x0, #1048]
	eor x2, x2, x1
	and x2, x2, x3
	eor x1, x1, x2
	str x1, [x0, #760]
	mov v29.d[0], x30
	bl {vg_p224_proj_add}
	umov x30, v29.d[0]
	ldr x1, [x0, #608]
	str x1, [x0, #512]
	ldr x1, [x0, #616]
	str x1, [x0, #520]
	ldr x1, [x0, #624]
	str x1, [x0, #528]
	ldr x1, [x0, #632]
	str x1, [x0, #536]
	ldr x1, [x0, #640]
	str x1, [x0, #544]
	ldr x1, [x0, #648]
	str x1, [x0, #552]
	ldr x1, [x0, #656]
	str x1, [x0, #560]
	ldr x1, [x0, #664]
	str x1, [x0, #568]
	ldr x1, [x0, #672]
	str x1, [x0, #576]
	ldr x1, [x0, #680]
	str x1, [x0, #584]
	ldr x1, [x0, #688]
	str x1, [x0, #592]
	ldr x1, [x0, #696]
	str x1, [x0, #600]
	cbnz x19, 20b
	add x30, x14, #0
	ret
	.p2align 6
