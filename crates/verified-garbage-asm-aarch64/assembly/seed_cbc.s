// The functions of `src/seed_cbc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_cbc_encrypt_chained:
	sub sp, sp, #1456
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #1360]
	str x20, [x5, #1368]
	str x21, [x5, #1376]
	str x22, [x5, #1384]
	str x23, [x5, #1392]
	str x24, [x5, #1400]
	str x25, [x5, #1408]
	str x26, [x5, #1416]
	str x27, [x5, #1424]
	str x28, [x5, #1432]
	add x25, x1, #0
	cbz x3, 20f
	ldr x6, [x2, #0]
	ldr x7, [x1, #0]
	eor x6, x6, x7
	str x6, [x2, #0]
	ldr x6, [x2, #8]
	ldr x7, [x1, #8]
	eor x6, x6, x7
	str x6, [x2, #8]
	b 21f
20:
21:
	add x23, x2, #0
	add x24, x3, #0
	ldr x6, [x0, #0]
	str x6, [x5, #1232]
	ldr x6, [x0, #8]
	str x6, [x5, #1240]
	ldr x6, [x0, #16]
	str x6, [x5, #1248]
	ldr x6, [x0, #24]
	str x6, [x5, #1256]
	ldr x6, [x0, #32]
	str x6, [x5, #1264]
	ldr x6, [x0, #40]
	str x6, [x5, #1272]
	ldr x6, [x0, #48]
	str x6, [x5, #1280]
	ldr x6, [x0, #56]
	str x6, [x5, #1288]
	ldr x6, [x0, #64]
	str x6, [x5, #1296]
	ldr x6, [x0, #72]
	str x6, [x5, #1304]
	ldr x6, [x0, #80]
	str x6, [x5, #1312]
	ldr x6, [x0, #88]
	str x6, [x5, #1320]
	ldr x6, [x0, #96]
	str x6, [x5, #1328]
	ldr x6, [x0, #104]
	str x6, [x5, #1336]
	ldr x6, [x0, #112]
	str x6, [x5, #1344]
	ldr x6, [x0, #120]
	str x6, [x5, #1352]
	cbz x24, 22f
24:
	ldr x6, [x23, #0]
	str x6, [x5, #976]
	ldr x6, [x23, #8]
	str x6, [x5, #984]
	movz x6, #34217, lsl #0
	movk x6, #54230, lsl #16
	movk x6, #7508, lsl #32
	movk x6, #9644, lsl #48
	movz x7, #17245, lsl #0
	movk x7, #7704, lsl #16
	movk x7, #64593, lsl #32
	movk x7, #25546, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #17448, lsl #0
	movk x6, #40224, lsl #16
	movk x6, #58080, lsl #32
	movk x6, #6088, lsl #48
	movz x7, #36773, lsl #0
	movk x7, #31491, lsl #16
	movk x7, #5051, lsl #32
	movk x7, #61138, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #35952, lsl #0
	movk x6, #43071, lsl #16
	movk x6, #56626, lsl #32
	movk x6, #29942, lsl #48
	movz x7, #38380, lsl #0
	movk x7, #22283, lsl #16
	movk x7, #23388, lsl #32
	movk x7, #445, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #7204, lsl #0
	movk x6, #39027, lsl #16
	movk x6, #52240, lsl #32
	movk x6, #55794, lsl #48
	movz x7, #59180, lsl #0
	movk x7, #33650, lsl #16
	movk x7, #53659, lsl #32
	movk x7, #51590, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #20576, lsl #0
	movk x6, #60323, lsl #16
	movk x6, #46605, lsl #32
	movk x6, #20382, lsl #48
	movz x7, #23223, lsl #0
	movk x7, #30918, lsl #16
	movk x7, #4774, lsl #32
	movk x7, #54703, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #50017, lsl #0
	movk x6, #16820, lsl #16
	movk x6, #32082, lsl #32
	movk x6, #2189, lsl #48
	movz x7, #39199, lsl #0
	movk x7, #6400, lsl #16
	movk x7, #21252, lsl #32
	movk x7, #57847, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #30461, lsl #0
	movk x6, #10031, lsl #16
	movk x6, #35760, lsl #32
	movk x6, #43790, lsl #48
	movz x7, #28322, lsl #0
	movk x7, #19859, lsl #16
	movk x7, #31849, lsl #32
	movk x7, #2569, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #61375, lsl #0
	movk x6, #50675, lsl #16
	movk x6, #5255, lsl #32
	movk x6, #25854, lsl #48
	movz x7, #11998, lsl #0
	movk x7, #6731, lsl #16
	movk x7, #8454, lsl #32
	movk x7, #26219, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #62722, lsl #0
	movk x6, #35474, lsl #16
	movk x6, #45836, lsl #32
	movk x6, #53374, lsl #48
	movz x7, #18298, lsl #0
	movk x7, #58774, lsl #16
	movk x7, #32806, lsl #32
	movk x7, #57261, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #12449, lsl #0
	movk x6, #44599, lsl #16
	movk x6, #5430, lsl #32
	movk x6, #14370, lsl #48
	movz x7, #42996, lsl #0
	movk x7, #19525, lsl #16
	movk x7, #59777, lsl #32
	movk x7, #38788, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #52021, lsl #0
	movk x6, #15566, lsl #16
	movk x6, #4465, lsl #32
	movk x6, #35271, lsl #48
	movz x7, #64373, lsl #0
	movk x7, #63706, lsl #16
	movk x7, #22932, lsl #32
	movk x7, #50306, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #18943, lsl #0
	movk x6, #26425, lsl #16
	movk x6, #53184, lsl #32
	movk x6, #47319, lsl #48
	movz x7, #36367, lsl #0
	movk x7, #9026, lsl #16
	movk x7, #27793, lsl #32
	movk x7, #42203, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #61748, lsl #0
	movk x6, #49736, lsl #16
	movk x6, #15727, lsl #32
	movk x6, #16429, lsl #48
	movz x7, #16062, lsl #0
	movk x7, #49596, lsl #16
	movk x7, #47786, lsl #32
	movk x7, #21838, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #56379, lsl #0
	movk x6, #32616, lsl #16
	movk x6, #55452, lsl #32
	movk x6, #22090, lsl #48
	movz x7, #41079, lsl #0
	movk x7, #18157, lsl #16
	movk x7, #11189, lsl #32
	movk x7, #64101, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #47587, lsl #0
	movk x6, #40881, lsl #16
	movk x6, #63838, lsl #32
	movk x6, #45798, lsl #48
	movz x7, #59953, lsl #0
	movk x7, #24429, lsl #16
	movk x7, #61668, lsl #32
	movk x7, #35021, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #14870, lsl #0
	movk x6, #54360, lsl #16
	movk x6, #10594, lsl #32
	movk x6, #13063, lsl #48
	movz x7, #7144, lsl #0
	movk x7, #30981, lsl #16
	movk x7, #27280, lsl #32
	movk x7, #39466, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #38920, lsl #0
	movk x6, #4481, lsl #16
	movk x6, #33555, lsl #32
	movk x6, #2714, lsl #48
	movz x7, #26872, lsl #0
	movk x7, #57713, lsl #16
	movk x7, #29667, lsl #32
	movk x7, #64106, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	movz x6, #44288, lsl #0
	movk x6, #38459, lsl #16
	movk x6, #56433, lsl #32
	movk x6, #59210, lsl #48
	movz x7, #50795, lsl #0
	movk x7, #64848, lsl #16
	movk x7, #46874, lsl #32
	movk x7, #35873, lsl #48
	mov v5.d[0], x6
	mov v5.d[1], x7
	movz w15, #64, lsl #0
	dup v6.16b, w15
	movz w15, #128, lsl #0
	dup v7.16b, w15
	movz w14, #192, lsl #0
	movz w15, #15, lsl #0
	movz x16, #65280, lsl #0
	movk x16, #65280, lsl #16
	movk x16, #0, lsl #32
	movk x16, #0, lsl #48
	movz x17, #53244, lsl #0
	movk x17, #53244, lsl #16
	movk x17, #0, lsl #32
	movk x17, #0, lsl #48
	movz x4, #62271, lsl #0
	movk x4, #62271, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	ldr w0, [x5, #976]
	rev w0, w0
	ldr w1, [x5, #980]
	rev w1, w1
	ldr w2, [x5, #984]
	rev w2, w2
	ldr w3, [x5, #988]
	rev w3, w3
	ldr w8, [x5, #1232]
	eor w8, w8, w2
	ldr w10, [x5, #1236]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1240]
	eor w8, w8, w0
	ldr w10, [x5, #1244]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1248]
	eor w8, w8, w2
	ldr w10, [x5, #1252]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1256]
	eor w8, w8, w0
	ldr w10, [x5, #1260]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1264]
	eor w8, w8, w2
	ldr w10, [x5, #1268]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1272]
	eor w8, w8, w0
	ldr w10, [x5, #1276]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1280]
	eor w8, w8, w2
	ldr w10, [x5, #1284]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1288]
	eor w8, w8, w0
	ldr w10, [x5, #1292]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1296]
	eor w8, w8, w2
	ldr w10, [x5, #1300]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1304]
	eor w8, w8, w0
	ldr w10, [x5, #1308]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1312]
	eor w8, w8, w2
	ldr w10, [x5, #1316]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1320]
	eor w8, w8, w0
	ldr w10, [x5, #1324]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1328]
	eor w8, w8, w2
	ldr w10, [x5, #1332]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1336]
	eor w8, w8, w0
	ldr w10, [x5, #1340]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	ldr w8, [x5, #1344]
	eor w8, w8, w2
	ldr w10, [x5, #1348]
	eor w10, w10, w3
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w1, w1, w10
	add w10, w10, w8
	eor w0, w0, w10
	ldr w8, [x5, #1352]
	eor w8, w8, w0
	ldr w10, [x5, #1356]
	eor w10, w10, w1
	eor w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x9, x10, #0
	add w10, w10, w8
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	add x8, x10, #0
	add w10, w10, w9
	dup v0.4s, w10
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v7.16b
	dup v3.16b, w14
	eor v3.16b, v0.16b, v3.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	dup v1.16b, w15
	and v1.16b, v0.16b, v1.16b
	ushr v2.16b, v0.16b, #4
	tbl v1.16b, {v4.16b}, v1.16b
	tbl v2.16b, {v5.16b}, v2.16b
	eor v1.16b, v1.16b, v2.16b
	dup v2.4s, w16
	bit v0.16b, v1.16b, v2.16b
	umov w10, v0.s[0]
	and w11, w10, w17
	and w12, w10, w4
	eor w11, w11, w12, ror #8
	and w12, w10, w17, ror #8
	and w13, w10, w4, ror #8
	eor w12, w12, w13, ror #8
	eor w10, w11, w12, ror #16
	eor w3, w3, w10
	add w10, w10, w8
	eor w2, w2, w10
	rev w2, w2
	str w2, [x5, #976]
	rev w3, w3
	str w3, [x5, #980]
	rev w0, w0
	str w0, [x5, #984]
	rev w1, w1
	str w1, [x5, #988]
	ldr x6, [x5, #976]
	str x6, [x23, #0]
	ldr x6, [x5, #984]
	str x6, [x23, #8]
	sub x24, x24, #1
	cbz x24, 25f
	ldr x6, [x23, #16]
	ldr x7, [x5, #976]
	eor x6, x6, x7
	str x6, [x23, #16]
	ldr x6, [x23, #24]
	ldr x7, [x5, #984]
	eor x6, x6, x7
	str x6, [x23, #24]
	b 26f
25:
26:
	add x23, x23, #16
	cbnz x24, 24b
	ldr x6, [x5, #976]
	str x6, [x25, #0]
	ldr x6, [x5, #984]
	str x6, [x25, #8]
	b 23f
22:
23:
	ldr x19, [x5, #1360]
	ldr x20, [x5, #1368]
	ldr x21, [x5, #1376]
	ldr x22, [x5, #1384]
	ldr x23, [x5, #1392]
	ldr x24, [x5, #1400]
	ldr x25, [x5, #1408]
	ldr x26, [x5, #1416]
	ldr x27, [x5, #1424]
	ldr x28, [x5, #1432]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	add sp, sp, #1456
	ret
	.p2align 6

vg_seed_cbc_decrypt_chained:
	sub sp, sp, #1456
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #1360]
	str x20, [x5, #1368]
	str x21, [x5, #1376]
	str x22, [x5, #1384]
	str x23, [x5, #1392]
	str x24, [x5, #1400]
	str x25, [x5, #1408]
	str x26, [x5, #1416]
	str x27, [x5, #1424]
	str x28, [x5, #1432]
	ldr x6, [x1, #0]
	str x6, [x5, #1440]
	ldr x6, [x1, #8]
	str x6, [x5, #1448]
	cbz x3, 20f
	sub x7, x3, #1
	lsl x7, x7, #4
	add x7, x7, x2
	ldr x6, [x7, #0]
	str x6, [x1, #0]
	ldr x6, [x7, #8]
	str x6, [x1, #8]
	b 21f
20:
21:
	add x23, x2, #0
	add x24, x3, #0
	ldr x6, [x0, #0]
	str x6, [x5, #1232]
	ldr x6, [x0, #8]
	str x6, [x5, #1240]
	ldr x6, [x0, #16]
	str x6, [x5, #1248]
	ldr x6, [x0, #24]
	str x6, [x5, #1256]
	ldr x6, [x0, #32]
	str x6, [x5, #1264]
	ldr x6, [x0, #40]
	str x6, [x5, #1272]
	ldr x6, [x0, #48]
	str x6, [x5, #1280]
	ldr x6, [x0, #56]
	str x6, [x5, #1288]
	ldr x6, [x0, #64]
	str x6, [x5, #1296]
	ldr x6, [x0, #72]
	str x6, [x5, #1304]
	ldr x6, [x0, #80]
	str x6, [x5, #1312]
	ldr x6, [x0, #88]
	str x6, [x5, #1320]
	ldr x6, [x0, #96]
	str x6, [x5, #1328]
	ldr x6, [x0, #104]
	str x6, [x5, #1336]
	ldr x6, [x0, #112]
	str x6, [x5, #1344]
	ldr x6, [x0, #120]
	str x6, [x5, #1352]
	cbz x24, 22f
24:
	lsr x13, x24, #4
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #16, lsl #0
26:
	add x14, x5, #0
	add x14, x14, #976
	add x15, x23, #0
	add x17, x16, #0
27:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 27b
	dup v28.2d, x30
	dup v27.2d, x5
	dup v29.2d, x23
	dup v30.2d, x24
	add x0, x5, #1232
	add x1, x5, #976
	movz x2, #16, lsl #0
	add x3, x5, #0
	bl {vg_seed_decrypt_blocks}
	umov x5, v27.d[0]
	umov x30, v28.d[0]
	umov x23, v29.d[0]
	umov x24, v30.d[0]
	lsr x13, x24, #4
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #16, lsl #0
29:
	add x14, x5, #0
	add x14, x14, #976
	add x15, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x14, #0]
	ldr x9, [x5, #1440]
	eor x8, x8, x9
	str x8, [x14, #0]
	ldr x8, [x14, #8]
	ldr x9, [x5, #1448]
	eor x8, x8, x9
	str x8, [x14, #8]
	ldr x8, [x15, #0]
	str x8, [x5, #1440]
	ldr x8, [x15, #8]
	str x8, [x5, #1448]
	ldr x8, [x14, #0]
	str x8, [x15, #0]
	ldr x8, [x14, #8]
	str x8, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 24b
	b 23f
22:
23:
	ldr x19, [x5, #1360]
	ldr x20, [x5, #1368]
	ldr x21, [x5, #1376]
	ldr x22, [x5, #1384]
	ldr x23, [x5, #1392]
	ldr x24, [x5, #1400]
	ldr x25, [x5, #1408]
	ldr x26, [x5, #1416]
	ldr x27, [x5, #1424]
	ldr x28, [x5, #1432]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #512
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1024
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	stp x17, x17, [x16, #224]
	stp x17, x17, [x16, #240]
	stp x17, x17, [x16, #256]
	stp x17, x17, [x16, #272]
	stp x17, x17, [x16, #288]
	stp x17, x17, [x16, #304]
	stp x17, x17, [x16, #320]
	stp x17, x17, [x16, #336]
	stp x17, x17, [x16, #352]
	stp x17, x17, [x16, #368]
	stp x17, x17, [x16, #384]
	stp x17, x17, [x16, #400]
	stp x17, x17, [x16, #416]
	add sp, sp, #1456
	ret
	.p2align 6
