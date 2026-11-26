// The functions of `src/internal/vg_seed_serial_encrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_seed_serial_encrypt:
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
	ret
	.p2align 6
