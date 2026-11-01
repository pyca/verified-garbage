// The functions of `src/internal/vg_rc2_expand_key.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_expand_key:
	str x23, [x4, #0]
	str x24, [x4, #8]
	str x19, [x4, #16]
	str x20, [x4, #24]
	str x21, [x4, #32]
	str x22, [x4, #40]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x3, #0
	add x22, x2, #0
	movz x23, #0, lsl #0
20:
	add x9, x19, x23
	ldrb w8, [x9, #0]
	add x9, x21, x23
	strb w8, [x9, #0]
	add x23, x23, #1
	sub x10, x23, x20
	cbnz x10, 20b
	sub x10, x23, #128
	cbnz x10, 21f
	b 22f
21:
23:
	add x9, x21, x23
	sub x9, x9, #1
	ldrb w8, [x9, #0]
	sub x5, x23, x20
	add x9, x21, x5
	ldrb w3, [x9, #0]
	add x8, x8, x3
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x23, x23, #1
	sub x10, x23, #128
	cbnz x10, 23b
22:
	add x24, x22, #7
	lsr x24, x24, #3
	movz x23, #128, lsl #0
	sub x23, x23, x24
	add x5, x22, #0
	lsl x5, x5, #61
	lsr x5, x5, #61
	movz x2, #255, lsl #0
	sub x10, x5, #1
	cbz x10, 24f
	b 25f
24:
	movz x2, #1, lsl #0
25:
	sub x10, x5, #2
	cbz x10, 26f
	b 27f
26:
	movz x2, #3, lsl #0
27:
	sub x10, x5, #3
	cbz x10, 28f
	b 29f
28:
	movz x2, #7, lsl #0
29:
	sub x10, x5, #4
	cbz x10, 210f
	b 211f
210:
	movz x2, #15, lsl #0
211:
	sub x10, x5, #5
	cbz x10, 212f
	b 213f
212:
	movz x2, #31, lsl #0
213:
	sub x10, x5, #6
	cbz x10, 214f
	b 215f
214:
	movz x2, #63, lsl #0
215:
	sub x10, x5, #7
	cbz x10, 216f
	b 217f
216:
	movz x2, #127, lsl #0
217:
	add x9, x21, x23
	ldrb w8, [x9, #0]
	and x8, x8, x2
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x10, x23, #0
	cbnz x10, 218f
	b 219f
218:
220:
	sub x23, x23, #1
	add x9, x21, x23
	add x9, x9, #1
	ldrb w8, [x9, #0]
	add x5, x23, x24
	add x9, x21, x5
	ldrb w3, [x9, #0]
	eor x8, x8, x3
	movz x6, #30937, lsl #0
	movk x6, #50425, lsl #16
	movk x6, #56601, lsl #32
	movk x6, #60853, lsl #48
	movz x7, #59688, lsl #0
	movk x7, #31229, lsl #16
	movk x7, #41034, lsl #32
	movk x7, #40408, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #32454, lsl #0
	movk x6, #33591, lsl #16
	movk x6, #30251, lsl #32
	movk x6, #36435, lsl #48
	movz x7, #19554, lsl #0
	movk x7, #34916, lsl #16
	movk x7, #35652, lsl #32
	movk x7, #41723, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #39447, lsl #0
	movk x6, #62809, lsl #16
	movk x6, #45959, lsl #32
	movk x6, #4943, lsl #48
	movz x7, #17761, lsl #0
	movk x7, #36205, lsl #16
	movk x7, #33033, lsl #32
	movk x7, #12925, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #36797, lsl #0
	movk x6, #60224, lsl #16
	movk x6, #46982, lsl #32
	movk x6, #2939, lsl #48
	movz x7, #38384, lsl #0
	movk x7, #8737, lsl #16
	movk x7, #27484, lsl #32
	movk x7, #33358, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #54868, lsl #0
	movk x6, #37733, lsl #16
	movk x6, #24782, lsl #32
	movk x6, #7346, lsl #48
	movz x7, #22131, lsl #0
	movk x7, #5312, lsl #16
	movk x7, #36007, lsl #32
	movk x7, #56561, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #29970, lsl #0
	movk x6, #8138, lsl #16
	movk x6, #48699, lsl #32
	movk x6, #53732, lsl #48
	movz x7, #15682, lsl #0
	movk x7, #12500, lsl #16
	movk x7, #15523, lsl #32
	movk x7, #9910, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #49007, lsl #0
	movk x6, #55822, lsl #16
	movk x6, #26950, lsl #32
	movk x6, #22279, lsl #48
	movz x7, #61991, lsl #0
	movk x7, #39709, lsl #16
	movk x7, #38076, lsl #32
	movk x7, #835, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #4600, lsl #0
	movk x6, #63175, lsl #16
	movk x6, #61328, lsl #32
	movk x6, #59198, lsl #48
	movz x7, #49926, lsl #0
	movk x7, #12245, lsl #16
	movk x7, #26312, lsl #32
	movk x7, #55070, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #59400, lsl #0
	movk x6, #57066, lsl #16
	movk x6, #21120, lsl #32
	movk x6, #63470, lsl #48
	movz x7, #43652, lsl #0
	movk x7, #44146, lsl #16
	movk x7, #19765, lsl #32
	movk x7, #10858, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #6806, lsl #0
	movk x6, #29138, lsl #16
	movk x6, #5466, lsl #32
	movk x6, #29769, lsl #48
	movz x7, #40779, lsl #0
	movk x7, #24272, lsl #16
	movk x7, #6148, lsl #32
	movk x7, #60580, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #57538, lsl #0
	movk x6, #28225, lsl #16
	movk x6, #20751, lsl #32
	movk x6, #52427, lsl #48
	movz x7, #37156, lsl #0
	movk x7, #20655, lsl #16
	movk x7, #62625, lsl #32
	movk x7, #14704, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #31897, lsl #0
	movk x6, #34106, lsl #16
	movk x6, #47139, lsl #32
	movk x6, #31412, lsl #48
	movz x7, #764, lsl #0
	movk x7, #23350, lsl #16
	movk x7, #21797, lsl #32
	movk x7, #12695, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #23853, lsl #0
	movk x6, #39162, lsl #16
	movk x6, #35555, lsl #32
	movk x6, #44690, lsl #48
	movz x7, #57093, lsl #0
	movk x7, #4137, lsl #16
	movk x7, #27751, lsl #32
	movk x7, #51642, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #211, lsl #0
	movk x6, #53222, lsl #16
	movk x6, #40673, lsl #32
	movk x6, #11432, lsl #48
	movz x7, #5731, lsl #0
	movk x7, #16129, lsl #16
	movk x7, #57944, lsl #32
	movk x7, #43401, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #14349, lsl #0
	movk x6, #6964, lsl #16
	movk x6, #13227, lsl #32
	movk x6, #45311, lsl #48
	movz x7, #18619, lsl #0
	movk x7, #24332, lsl #16
	movk x7, #45497, lsl #32
	movk x7, #11981, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #62405, lsl #0
	movk x6, #18395, lsl #16
	movk x6, #42469, lsl #32
	movk x6, #30620, lsl #48
	movz x7, #42506, lsl #0
	movk x7, #26656, lsl #16
	movk x7, #32766, lsl #32
	movk x7, #44481, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	dup v0.16b, w8
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	movz x6, #128, lsl #0
	dup v5.16b, w6
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov w8, v0.s[0]
	lsl x8, x8, #56
	lsr x8, x8, #56
	add x9, x21, x23
	strb w8, [x9, #0]
	add x10, x23, #0
	cbnz x10, 220b
219:
	ldr x23, [x4, #0]
	ldr x24, [x4, #8]
	ldr x19, [x4, #16]
	ldr x20, [x4, #24]
	ldr x21, [x4, #32]
	ldr x22, [x4, #40]
	ret
	.p2align 6
