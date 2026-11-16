// The functions of `src/camellia.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_expand_key:
	sub sp, sp, #160
	add x3, sp, #0
	add x5, x3, #0
	add x3, x1, #0
	str x19, [x5, #0]
	str x20, [x5, #8]
	str x21, [x5, #16]
	str x22, [x5, #24]
	str x23, [x5, #32]
	str x24, [x5, #40]
	str x25, [x5, #48]
	str x26, [x5, #56]
	str x27, [x5, #64]
	str x28, [x5, #72]
	ldr x21, [x0, #0]
	str x21, [x5, #80]
	ldr x21, [x0, #8]
	str x21, [x5, #88]
	sub x22, x3, #16
	cbz x22, 20f
	ldr x21, [x0, #16]
	str x21, [x5, #96]
	sub x22, x3, #24
	cbz x22, 22f
	ldr x21, [x0, #24]
	str x21, [x5, #104]
	b 23f
22:
	movz x23, #0, lsl #0
	sub x23, x23, #1
	eor x21, x21, x23
	str x21, [x5, #104]
23:
	b 21f
20:
	movz x21, #0, lsl #0
	str x21, [x5, #96]
	str x21, [x5, #104]
21:
	sub x21, x3, #16
	movz x6, #33392, lsl #0
	movk x6, #60460, lsl #16
	movk x6, #10163, lsl #32
	movk x6, #58816, lsl #48
	movz x7, #34276, lsl #0
	movk x7, #13655, lsl #16
	movk x7, #3306, lsl #32
	movk x7, #16814, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #61219, lsl #0
	movk x6, #37739, lsl #16
	movk x6, #6469, lsl #32
	movk x6, #8613, lsl #48
	movz x7, #3821, lsl #0
	movk x7, #20047, lsl #16
	movk x7, #25885, lsl #32
	movk x7, #48530, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #47238, lsl #0
	movk x6, #36783, lsl #16
	movk x6, #60284, lsl #32
	movk x6, #52767, lsl #48
	movz x7, #12350, lsl #0
	movk x7, #24540, lsl #16
	movk x7, #50526, lsl #32
	movk x7, #6667, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #57766, lsl #0
	movk x6, #51769, lsl #16
	movk x6, #18389, lsl #32
	movk x6, #15709, lsl #48
	movz x7, #473, lsl #0
	movk x7, #54874, lsl #16
	movk x7, #22097, lsl #32
	movk x7, #19820, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #3467, lsl #0
	movk x6, #26266, lsl #16
	movk x6, #52475, lsl #32
	movk x6, #11696, lsl #48
	movz x7, #4724, lsl #0
	movk x7, #8235, lsl #16
	movk x7, #45552, lsl #32
	movk x7, #39300, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #19679, lsl #0
	movk x6, #49867, lsl #16
	movk x6, #32308, lsl #32
	movk x6, #1398, lsl #48
	movz x7, #46957, lsl #0
	movk x7, #12713, lsl #16
	movk x7, #6097, lsl #32
	movk x7, #55044, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #22548, lsl #0
	movk x6, #24890, lsl #16
	movk x6, #7134, lsl #32
	movk x6, #7185, lsl #48
	movz x7, #3890, lsl #0
	movk x7, #5788, lsl #16
	movk x7, #6227, lsl #32
	movk x7, #8946, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #17662, lsl #0
	movk x6, #45775, lsl #16
	movk x6, #46531, lsl #32
	movk x6, #37242, lsl #48
	movz x7, #2084, lsl #0
	movk x7, #43240, lsl #16
	movk x7, #64608, lsl #32
	movk x7, #20585, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #53418, lsl #0
	movk x6, #32160, lsl #16
	movk x6, #35233, lsl #32
	movk x6, #38754, lsl #48
	movz x7, #23380, lsl #0
	movk x7, #38174, lsl #16
	movk x7, #65504, lsl #32
	movk x7, #53860, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #50192, lsl #0
	movk x6, #18432, lsl #16
	movk x6, #63395, lsl #32
	movk x6, #56181, lsl #48
	movz x7, #906, lsl #0
	movk x7, #56038, lsl #16
	movk x7, #16137, lsl #32
	movk x7, #38109, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #23687, lsl #0
	movk x6, #643, lsl #16
	movk x6, #19149, lsl #32
	movk x6, #13200, lsl #48
	movz x7, #26483, lsl #0
	movk x7, #62454, lsl #16
	movk x7, #32669, lsl #32
	movk x7, #58047, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #39762, lsl #0
	movk x6, #9944, lsl #16
	movk x6, #14280, lsl #32
	movk x6, #15302, lsl #48
	movz x7, #38529, lsl #0
	movk x7, #19311, lsl #16
	movk x7, #48659, lsl #32
	movk x7, #11875, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #31209, lsl #0
	movk x6, #36007, lsl #16
	movk x6, #28319, lsl #32
	movk x6, #36540, lsl #48
	movz x7, #62761, lsl #0
	movk x7, #46841, lsl #16
	movk x7, #64815, lsl #32
	movk x7, #22964, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #39032, lsl #0
	movk x6, #27142, lsl #16
	movk x6, #18151, lsl #32
	movk x6, #47729, lsl #48
	movz x7, #9684, lsl #0
	movk x7, #17067, lsl #16
	movk x7, #41608, lsl #32
	movk x7, #64141, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #1906, lsl #0
	movk x6, #21945, lsl #16
	movk x6, #61176, lsl #32
	movk x6, #2732, lsl #48
	movz x7, #18742, lsl #0
	movk x7, #26666, lsl #16
	movk x7, #14396, lsl #32
	movk x7, #42225, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #10304, lsl #0
	movk x6, #31699, lsl #16
	movk x6, #51643, lsl #32
	movk x6, #49475, lsl #48
	movz x7, #58133, lsl #0
	movk x7, #62637, lsl #16
	movk x7, #51063, lsl #32
	movk x7, #40576, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	movz x0, #255, lsl #0
	movk x0, #65535, lsl #16
	movk x0, #65280, lsl #32
	movk x0, #65535, lsl #48
	movz x3, #65024, lsl #0
	movk x3, #254, lsl #32
	movz x4, #256, lsl #0
	movk x4, #1, lsl #32
	movz x9, #65535, lsl #0
	movk x9, #255, lsl #32
	movk x9, #65280, lsl #48
	movz x13, #0, lsl #0
	movk x13, #65024, lsl #16
	movk x13, #254, lsl #48
	movz x14, #0, lsl #0
	movk x14, #256, lsl #16
	movk x14, #1, lsl #48
	movz x15, #0, lsl #0
	movk x15, #127, lsl #16
	movk x15, #32512, lsl #32
	ldr x6, [x5, #80]
	rev x6, x6
	ldr x7, [x5, #88]
	rev x7, x7
	ldr x8, [x5, #96]
	rev x8, x8
	eor x6, x6, x8
	ldr x8, [x5, #104]
	rev x8, x8
	eor x7, x7, x8
	movz x8, #37003, lsl #0
	movk x8, #15308, lsl #16
	movk x8, #26239, lsl #32
	movk x8, #41118, lsl #48
	eor x10, x6, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	movz x8, #29618, lsl #0
	movk x8, #19626, lsl #16
	movk x8, #59480, lsl #32
	movk x8, #46714, lsl #48
	eor x10, x7, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	ldr x8, [x5, #80]
	rev x8, x8
	eor x6, x6, x8
	ldr x8, [x5, #88]
	rev x8, x8
	eor x7, x7, x8
	movz x8, #33470, lsl #0
	movk x8, #59727, lsl #16
	movk x8, #14127, lsl #32
	movk x8, #50927, lsl #48
	eor x10, x6, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	movz x8, #28444, lsl #0
	movk x8, #61907, lsl #16
	movk x8, #21413, lsl #32
	movk x8, #21759, lsl #48
	eor x10, x7, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	rev x8, x6
	str x8, [x5, #128]
	rev x8, x7
	str x8, [x5, #136]
	cbz x21, 24f
	ldr x8, [x5, #96]
	rev x8, x8
	eor x6, x6, x8
	ldr x8, [x5, #104]
	rev x8, x8
	eor x7, x7, x8
	movz x8, #11549, lsl #0
	movk x8, #56936, lsl #16
	movk x8, #10234, lsl #32
	movk x8, #4325, lsl #48
	eor x10, x6, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x7, x7, x10
	movz x8, #49661, lsl #0
	movk x8, #46054, lsl #16
	movk x8, #35010, lsl #32
	movk x8, #45142, lsl #48
	eor x10, x7, x8
	and x11, x10, x0
	and x12, x3, x10, ror #63
	and x16, x4, x10, ror #7
	orr x11, x11, x12
	orr x10, x11, x16
	dup v0.2d, x10
	eor v1.16b, v0.16b, v4.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v0.16b, v6.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	umov x10, v0.d[0]
	and x11, x10, x9
	and x12, x13, x10, ror #63
	and x16, x14, x10, ror #7
	and x17, x15, x10, ror #1
	and x10, x4, x10, ror #8
	orr x17, x17, x10, ror #49
	orr x11, x11, x12
	orr x11, x11, x16
	orr x10, x11, x17
	lsr x11, x10, #32
	add w12, w10, #0
	eor w16, w11, w11, ror #8
	eor w16, w16, w11, ror #16
	extr w17, w12, w12, #8
	eor w17, w17, w12, ror #16
	eor w17, w17, w12, ror #24
	eor w16, w16, w17
	eor w12, w11, w11, ror #24
	eor w12, w12, w17
	lsl x10, x16, #32
	orr x10, x10, x12
	eor x6, x6, x10
	rev x8, x6
	str x8, [x5, #144]
	rev x8, x7
	str x8, [x5, #152]
	ldr x6, [x5, #80]
	rev x6, x6
	ldr x7, [x5, #88]
	rev x7, x7
	ldr x8, [x5, #96]
	rev x8, x8
	ldr x9, [x5, #104]
	rev x9, x9
	ldr x10, [x5, #128]
	rev x10, x10
	ldr x11, [x5, #136]
	rev x11, x11
	ldr x12, [x5, #144]
	rev x12, x12
	ldr x13, [x5, #152]
	rev x13, x13
	add x21, x6, #0
	rev x21, x21
	str x21, [x2, #0]
	add x21, x7, #0
	rev x21, x21
	str x21, [x2, #8]
	add x21, x12, #0
	rev x21, x21
	str x21, [x2, #16]
	add x21, x13, #0
	rev x21, x21
	str x21, [x2, #24]
	lsl x21, x8, #15
	lsr x22, x9, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #32]
	lsl x21, x9, #15
	lsr x22, x8, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #40]
	lsl x21, x10, #15
	lsr x22, x11, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #48]
	lsl x21, x11, #15
	lsr x22, x10, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #56]
	lsl x21, x8, #30
	lsr x22, x9, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #64]
	lsl x21, x9, #30
	lsr x22, x8, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #72]
	lsl x21, x12, #30
	lsr x22, x13, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #80]
	lsl x21, x13, #30
	lsr x22, x12, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #88]
	lsl x21, x6, #45
	lsr x22, x7, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #96]
	lsl x21, x7, #45
	lsr x22, x6, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #104]
	lsl x21, x10, #45
	lsr x22, x11, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #112]
	lsl x21, x11, #45
	lsr x22, x10, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #120]
	lsl x21, x6, #60
	lsr x22, x7, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #128]
	lsl x21, x7, #60
	lsr x22, x6, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #136]
	lsl x21, x8, #60
	lsr x22, x9, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #144]
	lsl x21, x9, #60
	lsr x22, x8, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #152]
	lsl x21, x12, #60
	lsr x22, x13, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #160]
	lsl x21, x13, #60
	lsr x22, x12, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #168]
	lsl x21, x7, #13
	lsr x22, x6, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #176]
	lsl x21, x6, #13
	lsr x22, x7, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #184]
	lsl x21, x11, #13
	lsr x22, x10, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #192]
	lsl x21, x10, #13
	lsr x22, x11, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #200]
	lsl x21, x9, #30
	lsr x22, x8, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #208]
	lsl x21, x8, #30
	lsr x22, x9, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #216]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #224]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #232]
	lsl x21, x7, #47
	lsr x22, x6, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #240]
	lsl x21, x6, #47
	lsr x22, x7, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #248]
	lsl x21, x13, #47
	lsr x22, x12, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #256]
	lsl x21, x12, #47
	lsr x22, x13, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #264]
	b 25f
24:
	ldr x6, [x5, #80]
	rev x6, x6
	ldr x7, [x5, #88]
	rev x7, x7
	ldr x8, [x5, #96]
	rev x8, x8
	ldr x9, [x5, #104]
	rev x9, x9
	ldr x10, [x5, #128]
	rev x10, x10
	ldr x11, [x5, #136]
	rev x11, x11
	ldr x12, [x5, #144]
	rev x12, x12
	ldr x13, [x5, #152]
	rev x13, x13
	add x21, x6, #0
	rev x21, x21
	str x21, [x2, #0]
	add x21, x7, #0
	rev x21, x21
	str x21, [x2, #8]
	add x21, x10, #0
	rev x21, x21
	str x21, [x2, #16]
	add x21, x11, #0
	rev x21, x21
	str x21, [x2, #24]
	lsl x21, x6, #15
	lsr x22, x7, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #32]
	lsl x21, x7, #15
	lsr x22, x6, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #40]
	lsl x21, x10, #15
	lsr x22, x11, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #48]
	lsl x21, x11, #15
	lsr x22, x10, #49
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #56]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #64]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #72]
	lsl x21, x6, #45
	lsr x22, x7, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #80]
	lsl x21, x7, #45
	lsr x22, x6, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #88]
	lsl x21, x10, #45
	lsr x22, x11, #19
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #96]
	lsl x21, x7, #60
	lsr x22, x6, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #104]
	lsl x21, x10, #60
	lsr x22, x11, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #112]
	lsl x21, x11, #60
	lsr x22, x10, #4
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #120]
	lsl x21, x7, #13
	lsr x22, x6, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #128]
	lsl x21, x6, #13
	lsr x22, x7, #51
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #136]
	lsl x21, x7, #30
	lsr x22, x6, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #144]
	lsl x21, x6, #30
	lsr x22, x7, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #152]
	lsl x21, x11, #30
	lsr x22, x10, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #160]
	lsl x21, x10, #30
	lsr x22, x11, #34
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #168]
	lsl x21, x7, #47
	lsr x22, x6, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #176]
	lsl x21, x6, #47
	lsr x22, x7, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #184]
	lsl x21, x11, #47
	lsr x22, x10, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #192]
	lsl x21, x10, #47
	lsr x22, x11, #17
	orr x21, x21, x22
	rev x21, x21
	str x21, [x2, #200]
25:
	ldr x19, [x5, #0]
	ldr x20, [x5, #8]
	ldr x21, [x5, #16]
	ldr x22, [x5, #24]
	ldr x23, [x5, #32]
	ldr x24, [x5, #40]
	ldr x25, [x5, #48]
	ldr x26, [x5, #56]
	ldr x27, [x5, #64]
	ldr x28, [x5, #72]
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
	add sp, sp, #160
	ret
	.p2align 6

vg_camellia_ecb_encrypt:
	sub sp, sp, #3248
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #2944]
	str x20, [x5, #2952]
	str x21, [x5, #2960]
	str x22, [x5, #2968]
	str x23, [x5, #2976]
	str x24, [x5, #2984]
	str x25, [x5, #2992]
	str x26, [x5, #3000]
	str x27, [x5, #3008]
	str x28, [x5, #3016]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #384]
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x5, #392]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #400]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	str x21, [x5, #408]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #255, lsl #32
	str x21, [x5, #416]
	sub x21, x1, #18
	cbz x21, 20f
	add x4, x5, #0
	add x4, x4, #2816
	movz x22, #34, lsl #0
	b 21f
20:
	add x4, x5, #0
	add x4, x4, #2304
	movz x22, #26, lsl #0
21:
	add x1, x5, #0
	add x1, x1, #768
22:
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	add x0, x0, #8
	sub x22, x22, #1
	cbnz x22, 22b
	cbz x3, 23f
25:
	lsr x21, x3, #3
	cbnz x21, 26f
	add x16, x3, #0
	b 27f
26:
	movz x16, #8, lsl #0
27:
	add x14, x2, #0
	add x15, x5, #0
	add x15, x15, #3024
	add x17, x16, #0
28:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x5, #3032]
	ldr x7, [x5, #3048]
	ldr x8, [x5, #3064]
	ldr x9, [x5, #3080]
	ldr x10, [x5, #3096]
	ldr x11, [x5, #3112]
	ldr x12, [x5, #3128]
	ldr x13, [x5, #3144]
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #3024]
	ldr x7, [x5, #3040]
	ldr x8, [x5, #3056]
	ldr x9, [x5, #3072]
	ldr x10, [x5, #3088]
	ldr x11, [x5, #3104]
	ldr x12, [x5, #3120]
	ldr x13, [x5, #3136]
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x21, [x5, #576]
	ldr x23, [x1, #64]
	eor x21, x21, x23
	str x21, [x5, #576]
	ldr x21, [x5, #584]
	ldr x23, [x1, #72]
	eor x21, x21, x23
	str x21, [x5, #584]
	ldr x21, [x5, #592]
	ldr x23, [x1, #80]
	eor x21, x21, x23
	str x21, [x5, #592]
	ldr x21, [x5, #600]
	ldr x23, [x1, #88]
	eor x21, x21, x23
	str x21, [x5, #600]
	ldr x21, [x5, #608]
	ldr x23, [x1, #96]
	eor x21, x21, x23
	str x21, [x5, #608]
	ldr x21, [x5, #616]
	ldr x23, [x1, #104]
	eor x21, x21, x23
	str x21, [x5, #616]
	ldr x21, [x5, #624]
	ldr x23, [x1, #112]
	eor x21, x21, x23
	str x21, [x5, #624]
	ldr x21, [x5, #632]
	ldr x23, [x1, #120]
	eor x21, x21, x23
	str x21, [x5, #632]
	add x1, x1, #128
29:
	add x0, x1, #384
210:
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
	add x1, x1, #128
	sub x21, x1, x0
	cbnz x21, 210b
	sub x21, x1, x4
	cbnz x21, 211f
	b 212f
211:
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x24, [x5, #384]
	ldr x23, [x1, #120]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #112]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #104]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #96]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #88]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #80]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #72]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #64]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #112]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #104]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #96]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #88]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #80]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #72]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #64]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #120]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #48]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #40]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #32]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #24]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #16]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #8]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #0]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #56]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #384]
	ldr x23, [x1, #56]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #48]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #40]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #32]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #24]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #16]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #8]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #0]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	add x1, x1, #128
212:
	sub x21, x1, x4
	cbnz x21, 29b
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #3032]
	str x7, [x5, #3048]
	str x8, [x5, #3064]
	str x9, [x5, #3080]
	str x10, [x5, #3096]
	str x11, [x5, #3112]
	str x12, [x5, #3128]
	str x13, [x5, #3144]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #3024]
	str x7, [x5, #3040]
	str x8, [x5, #3056]
	str x9, [x5, #3072]
	str x10, [x5, #3088]
	str x11, [x5, #3104]
	str x12, [x5, #3120]
	str x13, [x5, #3136]
	lsr x21, x3, #3
	cbnz x21, 213f
	add x16, x3, #0
	b 214f
213:
	movz x16, #8, lsl #0
214:
	add x14, x5, #0
	add x14, x14, #3024
	add x15, x2, #0
	add x17, x16, #0
215:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 215b
	sub x3, x3, x16
	add x2, x2, #128
	cbnz x3, 25b
	b 24f
23:
24:
	ldr x19, [x5, #2944]
	ldr x20, [x5, #2952]
	ldr x21, [x5, #2960]
	ldr x22, [x5, #2968]
	ldr x23, [x5, #2976]
	ldr x24, [x5, #2984]
	ldr x25, [x5, #2992]
	ldr x26, [x5, #3000]
	ldr x27, [x5, #3008]
	ldr x28, [x5, #3016]
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
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3248
	ret
	.p2align 6

vg_camellia_ecb_decrypt:
	sub sp, sp, #3248
	add x4, sp, #0
	add x5, x4, #0
	str x19, [x5, #2944]
	str x20, [x5, #2952]
	str x21, [x5, #2960]
	str x22, [x5, #2968]
	str x23, [x5, #2976]
	str x24, [x5, #2984]
	str x25, [x5, #2992]
	str x26, [x5, #3000]
	str x27, [x5, #3008]
	str x28, [x5, #3016]
	movz x21, #255, lsl #0
	movk x21, #255, lsl #16
	movk x21, #255, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #384]
	movz x21, #65280, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #65280, lsl #32
	movk x21, #65280, lsl #48
	str x21, [x5, #392]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #32
	movk x21, #255, lsl #48
	str x21, [x5, #400]
	movz x21, #65280, lsl #0
	movk x21, #255, lsl #16
	str x21, [x5, #408]
	movz x21, #0, lsl #0
	movk x21, #65280, lsl #16
	movk x21, #255, lsl #32
	str x21, [x5, #416]
	sub x21, x1, #18
	cbz x21, 20f
	add x4, x5, #0
	add x4, x4, #2816
	add x0, x0, #256
	movz x22, #30, lsl #0
	b 21f
20:
	add x4, x5, #0
	add x4, x4, #2304
	add x0, x0, #192
	movz x22, #22, lsl #0
21:
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	ldr x6, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	sub x0, x0, #8
22:
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	sub x0, x0, #8
	sub x22, x22, #1
	cbnz x22, 22b
	sub x0, x0, #8
	ldr x6, [x0, #0]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	ldr x6, [x0, #8]
	add x7, x6, #0
	add x8, x6, #0
	add x9, x6, #0
	add x10, x6, #0
	add x11, x6, #0
	add x12, x6, #0
	add x13, x6, #0
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x1, #0]
	str x7, [x1, #8]
	str x8, [x1, #16]
	str x9, [x1, #24]
	str x10, [x1, #32]
	str x11, [x1, #40]
	str x12, [x1, #48]
	str x13, [x1, #56]
	add x1, x1, #64
	cbz x3, 23f
25:
	lsr x21, x3, #3
	cbnz x21, 26f
	add x16, x3, #0
	b 27f
26:
	movz x16, #8, lsl #0
27:
	add x14, x2, #0
	add x15, x5, #0
	add x15, x15, #3024
	add x17, x16, #0
28:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	add x1, x5, #0
	add x1, x1, #768
	ldr x6, [x5, #3032]
	ldr x7, [x5, #3048]
	ldr x8, [x5, #3064]
	ldr x9, [x5, #3080]
	ldr x10, [x5, #3096]
	ldr x11, [x5, #3112]
	ldr x12, [x5, #3128]
	ldr x13, [x5, #3144]
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #3024]
	ldr x7, [x5, #3040]
	ldr x8, [x5, #3056]
	ldr x9, [x5, #3072]
	ldr x10, [x5, #3088]
	ldr x11, [x5, #3104]
	ldr x12, [x5, #3120]
	ldr x13, [x5, #3136]
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	ldr x21, [x5, #576]
	ldr x23, [x1, #64]
	eor x21, x21, x23
	str x21, [x5, #576]
	ldr x21, [x5, #584]
	ldr x23, [x1, #72]
	eor x21, x21, x23
	str x21, [x5, #584]
	ldr x21, [x5, #592]
	ldr x23, [x1, #80]
	eor x21, x21, x23
	str x21, [x5, #592]
	ldr x21, [x5, #600]
	ldr x23, [x1, #88]
	eor x21, x21, x23
	str x21, [x5, #600]
	ldr x21, [x5, #608]
	ldr x23, [x1, #96]
	eor x21, x21, x23
	str x21, [x5, #608]
	ldr x21, [x5, #616]
	ldr x23, [x1, #104]
	eor x21, x21, x23
	str x21, [x5, #616]
	ldr x21, [x5, #624]
	ldr x23, [x1, #112]
	eor x21, x21, x23
	str x21, [x5, #624]
	ldr x21, [x5, #632]
	ldr x23, [x1, #120]
	eor x21, x21, x23
	str x21, [x5, #632]
	add x1, x1, #128
29:
	add x0, x1, #384
210:
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #576]
	eor x6, x6, x21
	str x6, [x5, #576]
	ldr x21, [x5, #584]
	eor x7, x7, x21
	str x7, [x5, #584]
	ldr x21, [x5, #592]
	eor x8, x8, x21
	str x8, [x5, #592]
	ldr x21, [x5, #600]
	eor x9, x9, x21
	str x9, [x5, #600]
	ldr x21, [x5, #608]
	eor x10, x10, x21
	str x10, [x5, #608]
	ldr x21, [x5, #616]
	eor x11, x11, x21
	str x11, [x5, #616]
	ldr x21, [x5, #624]
	eor x12, x12, x21
	str x12, [x5, #624]
	ldr x21, [x5, #632]
	eor x13, x13, x21
	str x13, [x5, #632]
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	ldr x24, [x5, #400]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	movz x28, #0, lsl #0
	sub x28, x28, #1
	eor x14, x13, x7
	eor x15, x11, x9
	eor x16, x8, x14
	eor x17, x12, x6
	eor x19, x6, x15
	eor x20, x10, x7
	eor x21, x10, x16
	eor x22, x12, x15
	eor x23, x8, x17
	eor x24, x16, x17
	eor x25, x13, x12
	eor x26, x13, x17
	eor x26, x26, x28
	eor x27, x12, x9
	str x26, [x5, #0]
	eor x26, x11, x7
	str x13, [x5, #8]
	eor x13, x11, x6
	eor x11, x11, x16
	eor x17, x10, x17
	eor x10, x10, x25
	eor x9, x9, x6
	eor x9, x9, x28
	eor x6, x8, x19
	eor x8, x8, x20
	eor x8, x8, x28
	eor x25, x7, x22
	eor x25, x25, x28
	str x25, [x5, #16]
	eor x25, x14, x19
	eor x14, x14, x22
	eor x22, x15, x20
	str x25, [x5, #24]
	eor x25, x15, x21
	eor x15, x15, x24
	str x15, [x5, #32]
	eor x15, x16, x19
	eor x15, x15, x28
	eor x16, x16, x27
	eor x16, x16, x28
	eor x19, x19, x20
	eor x19, x19, x28
	eor x13, x21, x13
	eor x13, x13, x28
	eor x26, x23, x26
	eor x26, x26, x28
	eor x23, x23, x22
	eor x23, x23, x28
	ldr x22, [x5, #8]
	eor x20, x22, x12
	eor x20, x20, x28
	eor x20, x20, x12
	eor x22, x22, x7
	eor x22, x22, x28
	and x7, x8, x10
	and x12, x20, x26
	eor x12, x12, x7
	and x27, x21, x13
	eor x27, x27, x7
	and x7, x6, x15
	str x6, [x5, #8]
	and x6, x14, x11
	eor x6, x6, x7
	str x14, [x5, #40]
	and x14, x24, x9
	eor x14, x14, x7
	and x7, x17, x25
	str x17, [x5, #48]
	and x17, x19, x23
	eor x17, x17, x7
	str x19, [x5, #56]
	ldr x19, [x5, #16]
	str x24, [x5, #64]
	ldr x24, [x5, #0]
	str x21, [x5, #72]
	and x21, x19, x24
	eor x21, x21, x7
	eor x12, x12, x17
	eor x27, x27, x21
	eor x6, x6, x17
	eor x14, x14, x21
	ldr x21, [x5, #32]
	eor x12, x12, x21
	ldr x21, [x5, #24]
	eor x27, x27, x21
	eor x6, x6, x22
	eor x14, x14, x16
	eor x16, x12, x27
	and x12, x12, x6
	eor x22, x14, x12
	and x21, x16, x22
	eor x21, x21, x27
	eor x17, x6, x14
	eor x27, x27, x12
	and x27, x27, x17
	eor x27, x27, x14
	eor x6, x6, x27
	eor x17, x22, x27
	and x14, x14, x17
	eor x6, x14, x6
	eor x22, x22, x14
	and x22, x21, x22
	eor x16, x16, x22
	eor x22, x16, x6
	eor x14, x21, x27
	eor x17, x21, x16
	eor x12, x27, x6
	eor x7, x14, x22
	and x10, x12, x10
	and x26, x6, x26
	and x13, x27, x13
	and x15, x17, x15
	and x11, x16, x11
	and x9, x21, x9
	and x25, x14, x25
	and x23, x7, x23
	and x24, x22, x24
	and x12, x12, x8
	and x6, x6, x20
	ldr x20, [x5, #72]
	and x27, x27, x20
	ldr x20, [x5, #8]
	and x17, x17, x20
	ldr x20, [x5, #40]
	and x16, x16, x20
	ldr x20, [x5, #64]
	and x21, x21, x20
	ldr x20, [x5, #48]
	and x14, x14, x20
	ldr x20, [x5, #56]
	and x7, x7, x20
	and x22, x22, x19
	eor x23, x26, x23
	eor x15, x15, x9
	eor x19, x25, x24
	eor x20, x10, x7
	eor x27, x27, x23
	eor x8, x17, x15
	str x15, [x5, #16]
	eor x15, x14, x19
	eor x21, x13, x21
	eor x25, x25, x22
	eor x24, x24, x12
	eor x12, x12, x6
	eor x16, x16, x8
	eor x7, x7, x15
	str x7, [x5, #56]
	eor x7, x20, x27
	eor x10, x10, x13
	eor x26, x26, x11
	eor x9, x9, x20
	eor x6, x6, x25
	eor x17, x17, x27
	eor x14, x14, x23
	eor x22, x22, x24
	ldr x23, [x5, #16]
	eor x23, x23, x12
	eor x10, x19, x10
	eor x8, x8, x21
	eor x15, x15, x12
	eor x21, x21, x24
	eor x25, x25, x14
	ldr x14, [x5, #56]
	eor x24, x16, x14
	eor x16, x16, x7
	eor x11, x14, x23
	eor x11, x11, x28
	eor x7, x7, x6
	eor x7, x7, x28
	eor x26, x26, x9
	eor x9, x17, x21
	eor x9, x9, x28
	eor x22, x22, x16
	eor x22, x22, x28
	eor x13, x8, x25
	eor x12, x15, x26
	eor x12, x12, x28
	add x8, x7, #0
	add x7, x22, #0
	add x6, x24, #0
	ldr x24, [x5, #408]
	add x22, x13, #0
	eor x21, x13, x12
	and x21, x21, x24
	eor x13, x13, x21
	eor x21, x12, x11
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x11, x10
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x10, x9
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x9, x8
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x8, x7
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x7, x6
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x6, x22
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #416]
	add x22, x6, #0
	eor x21, x6, x7
	and x21, x21, x24
	eor x6, x6, x21
	eor x21, x7, x8
	and x21, x21, x24
	eor x7, x7, x21
	eor x21, x8, x9
	and x21, x21, x24
	eor x8, x8, x21
	eor x21, x9, x10
	and x21, x21, x24
	eor x9, x9, x21
	eor x21, x10, x11
	and x21, x21, x24
	eor x10, x10, x21
	eor x21, x11, x12
	and x21, x21, x24
	eor x11, x11, x21
	eor x21, x12, x13
	and x21, x21, x24
	eor x12, x12, x21
	eor x21, x13, x22
	and x21, x21, x24
	eor x13, x13, x21
	ldr x24, [x5, #384]
	ldr x23, [x5, #392]
	ror x21, x6, #8
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x6, #56
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #8
	and x21, x21, x23
	eor x6, x6, x21
	ror x21, x6, #40
	and x21, x21, x24
	eor x6, x6, x21
	ror x21, x7, #8
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x7, #56
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #8
	and x21, x21, x23
	eor x7, x7, x21
	ror x21, x7, #40
	and x21, x21, x24
	eor x7, x7, x21
	ror x21, x8, #8
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x8, #56
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #8
	and x21, x21, x23
	eor x8, x8, x21
	ror x21, x8, #40
	and x21, x21, x24
	eor x8, x8, x21
	ror x21, x9, #8
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x9, #56
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #8
	and x21, x21, x23
	eor x9, x9, x21
	ror x21, x9, #40
	and x21, x21, x24
	eor x9, x9, x21
	ror x21, x10, #8
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x10, #56
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #8
	and x21, x21, x23
	eor x10, x10, x21
	ror x21, x10, #40
	and x21, x21, x24
	eor x10, x10, x21
	ror x21, x11, #8
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x11, #56
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #8
	and x21, x21, x23
	eor x11, x11, x21
	ror x21, x11, #40
	and x21, x21, x24
	eor x11, x11, x21
	ror x21, x12, #8
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x12, #56
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #8
	and x21, x21, x23
	eor x12, x12, x21
	ror x21, x12, #40
	and x21, x21, x24
	eor x12, x12, x21
	ror x21, x13, #8
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ror x21, x13, #56
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #8
	and x21, x21, x23
	eor x13, x13, x21
	ror x21, x13, #40
	and x21, x21, x24
	eor x13, x13, x21
	ldr x21, [x5, #512]
	eor x6, x6, x21
	str x6, [x5, #512]
	ldr x21, [x5, #520]
	eor x7, x7, x21
	str x7, [x5, #520]
	ldr x21, [x5, #528]
	eor x8, x8, x21
	str x8, [x5, #528]
	ldr x21, [x5, #536]
	eor x9, x9, x21
	str x9, [x5, #536]
	ldr x21, [x5, #544]
	eor x10, x10, x21
	str x10, [x5, #544]
	ldr x21, [x5, #552]
	eor x11, x11, x21
	str x11, [x5, #552]
	ldr x21, [x5, #560]
	eor x12, x12, x21
	str x12, [x5, #560]
	ldr x21, [x5, #568]
	eor x13, x13, x21
	str x13, [x5, #568]
	add x1, x1, #128
	sub x21, x1, x0
	cbnz x21, 210b
	sub x21, x1, x4
	cbnz x21, 211f
	b 212f
211:
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x24, [x5, #384]
	ldr x23, [x1, #120]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #112]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #104]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #96]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #88]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #80]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #72]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #64]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #112]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #104]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #96]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #88]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #80]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #72]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #64]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #120]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #576]
	str x7, [x5, #584]
	str x8, [x5, #592]
	str x9, [x5, #600]
	str x10, [x5, #608]
	str x11, [x5, #616]
	str x12, [x5, #624]
	str x13, [x5, #632]
	ldr x6, [x5, #512]
	ldr x7, [x5, #520]
	ldr x8, [x5, #528]
	ldr x9, [x5, #536]
	ldr x10, [x5, #544]
	ldr x11, [x5, #552]
	ldr x12, [x5, #560]
	ldr x13, [x5, #568]
	ldr x24, [x5, #392]
	add x22, x13, #0
	ldr x23, [x1, #48]
	and x21, x12, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #40]
	and x21, x11, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #32]
	and x21, x10, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #24]
	and x21, x9, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #16]
	and x21, x8, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #8]
	and x21, x7, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #0]
	and x21, x6, x23
	ror x21, x21, #56
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #56]
	and x21, x22, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	ldr x24, [x5, #384]
	ldr x23, [x1, #56]
	orr x21, x13, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x13, x13, x21
	ldr x23, [x1, #48]
	orr x21, x12, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x12, x12, x21
	ldr x23, [x1, #40]
	orr x21, x11, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x11, x11, x21
	ldr x23, [x1, #32]
	orr x21, x10, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x10, x10, x21
	ldr x23, [x1, #24]
	orr x21, x9, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x9, x9, x21
	ldr x23, [x1, #16]
	orr x21, x8, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x8, x8, x21
	ldr x23, [x1, #8]
	orr x21, x7, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x7, x7, x21
	ldr x23, [x1, #0]
	orr x21, x6, x23
	ror x21, x21, #8
	and x21, x21, x24
	eor x6, x6, x21
	str x6, [x5, #512]
	str x7, [x5, #520]
	str x8, [x5, #528]
	str x9, [x5, #536]
	str x10, [x5, #544]
	str x11, [x5, #552]
	str x12, [x5, #560]
	str x13, [x5, #568]
	add x1, x1, #128
212:
	sub x21, x1, x4
	cbnz x21, 29b
	ldr x21, [x1, #64]
	eor x6, x6, x21
	ldr x21, [x1, #72]
	eor x7, x7, x21
	ldr x21, [x1, #80]
	eor x8, x8, x21
	ldr x21, [x1, #88]
	eor x9, x9, x21
	ldr x21, [x1, #96]
	eor x10, x10, x21
	ldr x21, [x1, #104]
	eor x11, x11, x21
	ldr x21, [x1, #112]
	eor x12, x12, x21
	ldr x21, [x1, #120]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #3032]
	str x7, [x5, #3048]
	str x8, [x5, #3064]
	str x9, [x5, #3080]
	str x10, [x5, #3096]
	str x11, [x5, #3112]
	str x12, [x5, #3128]
	str x13, [x5, #3144]
	ldr x6, [x5, #576]
	ldr x7, [x5, #584]
	ldr x8, [x5, #592]
	ldr x9, [x5, #600]
	ldr x10, [x5, #608]
	ldr x11, [x5, #616]
	ldr x12, [x5, #624]
	ldr x13, [x5, #632]
	ldr x21, [x1, #0]
	eor x6, x6, x21
	ldr x21, [x1, #8]
	eor x7, x7, x21
	ldr x21, [x1, #16]
	eor x8, x8, x21
	ldr x21, [x1, #24]
	eor x9, x9, x21
	ldr x21, [x1, #32]
	eor x10, x10, x21
	ldr x21, [x1, #40]
	eor x11, x11, x21
	ldr x21, [x1, #48]
	eor x12, x12, x21
	ldr x21, [x1, #56]
	eor x13, x13, x21
	movz x14, #0, lsl #0
	movk x14, #65535, lsl #16
	movz x15, #65280, lsl #0
	movk x15, #65280, lsl #32
	movz x17, #21845, lsl #0
	movk x17, #21845, lsl #16
	movk x17, #21845, lsl #32
	movk x17, #21845, lsl #48
	movz x19, #13107, lsl #0
	movk x19, #13107, lsl #16
	movk x19, #13107, lsl #32
	movk x19, #13107, lsl #48
	movz x20, #3855, lsl #0
	movk x20, #3855, lsl #16
	movk x20, #3855, lsl #32
	movk x20, #3855, lsl #48
	lsr x21, x6, #1
	eor x21, x21, x7
	and x21, x21, x17
	eor x7, x7, x21
	ror x21, x21, #63
	eor x6, x6, x21
	lsr x21, x8, #1
	eor x21, x21, x9
	and x21, x21, x17
	eor x9, x9, x21
	ror x21, x21, #63
	eor x8, x8, x21
	lsr x21, x10, #1
	eor x21, x21, x11
	and x21, x21, x17
	eor x11, x11, x21
	ror x21, x21, #63
	eor x10, x10, x21
	lsr x21, x12, #1
	eor x21, x21, x13
	and x21, x21, x17
	eor x13, x13, x21
	ror x21, x21, #63
	eor x12, x12, x21
	lsr x21, x6, #2
	eor x21, x21, x8
	and x21, x21, x19
	eor x8, x8, x21
	ror x21, x21, #62
	eor x6, x6, x21
	lsr x21, x7, #2
	eor x21, x21, x9
	and x21, x21, x19
	eor x9, x9, x21
	ror x21, x21, #62
	eor x7, x7, x21
	lsr x21, x10, #2
	eor x21, x21, x12
	and x21, x21, x19
	eor x12, x12, x21
	ror x21, x21, #62
	eor x10, x10, x21
	lsr x21, x11, #2
	eor x21, x21, x13
	and x21, x21, x19
	eor x13, x13, x21
	ror x21, x21, #62
	eor x11, x11, x21
	lsr x21, x6, #4
	eor x21, x21, x10
	and x21, x21, x20
	eor x10, x10, x21
	ror x21, x21, #60
	eor x6, x6, x21
	lsr x21, x7, #4
	eor x21, x21, x11
	and x21, x21, x20
	eor x11, x11, x21
	ror x21, x21, #60
	eor x7, x7, x21
	lsr x21, x8, #4
	eor x21, x21, x12
	and x21, x21, x20
	eor x12, x12, x21
	ror x21, x21, #60
	eor x8, x8, x21
	lsr x21, x9, #4
	eor x21, x21, x13
	and x21, x21, x20
	eor x13, x13, x21
	ror x21, x21, #60
	eor x9, x9, x21
	lsr x21, x6, #8
	eor x21, x21, x6
	and x21, x21, x15
	eor x6, x6, x21
	ror x21, x21, #56
	eor x6, x6, x21
	lsr x21, x7, #8
	eor x21, x21, x7
	and x21, x21, x15
	eor x7, x7, x21
	ror x21, x21, #56
	eor x7, x7, x21
	lsr x21, x8, #8
	eor x21, x21, x8
	and x21, x21, x15
	eor x8, x8, x21
	ror x21, x21, #56
	eor x8, x8, x21
	lsr x21, x9, #8
	eor x21, x21, x9
	and x21, x21, x15
	eor x9, x9, x21
	ror x21, x21, #56
	eor x9, x9, x21
	lsr x21, x10, #8
	eor x21, x21, x10
	and x21, x21, x15
	eor x10, x10, x21
	ror x21, x21, #56
	eor x10, x10, x21
	lsr x21, x11, #8
	eor x21, x21, x11
	and x21, x21, x15
	eor x11, x11, x21
	ror x21, x21, #56
	eor x11, x11, x21
	lsr x21, x12, #8
	eor x21, x21, x12
	and x21, x21, x15
	eor x12, x12, x21
	ror x21, x21, #56
	eor x12, x12, x21
	lsr x21, x13, #8
	eor x21, x21, x13
	and x21, x21, x15
	eor x13, x13, x21
	ror x21, x21, #56
	eor x13, x13, x21
	lsr x21, x6, #16
	eor x21, x21, x6
	and x21, x21, x14
	eor x6, x6, x21
	ror x21, x21, #48
	eor x6, x6, x21
	lsr x21, x7, #16
	eor x21, x21, x7
	and x21, x21, x14
	eor x7, x7, x21
	ror x21, x21, #48
	eor x7, x7, x21
	lsr x21, x8, #16
	eor x21, x21, x8
	and x21, x21, x14
	eor x8, x8, x21
	ror x21, x21, #48
	eor x8, x8, x21
	lsr x21, x9, #16
	eor x21, x21, x9
	and x21, x21, x14
	eor x9, x9, x21
	ror x21, x21, #48
	eor x9, x9, x21
	lsr x21, x10, #16
	eor x21, x21, x10
	and x21, x21, x14
	eor x10, x10, x21
	ror x21, x21, #48
	eor x10, x10, x21
	lsr x21, x11, #16
	eor x21, x21, x11
	and x21, x21, x14
	eor x11, x11, x21
	ror x21, x21, #48
	eor x11, x11, x21
	lsr x21, x12, #16
	eor x21, x21, x12
	and x21, x21, x14
	eor x12, x12, x21
	ror x21, x21, #48
	eor x12, x12, x21
	lsr x21, x13, #16
	eor x21, x21, x13
	and x21, x21, x14
	eor x13, x13, x21
	ror x21, x21, #48
	eor x13, x13, x21
	str x6, [x5, #3024]
	str x7, [x5, #3040]
	str x8, [x5, #3056]
	str x9, [x5, #3072]
	str x10, [x5, #3088]
	str x11, [x5, #3104]
	str x12, [x5, #3120]
	str x13, [x5, #3136]
	lsr x21, x3, #3
	cbnz x21, 213f
	add x16, x3, #0
	b 214f
213:
	movz x16, #8, lsl #0
214:
	add x14, x5, #0
	add x14, x14, #3024
	add x15, x2, #0
	add x17, x16, #0
215:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 215b
	sub x3, x3, x16
	add x2, x2, #128
	cbnz x3, 25b
	b 24f
23:
24:
	ldr x19, [x5, #2944]
	ldr x20, [x5, #2952]
	ldr x21, [x5, #2960]
	ldr x22, [x5, #2968]
	ldr x23, [x5, #2976]
	ldr x24, [x5, #2984]
	ldr x25, [x5, #2992]
	ldr x26, [x5, #3000]
	ldr x27, [x5, #3008]
	ldr x28, [x5, #3016]
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
	stp x17, x17, [x16, #432]
	stp x17, x17, [x16, #448]
	stp x17, x17, [x16, #464]
	stp x17, x17, [x16, #480]
	stp x17, x17, [x16, #496]
	add x16, sp, #1536
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
	add x16, sp, #2048
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
	add x16, sp, #2560
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
	add x16, sp, #3072
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
	add sp, sp, #3248
	ret
	.p2align 6
