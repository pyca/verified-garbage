// The functions of `src/sm4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key_sm4:
	ldr q0, [x0, #0]
	rev32 v0.16b, v0.16b
	adrp x9, {VG_SM4_FK_CK}
	add x9, x9, {VG_SM4_FK_CK}
	ldr q1, [x9, #0]
	eor v0.16b, v0.16b, v1.16b
	ldr q1, [x9, #16]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #0]
	ldr q1, [x9, #32]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #16]
	ldr q1, [x9, #48]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #32]
	ldr q1, [x9, #64]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #48]
	ldr q1, [x9, #80]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #64]
	ldr q1, [x9, #96]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #80]
	ldr q1, [x9, #112]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #96]
	ldr q1, [x9, #128]
	sm4ekey v0.4s, v0.4s, v1.4s
	str q0, [x1, #112]
	movz x9, #0, lsl #0
	movi v0.2d, #0
	ret
	.p2align 6

vg_sm4_expand_key:
	movz x6, #37078, lsl #0
	movk x6, #65257, lsl #16
	movk x6, #57804, lsl #32
	movk x6, #46909, lsl #48
	movz x7, #46614, lsl #0
	movk x7, #49684, lsl #16
	movk x7, #64296, lsl #32
	movk x7, #1324, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #26411, lsl #0
	movk x6, #30362, lsl #16
	movk x6, #48682, lsl #32
	movk x6, #49924, lsl #48
	movz x7, #17578, lsl #0
	movk x7, #9747, lsl #16
	movk x7, #34377, lsl #32
	movk x7, #39174, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #17052, lsl #0
	movk x6, #62544, lsl #16
	movk x6, #61329, lsl #32
	movk x6, #31384, lsl #48
	movz x7, #21555, lsl #0
	movk x7, #17163, lsl #16
	movk x7, #53229, lsl #32
	movk x7, #25260, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #46052, lsl #0
	movk x6, #43292, lsl #16
	movk x6, #2249, lsl #32
	movk x6, #38376, lsl #48
	movz x7, #57216, lsl #0
	movk x7, #64148, lsl #16
	movk x7, #36725, lsl #32
	movk x7, #42559, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #1863, lsl #0
	movk x6, #64679, lsl #16
	movk x6, #29683, lsl #32
	movk x6, #47639, lsl #48
	movz x7, #22915, lsl #0
	movk x7, #6460, lsl #16
	movk x7, #34278, lsl #32
	movk x7, #43087, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #27496, lsl #0
	movk x6, #45697, lsl #16
	movk x6, #25713, lsl #32
	movk x6, #35802, lsl #48
	movz x7, #60408, lsl #0
	movk x7, #19215, lsl #16
	movk x7, #22128, lsl #32
	movk x7, #13725, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #9246, lsl #0
	movk x6, #24078, lsl #16
	movk x6, #22627, lsl #32
	movk x6, #41681, lsl #48
	movz x7, #8741, lsl #0
	movk x7, #15228, lsl #16
	movk x7, #8449, lsl #32
	movk x7, #34680, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #212, lsl #0
	movk x6, #22342, lsl #16
	movk x6, #54175, lsl #32
	movk x6, #21031, lsl #48
	movz x7, #13900, lsl #0
	movk x7, #59138, lsl #16
	movk x7, #50336, lsl #32
	movk x7, #40648, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #49130, lsl #0
	movk x6, #53898, lsl #16
	movk x6, #51008, lsl #32
	movk x6, #46392, lsl #48
	movz x7, #63395, lsl #0
	movk x7, #52978, lsl #16
	movk x7, #25081, lsl #32
	movk x7, #41237, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #44768, lsl #0
	movk x6, #42077, lsl #16
	movk x6, #13467, lsl #32
	movk x6, #21786, lsl #48
	movz x7, #37805, lsl #0
	movk x7, #12338, lsl #16
	movk x7, #36085, lsl #32
	movk x7, #58289, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #63005, lsl #0
	movk x6, #12002, lsl #16
	movk x6, #26242, lsl #32
	movk x6, #24778, lsl #48
	movz x7, #10688, lsl #0
	movk x7, #43811, lsl #16
	movk x7, #21261, lsl #32
	movk x7, #28494, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #56277, lsl #0
	movk x6, #17719, lsl #16
	movk x6, #64990, lsl #32
	movk x6, #12174, lsl #48
	movz x7, #65283, lsl #0
	movk x7, #29290, lsl #16
	movk x7, #27757, lsl #32
	movk x7, #20827, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #7053, lsl #0
	movk x6, #37551, lsl #16
	movk x6, #56763, lsl #32
	movk x6, #32700, lsl #48
	movz x7, #55569, lsl #0
	movk x7, #16732, lsl #16
	movk x7, #4127, lsl #32
	movk x7, #55386, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #49418, lsl #0
	movk x6, #34865, lsl #16
	movk x6, #52645, lsl #32
	movk x6, #48507, lsl #48
	movz x7, #29741, lsl #0
	movk x7, #4816, lsl #16
	movk x7, #58808, lsl #32
	movk x7, #45236, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #27017, lsl #0
	movk x6, #19095, lsl #16
	movk x6, #38412, lsl #32
	movk x6, #32375, lsl #48
	movz x7, #47461, lsl #0
	movk x7, #2545, lsl #16
	movk x7, #28357, lsl #32
	movk x7, #33990, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #61464, lsl #0
	movk x6, #60541, lsl #16
	movk x6, #56378, lsl #32
	movk x6, #8269, lsl #48
	movz x7, #61049, lsl #0
	movk x7, #15967, lsl #16
	movk x7, #52183, lsl #32
	movk x7, #18489, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	ldr w6, [x0, #0]
	rev w6, w6
	movz w10, #47814, lsl #0
	movk w10, #41905, lsl #16
	eor w6, w6, w10
	ldr w7, [x0, #4]
	rev w7, w7
	movz w10, #13136, lsl #0
	movk w10, #22186, lsl #16
	eor w7, w7, w10
	ldr w8, [x0, #8]
	rev w8, w8
	movz w10, #37271, lsl #0
	movk w10, #26493, lsl #16
	eor w8, w8, w10
	ldr w9, [x0, #12]
	rev w9, w9
	movz w10, #8924, lsl #0
	movk w10, #45680, lsl #16
	eor w9, w9, w10
	movz w10, #3605, lsl #0
	movk w10, #7, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #0]
	movz w10, #10801, lsl #0
	movk w10, #7203, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #4]
	movz w10, #17997, lsl #0
	movk w10, #14399, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #8]
	movz w10, #25193, lsl #0
	movk w10, #21595, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #12]
	movz w10, #32389, lsl #0
	movk w10, #28791, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #16]
	movz w10, #39585, lsl #0
	movk w10, #35987, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #20]
	movz w10, #46781, lsl #0
	movk w10, #43183, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #24]
	movz w10, #53977, lsl #0
	movk w10, #50379, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #28]
	movz w10, #61173, lsl #0
	movk w10, #57575, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #32]
	movz w10, #2577, lsl #0
	movk w10, #64515, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #36]
	movz w10, #9773, lsl #0
	movk w10, #6175, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #40]
	movz w10, #16969, lsl #0
	movk w10, #13371, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #44]
	movz w10, #24165, lsl #0
	movk w10, #20567, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #48]
	movz w10, #31361, lsl #0
	movk w10, #27763, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #52]
	movz w10, #38557, lsl #0
	movk w10, #34959, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #56]
	movz w10, #45753, lsl #0
	movk w10, #42155, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #60]
	movz w10, #52949, lsl #0
	movk w10, #49351, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #64]
	movz w10, #60145, lsl #0
	movk w10, #56547, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #68]
	movz w10, #1549, lsl #0
	movk w10, #63743, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #72]
	movz w10, #8745, lsl #0
	movk w10, #5147, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #76]
	movz w10, #15941, lsl #0
	movk w10, #12343, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #80]
	movz w10, #23137, lsl #0
	movk w10, #19539, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #84]
	movz w10, #30333, lsl #0
	movk w10, #26735, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #88]
	movz w10, #37529, lsl #0
	movk w10, #33931, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #92]
	movz w10, #44725, lsl #0
	movk w10, #41127, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #96]
	movz w10, #51921, lsl #0
	movk w10, #48323, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #100]
	movz w10, #59117, lsl #0
	movk w10, #55519, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #104]
	movz w10, #521, lsl #0
	movk w10, #62715, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #108]
	movz w10, #7717, lsl #0
	movk w10, #4119, lsl #16
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w6, w6, w11
	str w6, [x1, #112]
	movz w10, #14913, lsl #0
	movk w10, #11315, lsl #16
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w7, w7, w11
	str w7, [x1, #116]
	movz w10, #22109, lsl #0
	movk w10, #18511, lsl #16
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w8, w8, w11
	str w8, [x1, #120]
	movz w10, #29305, lsl #0
	movk w10, #25707, lsl #16
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #19
	eor w11, w11, w10, ror #9
	eor w9, w9, w11
	str w9, [x1, #124]
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x15, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	ret
	.p2align 6

vg_sm4_ecb_encrypt_sm4:
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	lsr x13, x2, #3
	cbz x13, 20f
22:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q2, [x1, #32]
	ldr q3, [x1, #48]
	ldr q4, [x1, #64]
	ldr q5, [x1, #80]
	ldr q6, [x1, #96]
	ldr q7, [x1, #112]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	rev32 v2.16b, v2.16b
	rev32 v3.16b, v3.16b
	rev32 v4.16b, v4.16b
	rev32 v5.16b, v5.16b
	rev32 v6.16b, v6.16b
	rev32 v7.16b, v7.16b
	sm4e v0.4s, v16.4s
	sm4e v1.4s, v16.4s
	sm4e v2.4s, v16.4s
	sm4e v3.4s, v16.4s
	sm4e v4.4s, v16.4s
	sm4e v5.4s, v16.4s
	sm4e v6.4s, v16.4s
	sm4e v7.4s, v16.4s
	sm4e v0.4s, v17.4s
	sm4e v1.4s, v17.4s
	sm4e v2.4s, v17.4s
	sm4e v3.4s, v17.4s
	sm4e v4.4s, v17.4s
	sm4e v5.4s, v17.4s
	sm4e v6.4s, v17.4s
	sm4e v7.4s, v17.4s
	sm4e v0.4s, v18.4s
	sm4e v1.4s, v18.4s
	sm4e v2.4s, v18.4s
	sm4e v3.4s, v18.4s
	sm4e v4.4s, v18.4s
	sm4e v5.4s, v18.4s
	sm4e v6.4s, v18.4s
	sm4e v7.4s, v18.4s
	sm4e v0.4s, v19.4s
	sm4e v1.4s, v19.4s
	sm4e v2.4s, v19.4s
	sm4e v3.4s, v19.4s
	sm4e v4.4s, v19.4s
	sm4e v5.4s, v19.4s
	sm4e v6.4s, v19.4s
	sm4e v7.4s, v19.4s
	sm4e v0.4s, v20.4s
	sm4e v1.4s, v20.4s
	sm4e v2.4s, v20.4s
	sm4e v3.4s, v20.4s
	sm4e v4.4s, v20.4s
	sm4e v5.4s, v20.4s
	sm4e v6.4s, v20.4s
	sm4e v7.4s, v20.4s
	sm4e v0.4s, v21.4s
	sm4e v1.4s, v21.4s
	sm4e v2.4s, v21.4s
	sm4e v3.4s, v21.4s
	sm4e v4.4s, v21.4s
	sm4e v5.4s, v21.4s
	sm4e v6.4s, v21.4s
	sm4e v7.4s, v21.4s
	sm4e v0.4s, v22.4s
	sm4e v1.4s, v22.4s
	sm4e v2.4s, v22.4s
	sm4e v3.4s, v22.4s
	sm4e v4.4s, v22.4s
	sm4e v5.4s, v22.4s
	sm4e v6.4s, v22.4s
	sm4e v7.4s, v22.4s
	sm4e v0.4s, v23.4s
	sm4e v1.4s, v23.4s
	sm4e v2.4s, v23.4s
	sm4e v3.4s, v23.4s
	sm4e v4.4s, v23.4s
	sm4e v5.4s, v23.4s
	sm4e v6.4s, v23.4s
	sm4e v7.4s, v23.4s
	rev64 v0.16b, v0.16b
	ext v0.16b, v0.16b, v0.16b, #8
	rev64 v1.16b, v1.16b
	ext v1.16b, v1.16b, v1.16b, #8
	rev64 v2.16b, v2.16b
	ext v2.16b, v2.16b, v2.16b, #8
	rev64 v3.16b, v3.16b
	ext v3.16b, v3.16b, v3.16b, #8
	rev64 v4.16b, v4.16b
	ext v4.16b, v4.16b, v4.16b, #8
	rev64 v5.16b, v5.16b
	ext v5.16b, v5.16b, v5.16b, #8
	rev64 v6.16b, v6.16b
	ext v6.16b, v6.16b, v6.16b, #8
	rev64 v7.16b, v7.16b
	ext v7.16b, v7.16b, v7.16b, #8
	str q0, [x1, #0]
	str q1, [x1, #16]
	str q2, [x1, #32]
	str q3, [x1, #48]
	str q4, [x1, #64]
	str q5, [x1, #80]
	str q6, [x1, #96]
	str q7, [x1, #112]
	add x1, x1, #128
	sub x2, x2, #8
	lsr x13, x2, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x2, 23f
25:
	ldr q0, [x1, #0]
	rev32 v0.16b, v0.16b
	sm4e v0.4s, v16.4s
	sm4e v0.4s, v17.4s
	sm4e v0.4s, v18.4s
	sm4e v0.4s, v19.4s
	sm4e v0.4s, v20.4s
	sm4e v0.4s, v21.4s
	sm4e v0.4s, v22.4s
	sm4e v0.4s, v23.4s
	rev64 v0.16b, v0.16b
	ext v0.16b, v0.16b, v0.16b, #8
	str q0, [x1, #0]
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 25b
	b 24f
23:
24:
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	ret
	.p2align 6

vg_sm4_ecb_decrypt_sm4:
	ldr q16, [x0, #112]
	rev64 v16.4s, v16.4s
	ext v16.16b, v16.16b, v16.16b, #8
	ldr q17, [x0, #96]
	rev64 v17.4s, v17.4s
	ext v17.16b, v17.16b, v17.16b, #8
	ldr q18, [x0, #80]
	rev64 v18.4s, v18.4s
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q19, [x0, #64]
	rev64 v19.4s, v19.4s
	ext v19.16b, v19.16b, v19.16b, #8
	ldr q20, [x0, #48]
	rev64 v20.4s, v20.4s
	ext v20.16b, v20.16b, v20.16b, #8
	ldr q21, [x0, #32]
	rev64 v21.4s, v21.4s
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x0, #16]
	rev64 v22.4s, v22.4s
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x0, #0]
	rev64 v23.4s, v23.4s
	ext v23.16b, v23.16b, v23.16b, #8
	lsr x13, x2, #3
	cbz x13, 20f
22:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q2, [x1, #32]
	ldr q3, [x1, #48]
	ldr q4, [x1, #64]
	ldr q5, [x1, #80]
	ldr q6, [x1, #96]
	ldr q7, [x1, #112]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	rev32 v2.16b, v2.16b
	rev32 v3.16b, v3.16b
	rev32 v4.16b, v4.16b
	rev32 v5.16b, v5.16b
	rev32 v6.16b, v6.16b
	rev32 v7.16b, v7.16b
	sm4e v0.4s, v16.4s
	sm4e v1.4s, v16.4s
	sm4e v2.4s, v16.4s
	sm4e v3.4s, v16.4s
	sm4e v4.4s, v16.4s
	sm4e v5.4s, v16.4s
	sm4e v6.4s, v16.4s
	sm4e v7.4s, v16.4s
	sm4e v0.4s, v17.4s
	sm4e v1.4s, v17.4s
	sm4e v2.4s, v17.4s
	sm4e v3.4s, v17.4s
	sm4e v4.4s, v17.4s
	sm4e v5.4s, v17.4s
	sm4e v6.4s, v17.4s
	sm4e v7.4s, v17.4s
	sm4e v0.4s, v18.4s
	sm4e v1.4s, v18.4s
	sm4e v2.4s, v18.4s
	sm4e v3.4s, v18.4s
	sm4e v4.4s, v18.4s
	sm4e v5.4s, v18.4s
	sm4e v6.4s, v18.4s
	sm4e v7.4s, v18.4s
	sm4e v0.4s, v19.4s
	sm4e v1.4s, v19.4s
	sm4e v2.4s, v19.4s
	sm4e v3.4s, v19.4s
	sm4e v4.4s, v19.4s
	sm4e v5.4s, v19.4s
	sm4e v6.4s, v19.4s
	sm4e v7.4s, v19.4s
	sm4e v0.4s, v20.4s
	sm4e v1.4s, v20.4s
	sm4e v2.4s, v20.4s
	sm4e v3.4s, v20.4s
	sm4e v4.4s, v20.4s
	sm4e v5.4s, v20.4s
	sm4e v6.4s, v20.4s
	sm4e v7.4s, v20.4s
	sm4e v0.4s, v21.4s
	sm4e v1.4s, v21.4s
	sm4e v2.4s, v21.4s
	sm4e v3.4s, v21.4s
	sm4e v4.4s, v21.4s
	sm4e v5.4s, v21.4s
	sm4e v6.4s, v21.4s
	sm4e v7.4s, v21.4s
	sm4e v0.4s, v22.4s
	sm4e v1.4s, v22.4s
	sm4e v2.4s, v22.4s
	sm4e v3.4s, v22.4s
	sm4e v4.4s, v22.4s
	sm4e v5.4s, v22.4s
	sm4e v6.4s, v22.4s
	sm4e v7.4s, v22.4s
	sm4e v0.4s, v23.4s
	sm4e v1.4s, v23.4s
	sm4e v2.4s, v23.4s
	sm4e v3.4s, v23.4s
	sm4e v4.4s, v23.4s
	sm4e v5.4s, v23.4s
	sm4e v6.4s, v23.4s
	sm4e v7.4s, v23.4s
	rev64 v0.16b, v0.16b
	ext v0.16b, v0.16b, v0.16b, #8
	rev64 v1.16b, v1.16b
	ext v1.16b, v1.16b, v1.16b, #8
	rev64 v2.16b, v2.16b
	ext v2.16b, v2.16b, v2.16b, #8
	rev64 v3.16b, v3.16b
	ext v3.16b, v3.16b, v3.16b, #8
	rev64 v4.16b, v4.16b
	ext v4.16b, v4.16b, v4.16b, #8
	rev64 v5.16b, v5.16b
	ext v5.16b, v5.16b, v5.16b, #8
	rev64 v6.16b, v6.16b
	ext v6.16b, v6.16b, v6.16b, #8
	rev64 v7.16b, v7.16b
	ext v7.16b, v7.16b, v7.16b, #8
	str q0, [x1, #0]
	str q1, [x1, #16]
	str q2, [x1, #32]
	str q3, [x1, #48]
	str q4, [x1, #64]
	str q5, [x1, #80]
	str q6, [x1, #96]
	str q7, [x1, #112]
	add x1, x1, #128
	sub x2, x2, #8
	lsr x13, x2, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x2, 23f
25:
	ldr q0, [x1, #0]
	rev32 v0.16b, v0.16b
	sm4e v0.4s, v16.4s
	sm4e v0.4s, v17.4s
	sm4e v0.4s, v18.4s
	sm4e v0.4s, v19.4s
	sm4e v0.4s, v20.4s
	sm4e v0.4s, v21.4s
	sm4e v0.4s, v22.4s
	sm4e v0.4s, v23.4s
	rev64 v0.16b, v0.16b
	ext v0.16b, v0.16b, v0.16b, #8
	str q0, [x1, #0]
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 25b
	b 24f
23:
24:
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	ret
	.p2align 6

vg_sm4_ecb_encrypt:
	add x13, x2, #1
	lsr x13, x13, #3
	cbz x13, 20f
	str x30, [sp, #-16]!
	movz x3, #0, lsl #0
	bl {vg_sm4_ecb}
	ldr x30, [sp], #16
	b 21f
20:
	sub sp, sp, #3264
	add x3, sp, #0
	add x5, x3, #0
	str x19, [x5, #3168]
	str x20, [x5, #3176]
	str x21, [x5, #3184]
	str x22, [x5, #3192]
	str x23, [x5, #3200]
	str x24, [x5, #3208]
	str x25, [x5, #3216]
	str x26, [x5, #3224]
	str x27, [x5, #3232]
	str x28, [x5, #3240]
	add x23, x1, #0
	add x24, x2, #0
	movz x21, #37078, lsl #0
	movk x21, #65257, lsl #16
	movk x21, #57804, lsl #32
	movk x21, #46909, lsl #48
	str x21, [x5, #0]
	movz x21, #46614, lsl #0
	movk x21, #49684, lsl #16
	movk x21, #64296, lsl #32
	movk x21, #1324, lsl #48
	str x21, [x5, #8]
	movz x21, #26411, lsl #0
	movk x21, #30362, lsl #16
	movk x21, #48682, lsl #32
	movk x21, #49924, lsl #48
	str x21, [x5, #16]
	movz x21, #17578, lsl #0
	movk x21, #9747, lsl #16
	movk x21, #34377, lsl #32
	movk x21, #39174, lsl #48
	str x21, [x5, #24]
	movz x21, #17052, lsl #0
	movk x21, #62544, lsl #16
	movk x21, #61329, lsl #32
	movk x21, #31384, lsl #48
	str x21, [x5, #32]
	movz x21, #21555, lsl #0
	movk x21, #17163, lsl #16
	movk x21, #53229, lsl #32
	movk x21, #25260, lsl #48
	str x21, [x5, #40]
	movz x21, #46052, lsl #0
	movk x21, #43292, lsl #16
	movk x21, #2249, lsl #32
	movk x21, #38376, lsl #48
	str x21, [x5, #48]
	movz x21, #57216, lsl #0
	movk x21, #64148, lsl #16
	movk x21, #36725, lsl #32
	movk x21, #42559, lsl #48
	str x21, [x5, #56]
	movz x21, #1863, lsl #0
	movk x21, #64679, lsl #16
	movk x21, #29683, lsl #32
	movk x21, #47639, lsl #48
	str x21, [x5, #64]
	movz x21, #22915, lsl #0
	movk x21, #6460, lsl #16
	movk x21, #34278, lsl #32
	movk x21, #43087, lsl #48
	str x21, [x5, #72]
	movz x21, #27496, lsl #0
	movk x21, #45697, lsl #16
	movk x21, #25713, lsl #32
	movk x21, #35802, lsl #48
	str x21, [x5, #80]
	movz x21, #60408, lsl #0
	movk x21, #19215, lsl #16
	movk x21, #22128, lsl #32
	movk x21, #13725, lsl #48
	str x21, [x5, #88]
	movz x21, #9246, lsl #0
	movk x21, #24078, lsl #16
	movk x21, #22627, lsl #32
	movk x21, #41681, lsl #48
	str x21, [x5, #96]
	movz x21, #8741, lsl #0
	movk x21, #15228, lsl #16
	movk x21, #8449, lsl #32
	movk x21, #34680, lsl #48
	str x21, [x5, #104]
	movz x21, #212, lsl #0
	movk x21, #22342, lsl #16
	movk x21, #54175, lsl #32
	movk x21, #21031, lsl #48
	str x21, [x5, #112]
	movz x21, #13900, lsl #0
	movk x21, #59138, lsl #16
	movk x21, #50336, lsl #32
	movk x21, #40648, lsl #48
	str x21, [x5, #120]
	movz x21, #49130, lsl #0
	movk x21, #53898, lsl #16
	movk x21, #51008, lsl #32
	movk x21, #46392, lsl #48
	str x21, [x5, #128]
	movz x21, #63395, lsl #0
	movk x21, #52978, lsl #16
	movk x21, #25081, lsl #32
	movk x21, #41237, lsl #48
	str x21, [x5, #136]
	movz x21, #44768, lsl #0
	movk x21, #42077, lsl #16
	movk x21, #13467, lsl #32
	movk x21, #21786, lsl #48
	str x21, [x5, #144]
	movz x21, #37805, lsl #0
	movk x21, #12338, lsl #16
	movk x21, #36085, lsl #32
	movk x21, #58289, lsl #48
	str x21, [x5, #152]
	movz x21, #63005, lsl #0
	movk x21, #12002, lsl #16
	movk x21, #26242, lsl #32
	movk x21, #24778, lsl #48
	str x21, [x5, #160]
	movz x21, #10688, lsl #0
	movk x21, #43811, lsl #16
	movk x21, #21261, lsl #32
	movk x21, #28494, lsl #48
	str x21, [x5, #168]
	movz x21, #56277, lsl #0
	movk x21, #17719, lsl #16
	movk x21, #64990, lsl #32
	movk x21, #12174, lsl #48
	str x21, [x5, #176]
	movz x21, #65283, lsl #0
	movk x21, #29290, lsl #16
	movk x21, #27757, lsl #32
	movk x21, #20827, lsl #48
	str x21, [x5, #184]
	movz x21, #7053, lsl #0
	movk x21, #37551, lsl #16
	movk x21, #56763, lsl #32
	movk x21, #32700, lsl #48
	str x21, [x5, #192]
	movz x21, #55569, lsl #0
	movk x21, #16732, lsl #16
	movk x21, #4127, lsl #32
	movk x21, #55386, lsl #48
	str x21, [x5, #200]
	movz x21, #49418, lsl #0
	movk x21, #34865, lsl #16
	movk x21, #52645, lsl #32
	movk x21, #48507, lsl #48
	str x21, [x5, #208]
	movz x21, #29741, lsl #0
	movk x21, #4816, lsl #16
	movk x21, #58808, lsl #32
	movk x21, #45236, lsl #48
	str x21, [x5, #216]
	movz x21, #27017, lsl #0
	movk x21, #19095, lsl #16
	movk x21, #38412, lsl #32
	movk x21, #32375, lsl #48
	str x21, [x5, #224]
	movz x21, #47461, lsl #0
	movk x21, #2545, lsl #16
	movk x21, #28357, lsl #32
	movk x21, #33990, lsl #48
	str x21, [x5, #232]
	movz x21, #61464, lsl #0
	movk x21, #60541, lsl #16
	movk x21, #56378, lsl #32
	movk x21, #8269, lsl #48
	str x21, [x5, #240]
	movz x21, #61049, lsl #0
	movk x21, #15967, lsl #16
	movk x21, #52183, lsl #32
	movk x21, #18489, lsl #48
	str x21, [x5, #248]
	add x14, x0, #0
	add x15, x5, #256
	movz x17, #8, lsl #0
22:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 22b
	cbz x24, 23f
25:
	lsr x13, x24, #0
	cbnz x13, 26f
	add x16, x24, #0
	b 27f
26:
	movz x16, #1, lsl #0
27:
	add x14, x5, #0
	add x14, x14, #768
	add x15, x23, #0
	add x17, x16, #0
28:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	ldr q16, [x5, #0]
	ldr q17, [x5, #16]
	ldr q18, [x5, #32]
	ldr q19, [x5, #48]
	ldr q20, [x5, #64]
	ldr q21, [x5, #80]
	ldr q22, [x5, #96]
	ldr q23, [x5, #112]
	ldr q24, [x5, #128]
	ldr q25, [x5, #144]
	ldr q26, [x5, #160]
	ldr q27, [x5, #176]
	ldr q28, [x5, #192]
	ldr q29, [x5, #208]
	ldr q30, [x5, #224]
	ldr q31, [x5, #240]
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	ldr w6, [x5, #768]
	rev w6, w6
	ldr w7, [x5, #772]
	rev w7, w7
	ldr w8, [x5, #776]
	rev w8, w8
	ldr w9, [x5, #780]
	rev w9, w9
	ldr w10, [x5, #256]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #260]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #264]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #268]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #272]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #276]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #280]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #284]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #288]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #292]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #296]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #300]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #304]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #308]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #312]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #316]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #320]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #324]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #328]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #332]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #336]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #340]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #344]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #348]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #352]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #356]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #360]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #364]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #368]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #372]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #376]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #380]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	rev w9, w9
	str w9, [x5, #768]
	rev w8, w8
	str w8, [x5, #772]
	rev w7, w7
	str w7, [x5, #776]
	rev w6, w6
	str w6, [x5, #780]
	lsr x13, x24, #0
	cbnz x13, 29f
	add x16, x24, #0
	b 210f
29:
	movz x16, #1, lsl #0
210:
	add x15, x5, #0
	add x15, x15, #768
	add x14, x23, #0
	add x17, x16, #0
211:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 211b
	add x23, x14, #0
	sub x24, x24, x16
	cbnz x24, 25b
	b 24f
23:
24:
	ldr x19, [x5, #3168]
	ldr x20, [x5, #3176]
	ldr x21, [x5, #3184]
	ldr x22, [x5, #3192]
	ldr x23, [x5, #3200]
	ldr x24, [x5, #3208]
	ldr x25, [x5, #3216]
	ldr x26, [x5, #3224]
	ldr x27, [x5, #3232]
	ldr x28, [x5, #3240]
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
	stp x17, x17, [x16, #176]
	add sp, sp, #3264
21:
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	sub sp, sp, #3264
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #3248]
	add sp, sp, #3264
	ret
	.p2align 6

vg_sm4_ecb_decrypt:
	add x13, x2, #1
	lsr x13, x13, #3
	cbz x13, 20f
	str x30, [sp, #-16]!
	movz x3, #1, lsl #0
	bl {vg_sm4_ecb}
	ldr x30, [sp], #16
	b 21f
20:
	sub sp, sp, #3264
	add x3, sp, #0
	add x5, x3, #0
	str x19, [x5, #3168]
	str x20, [x5, #3176]
	str x21, [x5, #3184]
	str x22, [x5, #3192]
	str x23, [x5, #3200]
	str x24, [x5, #3208]
	str x25, [x5, #3216]
	str x26, [x5, #3224]
	str x27, [x5, #3232]
	str x28, [x5, #3240]
	add x23, x1, #0
	add x24, x2, #0
	movz x21, #37078, lsl #0
	movk x21, #65257, lsl #16
	movk x21, #57804, lsl #32
	movk x21, #46909, lsl #48
	str x21, [x5, #0]
	movz x21, #46614, lsl #0
	movk x21, #49684, lsl #16
	movk x21, #64296, lsl #32
	movk x21, #1324, lsl #48
	str x21, [x5, #8]
	movz x21, #26411, lsl #0
	movk x21, #30362, lsl #16
	movk x21, #48682, lsl #32
	movk x21, #49924, lsl #48
	str x21, [x5, #16]
	movz x21, #17578, lsl #0
	movk x21, #9747, lsl #16
	movk x21, #34377, lsl #32
	movk x21, #39174, lsl #48
	str x21, [x5, #24]
	movz x21, #17052, lsl #0
	movk x21, #62544, lsl #16
	movk x21, #61329, lsl #32
	movk x21, #31384, lsl #48
	str x21, [x5, #32]
	movz x21, #21555, lsl #0
	movk x21, #17163, lsl #16
	movk x21, #53229, lsl #32
	movk x21, #25260, lsl #48
	str x21, [x5, #40]
	movz x21, #46052, lsl #0
	movk x21, #43292, lsl #16
	movk x21, #2249, lsl #32
	movk x21, #38376, lsl #48
	str x21, [x5, #48]
	movz x21, #57216, lsl #0
	movk x21, #64148, lsl #16
	movk x21, #36725, lsl #32
	movk x21, #42559, lsl #48
	str x21, [x5, #56]
	movz x21, #1863, lsl #0
	movk x21, #64679, lsl #16
	movk x21, #29683, lsl #32
	movk x21, #47639, lsl #48
	str x21, [x5, #64]
	movz x21, #22915, lsl #0
	movk x21, #6460, lsl #16
	movk x21, #34278, lsl #32
	movk x21, #43087, lsl #48
	str x21, [x5, #72]
	movz x21, #27496, lsl #0
	movk x21, #45697, lsl #16
	movk x21, #25713, lsl #32
	movk x21, #35802, lsl #48
	str x21, [x5, #80]
	movz x21, #60408, lsl #0
	movk x21, #19215, lsl #16
	movk x21, #22128, lsl #32
	movk x21, #13725, lsl #48
	str x21, [x5, #88]
	movz x21, #9246, lsl #0
	movk x21, #24078, lsl #16
	movk x21, #22627, lsl #32
	movk x21, #41681, lsl #48
	str x21, [x5, #96]
	movz x21, #8741, lsl #0
	movk x21, #15228, lsl #16
	movk x21, #8449, lsl #32
	movk x21, #34680, lsl #48
	str x21, [x5, #104]
	movz x21, #212, lsl #0
	movk x21, #22342, lsl #16
	movk x21, #54175, lsl #32
	movk x21, #21031, lsl #48
	str x21, [x5, #112]
	movz x21, #13900, lsl #0
	movk x21, #59138, lsl #16
	movk x21, #50336, lsl #32
	movk x21, #40648, lsl #48
	str x21, [x5, #120]
	movz x21, #49130, lsl #0
	movk x21, #53898, lsl #16
	movk x21, #51008, lsl #32
	movk x21, #46392, lsl #48
	str x21, [x5, #128]
	movz x21, #63395, lsl #0
	movk x21, #52978, lsl #16
	movk x21, #25081, lsl #32
	movk x21, #41237, lsl #48
	str x21, [x5, #136]
	movz x21, #44768, lsl #0
	movk x21, #42077, lsl #16
	movk x21, #13467, lsl #32
	movk x21, #21786, lsl #48
	str x21, [x5, #144]
	movz x21, #37805, lsl #0
	movk x21, #12338, lsl #16
	movk x21, #36085, lsl #32
	movk x21, #58289, lsl #48
	str x21, [x5, #152]
	movz x21, #63005, lsl #0
	movk x21, #12002, lsl #16
	movk x21, #26242, lsl #32
	movk x21, #24778, lsl #48
	str x21, [x5, #160]
	movz x21, #10688, lsl #0
	movk x21, #43811, lsl #16
	movk x21, #21261, lsl #32
	movk x21, #28494, lsl #48
	str x21, [x5, #168]
	movz x21, #56277, lsl #0
	movk x21, #17719, lsl #16
	movk x21, #64990, lsl #32
	movk x21, #12174, lsl #48
	str x21, [x5, #176]
	movz x21, #65283, lsl #0
	movk x21, #29290, lsl #16
	movk x21, #27757, lsl #32
	movk x21, #20827, lsl #48
	str x21, [x5, #184]
	movz x21, #7053, lsl #0
	movk x21, #37551, lsl #16
	movk x21, #56763, lsl #32
	movk x21, #32700, lsl #48
	str x21, [x5, #192]
	movz x21, #55569, lsl #0
	movk x21, #16732, lsl #16
	movk x21, #4127, lsl #32
	movk x21, #55386, lsl #48
	str x21, [x5, #200]
	movz x21, #49418, lsl #0
	movk x21, #34865, lsl #16
	movk x21, #52645, lsl #32
	movk x21, #48507, lsl #48
	str x21, [x5, #208]
	movz x21, #29741, lsl #0
	movk x21, #4816, lsl #16
	movk x21, #58808, lsl #32
	movk x21, #45236, lsl #48
	str x21, [x5, #216]
	movz x21, #27017, lsl #0
	movk x21, #19095, lsl #16
	movk x21, #38412, lsl #32
	movk x21, #32375, lsl #48
	str x21, [x5, #224]
	movz x21, #47461, lsl #0
	movk x21, #2545, lsl #16
	movk x21, #28357, lsl #32
	movk x21, #33990, lsl #48
	str x21, [x5, #232]
	movz x21, #61464, lsl #0
	movk x21, #60541, lsl #16
	movk x21, #56378, lsl #32
	movk x21, #8269, lsl #48
	str x21, [x5, #240]
	movz x21, #61049, lsl #0
	movk x21, #15967, lsl #16
	movk x21, #52183, lsl #32
	movk x21, #18489, lsl #48
	str x21, [x5, #248]
	add x14, x0, #0
	add x15, x5, #256
	movz x17, #8, lsl #0
22:
	ldr x21, [x14, #0]
	str x21, [x15, #0]
	ldr x21, [x14, #8]
	str x21, [x15, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 22b
	cbz x24, 23f
25:
	lsr x13, x24, #0
	cbnz x13, 26f
	add x16, x24, #0
	b 27f
26:
	movz x16, #1, lsl #0
27:
	add x14, x5, #0
	add x14, x14, #768
	add x15, x23, #0
	add x17, x16, #0
28:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 28b
	ldr q16, [x5, #0]
	ldr q17, [x5, #16]
	ldr q18, [x5, #32]
	ldr q19, [x5, #48]
	ldr q20, [x5, #64]
	ldr q21, [x5, #80]
	ldr q22, [x5, #96]
	ldr q23, [x5, #112]
	ldr q24, [x5, #128]
	ldr q25, [x5, #144]
	ldr q26, [x5, #160]
	ldr q27, [x5, #176]
	ldr q28, [x5, #192]
	ldr q29, [x5, #208]
	ldr q30, [x5, #224]
	ldr q31, [x5, #240]
	movz w15, #64, lsl #0
	dup v4.16b, w15
	movz w15, #128, lsl #0
	dup v5.16b, w15
	movz w15, #192, lsl #0
	dup v6.16b, w15
	ldr w6, [x5, #768]
	rev w6, w6
	ldr w7, [x5, #772]
	rev w7, w7
	ldr w8, [x5, #776]
	rev w8, w8
	ldr w9, [x5, #780]
	rev w9, w9
	ldr w10, [x5, #380]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #376]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #372]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #368]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #364]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #360]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #356]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #352]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #348]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #344]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #340]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #336]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #332]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #328]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #324]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #320]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #316]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #312]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #308]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #304]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #300]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #296]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #292]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #288]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #284]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #280]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #276]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #272]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	ldr w10, [x5, #268]
	eor w10, w10, w7
	eor w10, w10, w8
	eor w10, w10, w9
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w6, w6, w11
	ldr w10, [x5, #264]
	eor w10, w10, w8
	eor w10, w10, w9
	eor w10, w10, w6
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w7, w7, w11
	ldr w10, [x5, #260]
	eor w10, w10, w9
	eor w10, w10, w6
	eor w10, w10, w7
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w8, w8, w11
	ldr w10, [x5, #256]
	eor w10, w10, w6
	eor w10, w10, w7
	eor w10, w10, w8
	dup v0.4s, w10
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
	umov w10, v0.s[0]
	eor w11, w10, w10, ror #30
	eor w12, w10, w10, ror #8
	ror w13, w10, #8
	eor w12, w13, w12, ror #14
	eor w11, w11, w12
	eor w9, w9, w11
	rev w9, w9
	str w9, [x5, #768]
	rev w8, w8
	str w8, [x5, #772]
	rev w7, w7
	str w7, [x5, #776]
	rev w6, w6
	str w6, [x5, #780]
	lsr x13, x24, #0
	cbnz x13, 29f
	add x16, x24, #0
	b 210f
29:
	movz x16, #1, lsl #0
210:
	add x15, x5, #0
	add x15, x15, #768
	add x14, x23, #0
	add x17, x16, #0
211:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	ldr x8, [x15, #8]
	str x8, [x14, #8]
	add x14, x14, #16
	add x15, x15, #16
	sub x17, x17, #1
	cbnz x17, 211b
	add x23, x14, #0
	sub x24, x24, x16
	cbnz x24, 25b
	b 24f
23:
24:
	ldr x19, [x5, #3168]
	ldr x20, [x5, #3176]
	ldr x21, [x5, #3184]
	ldr x22, [x5, #3192]
	ldr x23, [x5, #3200]
	ldr x24, [x5, #3208]
	ldr x25, [x5, #3216]
	ldr x26, [x5, #3224]
	ldr x27, [x5, #3232]
	ldr x28, [x5, #3240]
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
	stp x17, x17, [x16, #176]
	add sp, sp, #3264
21:
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	sub sp, sp, #3264
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	str q31, [x9, #64]
	str q31, [x9, #3248]
	add sp, sp, #3264
	ret
	.p2align 6
