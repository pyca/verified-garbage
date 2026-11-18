// The functions of `src/internal/vg_sm4_expand_key_core.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key_core:
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
	ret
	.p2align 6
