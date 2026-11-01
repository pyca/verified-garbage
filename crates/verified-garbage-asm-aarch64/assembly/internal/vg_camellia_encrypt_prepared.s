// The functions of `src/internal/vg_camellia_encrypt_prepared.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_camellia_encrypt_prepared:
	add x5, x1, #0
	add x1, x0, #0
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
	movz x15, #65280, lsl #0
	movk x15, #255, lsl #32
	dup v7.2d, x15
	movz x13, #0, lsl #0
	movk x13, #65280, lsl #16
	movk x13, #255, lsl #48
	movz x14, #0, lsl #0
	movk x14, #255, lsl #16
	movk x14, #65280, lsl #32
	ldr x6, [x5, #768]
	rev x6, x6
	ldr x7, [x5, #776]
	rev x7, x7
	ldr x10, [x5, #256]
	rev x10, x10
	eor x6, x6, x10
	ldr x10, [x5, #264]
	rev x10, x10
	eor x7, x7, x10
	ldr x8, [x5, #272]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #280]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #288]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #296]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #304]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #312]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #320]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #328]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #336]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #344]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #352]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #360]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #368]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #376]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #384]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #392]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #400]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #408]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #416]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #424]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #432]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #440]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	sub x8, x1, #18
	cbz x8, 20f
	ldr x8, [x5, #448]
	rev x8, x8
	lsr x10, x6, #32
	add w12, w6, #0
	lsr x16, x8, #32
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	orr w11, w12, w8
	eor w10, w10, w11
	lsl x6, x10, #32
	orr x6, x6, x12
	ldr x8, [x5, #456]
	rev x8, x8
	lsr x10, x7, #32
	add w12, w7, #0
	lsr x16, x8, #32
	orr w11, w12, w8
	eor w10, w10, w11
	and w11, w10, w16
	extr w11, w11, w11, #31
	eor w12, w12, w11
	lsl x7, x10, #32
	orr x7, x7, x12
	ldr x8, [x5, #464]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #472]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #480]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #488]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #496]
	rev x8, x8
	eor x10, x6, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x8, [x5, #504]
	rev x8, x8
	eor x10, x7, x8
	dup v0.2d, x10
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v7.16b
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
	dup v3.2d, x13
	shl v1.16b, v0.16b, #1
	sri v1.16b, v0.16b, #7
	bit v0.16b, v1.16b, v3.16b
	dup v3.2d, x14
	shl v1.16b, v0.16b, #7
	sri v1.16b, v0.16b, #1
	bit v0.16b, v1.16b, v3.16b
	umov x10, v0.d[0]
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
	ldr x10, [x5, #512]
	rev x10, x10
	eor x7, x7, x10
	ldr x10, [x5, #520]
	rev x10, x10
	eor x6, x6, x10
	rev x7, x7
	rev x6, x6
	str x7, [x5, #768]
	str x6, [x5, #776]
	b 21f
20:
	ldr x10, [x5, #448]
	rev x10, x10
	eor x7, x7, x10
	ldr x10, [x5, #456]
	rev x10, x10
	eor x6, x6, x10
	rev x7, x7
	rev x6, x6
	str x7, [x5, #768]
	str x6, [x5, #776]
21:
	ret
	.p2align 6
