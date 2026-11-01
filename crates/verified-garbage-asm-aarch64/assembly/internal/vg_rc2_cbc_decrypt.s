// The functions of `src/internal/vg_rc2_cbc_decrypt.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_decrypt:
	str x23, [x4, #264]
	str x24, [x4, #272]
	str x30, [x4, #280]
	add x23, x1, #0
	add x24, x3, #0
	add x1, x2, #0
	add x2, x4, #0
	lsr x10, x24, #3
	cbz x10, 20f
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	movz x9, #65535, lsl #0
	dup v6.4s, w9
	ldr x11, [x23, #0]
22:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q2, [x1, #32]
	ldr q3, [x1, #48]
	movz x6, #256, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #2312, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #4368, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #6424, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v24.16b, {v0.16b, v1.16b}, v4.16b
	tbl v28.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #770, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #2826, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #4882, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #6938, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v25.16b, {v0.16b, v1.16b}, v4.16b
	tbl v29.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #1284, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #3340, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #5396, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #7452, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v26.16b, {v0.16b, v1.16b}, v4.16b
	tbl v30.16b, {v2.16b, v3.16b}, v4.16b
	movz x6, #1798, lsl #0
	movk x6, #65535, lsl #16
	movk x6, #3854, lsl #32
	movk x6, #65535, lsl #48
	movz x7, #5910, lsl #0
	movk x7, #65535, lsl #16
	movk x7, #7966, lsl #32
	movk x7, #65535, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v27.16b, {v0.16b, v1.16b}, v4.16b
	tbl v31.16b, {v2.16b, v3.16b}, v4.16b
	dup v7.4s, v23.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v23.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v22.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v26.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v27.4s, v27.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v30.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v31.4s, v31.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v25.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v26.4s, v26.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v29.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v30.4s, v30.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v24.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v25.4s, v25.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v28.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v29.4s, v29.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v27.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v24.4s, v24.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v31.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v28.4s, v28.4s, v0.4s
	dup v7.4s, v21.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v21.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v20.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v19.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v26.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v27.4s, v27.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v30.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v31.4s, v31.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v25.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v26.4s, v26.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v29.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v30.4s, v30.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v24.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v25.4s, v25.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v28.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v29.4s, v29.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v27.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v24.4s, v24.4s, v0.4s
	movz x9, #63, lsl #0
	dup v1.4s, w9
	and v0.16b, v31.16b, v1.16b
	movz x9, #514, lsl #0
	dup v4.4s, w9
	mul v0.4s, v0.4s, v4.4s
	movz x9, #256, lsl #0
	dup v1.4s, w9
	add v0.4s, v0.4s, v1.4s
	movz x6, #64, lsl #0
	dup v4.16b, w6
	eor v1.16b, v0.16b, v4.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	orr v0.16b, v0.16b, v1.16b
	sub v28.4s, v28.4s, v0.4s
	dup v7.4s, v18.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v18.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v17.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[3]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[3]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[2]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[2]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[1]
	rev32 v7.8h, v7.8h
	and v27.16b, v27.16b, v6.16b
	ushr v0.4s, v27.4s, #5
	sli v0.4s, v27.4s, #11
	and v1.16b, v26.16b, v25.16b
	bic v2.16b, v24.16b, v26.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v27.4s, v0.4s, v2.4s
	and v31.16b, v31.16b, v6.16b
	ushr v3.4s, v31.4s, #5
	sli v3.4s, v31.4s, #11
	and v4.16b, v30.16b, v29.16b
	bic v5.16b, v28.16b, v30.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v31.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[1]
	and v26.16b, v26.16b, v6.16b
	ushr v0.4s, v26.4s, #3
	sli v0.4s, v26.4s, #13
	and v1.16b, v25.16b, v24.16b
	bic v2.16b, v27.16b, v25.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v26.4s, v0.4s, v2.4s
	and v30.16b, v30.16b, v6.16b
	ushr v3.4s, v30.4s, #3
	sli v3.4s, v30.4s, #13
	and v4.16b, v29.16b, v28.16b
	bic v5.16b, v31.16b, v29.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v30.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[0]
	rev32 v7.8h, v7.8h
	and v25.16b, v25.16b, v6.16b
	ushr v0.4s, v25.4s, #2
	sli v0.4s, v25.4s, #14
	and v1.16b, v24.16b, v27.16b
	bic v2.16b, v26.16b, v24.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v25.4s, v0.4s, v2.4s
	and v29.16b, v29.16b, v6.16b
	ushr v3.4s, v29.4s, #2
	sli v3.4s, v29.4s, #14
	and v4.16b, v28.16b, v31.16b
	bic v5.16b, v30.16b, v28.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v29.4s, v3.4s, v5.4s
	dup v7.4s, v16.s[0]
	and v24.16b, v24.16b, v6.16b
	ushr v0.4s, v24.4s, #1
	sli v0.4s, v24.4s, #15
	and v1.16b, v27.16b, v26.16b
	bic v2.16b, v25.16b, v27.16b
	sub v0.4s, v0.4s, v7.4s
	sub v0.4s, v0.4s, v1.4s
	sub v24.4s, v0.4s, v2.4s
	and v28.16b, v28.16b, v6.16b
	ushr v3.4s, v28.4s, #1
	sli v3.4s, v28.4s, #15
	and v4.16b, v31.16b, v30.16b
	bic v5.16b, v29.16b, v31.16b
	sub v3.4s, v3.4s, v7.4s
	sub v3.4s, v3.4s, v4.4s
	sub v28.4s, v3.4s, v5.4s
	movz x6, #256, lsl #0
	movk x6, #4368, lsl #16
	movk x6, #8480, lsl #32
	movk x6, #12592, lsl #48
	movz x7, #1284, lsl #0
	movk x7, #5396, lsl #16
	movk x7, #9508, lsl #32
	movk x7, #13620, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v0.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v4.16b
	tbl v2.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v4.16b
	movz x6, #2312, lsl #0
	movk x6, #6424, lsl #16
	movk x6, #10536, lsl #32
	movk x6, #14648, lsl #48
	movz x7, #3340, lsl #0
	movk x7, #7452, lsl #16
	movk x7, #11564, lsl #32
	movk x7, #15676, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	tbl v1.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v4.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v4.16b
	ldr x9, [x1, #0]
	mov v4.d[0], x11
	mov v4.d[1], x9
	add x12, x1, #8
	ldr q5, [x12, #0]
	eor v0.16b, v0.16b, v4.16b
	eor v1.16b, v1.16b, v5.16b
	ldr q4, [x12, #16]
	ldr q5, [x12, #32]
	eor v2.16b, v2.16b, v4.16b
	eor v3.16b, v3.16b, v5.16b
	ldr x11, [x1, #56]
	str q0, [x1, #0]
	str q1, [x1, #16]
	str q2, [x1, #32]
	str q3, [x1, #48]
	add x1, x1, #64
	sub x10, x10, #1
	cbnz x10, 22b
	str x11, [x23, #0]
	b 21f
20:
21:
	lsl x24, x24, #61
	lsr x24, x24, #61
	cbz x24, 23f
25:
	ldr x8, [x1, #0]
	str x8, [x2, #256]
	bl {vg_rc2_decrypt_block}
	ldr x8, [x1, #0]
	ldr x9, [x23, #0]
	eor x8, x8, x9
	str x8, [x1, #0]
	ldr x8, [x2, #256]
	str x8, [x23, #0]
	add x1, x1, #8
	sub x24, x24, #1
	cbnz x24, 25b
	b 24f
23:
24:
	ldr x23, [x2, #264]
	ldr x24, [x2, #272]
	ldr x30, [x2, #280]
	ret
	.p2align 6
