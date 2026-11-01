// The functions of `src/internal/vg_mldsa_usehint_pack4.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_usehint_pack4:
	add x4, x1, #0
	add x5, x2, #0
	add x1, x0, #0
	add w3, w3, #0
	movz w6, #65280, lsl #0
	movk w6, #3, lsl #16
	sub x6, x3, x6
	cbz x6, 20f
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v16.4s, w9
	movz w9, #127, lsl #0
	movk w9, #0, lsl #16
	dup v17.4s, w9
	movz w9, #11275, lsl #0
	movk w9, #0, lsl #16
	dup v18.4s, w9
	movz w9, #0, lsl #0
	movk w9, #128, lsl #16
	dup v19.4s, w9
	movz w9, #44, lsl #0
	movk w9, #0, lsl #16
	dup v20.4s, w9
	movz w9, #59392, lsl #0
	movk w9, #2, lsl #16
	dup v21.4s, w9
	movz w9, #1, lsl #0
	movk w9, #0, lsl #16
	dup v22.4s, w9
	movi v23.2d, #0
	movi v28.2d, #0
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v29.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v29.d[1], x9
	movz x9, #256, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #1284, lsl #32
	movk x9, #65535, lsl #48
	dup v24.2d, x9
	movz x9, #2312, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #3340, lsl #32
	movk x9, #65535, lsl #48
	mov v24.d[1], x9
	movz x9, #770, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #1798, lsl #32
	movk x9, #65535, lsl #48
	dup v25.2d, x9
	movz x9, #2826, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #3854, lsl #32
	movk x9, #65535, lsl #48
	mov v25.d[1], x9
	movz x11, #16, lsl #0
22:
	ldr q4, [x5, #0]
	ldr q5, [x4, #0]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #24
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v0.16b, v6.16b
	ldr q4, [x5, #16]
	ldr q5, [x4, #16]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #24
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v1.16b, v6.16b
	ldr q4, [x5, #32]
	ldr q5, [x4, #32]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #24
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v2.16b, v6.16b
	ldr q4, [x5, #48]
	ldr q5, [x4, #48]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #24
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v3.16b, v6.16b
	uzp1 v4.16b, v0.16b, v1.16b
	uzp1 v5.16b, v2.16b, v3.16b
	uzp1 v4.16b, v4.16b, v4.16b
	uzp1 v5.16b, v5.16b, v5.16b
	zip1 v6.2d, v4.2d, v5.2d
	uzp1 v4.16b, v6.16b, v6.16b
	uzp2 v5.16b, v6.16b, v6.16b
	zip1 v4.16b, v4.16b, v28.16b
	zip1 v5.16b, v5.16b, v28.16b
	shl v5.4s, v5.4s, #6
	orr v4.16b, v4.16b, v5.16b
	tbl v5.16b, {v4.16b}, v24.16b
	tbl v6.16b, {v4.16b}, v25.16b
	shl v6.4s, v6.4s, #12
	orr v5.16b, v5.16b, v6.16b
	tbl v4.16b, {v5.16b}, v29.16b
	umov x9, v4.d[0]
	str x9, [x1, #0]
	umov w9, v4.s[2]
	str w9, [x1, #8]
	add x4, x4, #64
	add x5, x5, #64
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 22b
	b 21f
20:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v16.4s, w9
	movz w9, #127, lsl #0
	movk w9, #0, lsl #16
	dup v17.4s, w9
	movz w9, #1025, lsl #0
	movk w9, #0, lsl #16
	dup v18.4s, w9
	movz w9, #0, lsl #0
	movk w9, #32, lsl #16
	dup v19.4s, w9
	movz w9, #16, lsl #0
	movk w9, #0, lsl #16
	dup v20.4s, w9
	movz w9, #65024, lsl #0
	movk w9, #7, lsl #16
	dup v21.4s, w9
	movz w9, #1, lsl #0
	movk w9, #0, lsl #16
	dup v22.4s, w9
	movi v23.2d, #0
	movi v28.2d, #0
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v29.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v29.d[1], x9
	movz x9, #256, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #1284, lsl #32
	movk x9, #65535, lsl #48
	dup v24.2d, x9
	movz x9, #2312, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #3340, lsl #32
	movk x9, #65535, lsl #48
	mov v24.d[1], x9
	movz x9, #770, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #1798, lsl #32
	movk x9, #65535, lsl #48
	dup v25.2d, x9
	movz x9, #2826, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #3854, lsl #32
	movk x9, #65535, lsl #48
	mov v25.d[1], x9
	movz x11, #16, lsl #0
23:
	ldr q4, [x5, #0]
	ldr q5, [x4, #0]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #22
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v0.16b, v6.16b
	ldr q4, [x5, #16]
	ldr q5, [x4, #16]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #22
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v1.16b, v6.16b
	ldr q4, [x5, #32]
	ldr q5, [x4, #32]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #22
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v2.16b, v6.16b
	ldr q4, [x5, #48]
	ldr q5, [x4, #48]
	add v6.4s, v4.4s, v17.4s
	ushr v6.4s, v6.4s, #7
	mul v6.4s, v6.4s, v18.4s
	add v6.4s, v6.4s, v19.4s
	ushr v6.4s, v6.4s, #22
	mul v26.4s, v6.4s, v21.4s
	sub v26.4s, v26.4s, v4.4s
	ushr v26.4s, v26.4s, #31
	shl v26.4s, v26.4s, #1
	sub v26.4s, v26.4s, v22.4s
	cmeq v5.4s, v5.4s, v23.4s
	bic v26.16b, v26.16b, v5.16b
	add v6.4s, v6.4s, v26.4s
	add v6.4s, v6.4s, v20.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	sub v7.4s, v6.4s, v20.4s
	umin v6.4s, v6.4s, v7.4s
	mov v3.16b, v6.16b
	uzp1 v4.16b, v0.16b, v1.16b
	uzp1 v5.16b, v2.16b, v3.16b
	uzp1 v4.16b, v4.16b, v4.16b
	uzp1 v5.16b, v5.16b, v5.16b
	zip1 v6.2d, v4.2d, v5.2d
	uzp1 v4.16b, v6.16b, v6.16b
	uzp2 v5.16b, v6.16b, v6.16b
	shl v5.16b, v5.16b, #4
	orr v4.16b, v4.16b, v5.16b
	umov x9, v4.d[0]
	str x9, [x1, #0]
	add x4, x4, #64
	add x5, x5, #64
	add x1, x1, #8
	sub x11, x11, #1
	cbnz x11, 23b
21:
	ret
	.p2align 6
