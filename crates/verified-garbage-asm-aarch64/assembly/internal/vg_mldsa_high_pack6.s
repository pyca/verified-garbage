// The functions of `src/internal/vg_mldsa_high_pack6.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_high_pack6:
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
20:
	ldr q0, [x0, #0]
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #7
	mul v0.4s, v0.4s, v18.4s
	add v0.4s, v0.4s, v19.4s
	ushr v0.4s, v0.4s, #24
	sub v7.4s, v0.4s, v20.4s
	sshr v7.4s, v7.4s, #31
	and v0.16b, v0.16b, v7.16b
	ldr q1, [x0, #16]
	add v1.4s, v1.4s, v17.4s
	ushr v1.4s, v1.4s, #7
	mul v1.4s, v1.4s, v18.4s
	add v1.4s, v1.4s, v19.4s
	ushr v1.4s, v1.4s, #24
	sub v7.4s, v1.4s, v20.4s
	sshr v7.4s, v7.4s, #31
	and v1.16b, v1.16b, v7.16b
	ldr q2, [x0, #32]
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #7
	mul v2.4s, v2.4s, v18.4s
	add v2.4s, v2.4s, v19.4s
	ushr v2.4s, v2.4s, #24
	sub v7.4s, v2.4s, v20.4s
	sshr v7.4s, v7.4s, #31
	and v2.16b, v2.16b, v7.16b
	ldr q3, [x0, #48]
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #7
	mul v3.4s, v3.4s, v18.4s
	add v3.4s, v3.4s, v19.4s
	ushr v3.4s, v3.4s, #24
	sub v7.4s, v3.4s, v20.4s
	sshr v7.4s, v7.4s, #31
	and v3.16b, v3.16b, v7.16b
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
	add x0, x0, #64
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6
