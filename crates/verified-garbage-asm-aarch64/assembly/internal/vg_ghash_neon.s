// The functions of `src/internal/vg_ghash_neon.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_neon:
	cbz x3, 20f
	ldr q1, [x0, #0]
	rev64 v1.16b, v1.16b
	ushr v3.2d, v1.2d, #63
	shl v2.2d, v1.2d, #1
	ext v4.16b, v3.16b, v3.16b, #8
	eor v2.16b, v2.16b, v4.16b
	sshr v5.2d, v1.2d, #63
	movz x5, #49664, lsl #48
	movi v6.2d, #0
	mov v6.d[0], x5
	and v5.16b, v5.16b, v6.16b
	eor v19.16b, v2.16b, v5.16b
	ext v27.16b, v19.16b, v19.16b, #8
	eor v27.16b, v19.16b, v27.16b
	shl v16.2d, v19.2d, #24
	shl v17.2d, v19.2d, #16
	shl v18.2d, v19.2d, #8
	ushr v20.2d, v19.2d, #8
	ushr v21.2d, v19.2d, #16
	ushr v22.2d, v19.2d, #24
	ushr v23.2d, v19.2d, #32
	shl v24.2d, v27.2d, #24
	shl v25.2d, v27.2d, #16
	shl v26.2d, v27.2d, #8
	ushr v28.2d, v27.2d, #8
	ushr v29.2d, v27.2d, #16
	ushr v30.2d, v27.2d, #24
	ushr v31.2d, v27.2d, #32
	ldr q0, [x1, #0]
	rev64 v0.16b, v0.16b
22:
	ldr q1, [x2, #0]
	rev64 v1.16b, v1.16b
	eor v1.16b, v1.16b, v0.16b
	pmull v4.8h, v1.8b, v19.8b
	pmull2 v5.8h, v1.16b, v19.16b
	pmull v6.8h, v1.8b, v20.8b
	pmull2 v7.8h, v1.16b, v20.16b
	ushr v2.2d, v1.2d, #8
	pmull v3.8h, v2.8b, v18.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v19.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v18.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v19.16b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #16
	pmull v3.8h, v2.8b, v17.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v18.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v17.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v18.16b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #24
	pmull v3.8h, v2.8b, v16.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v17.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v16.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v17.16b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #32
	pmull v3.8h, v2.8b, v16.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v16.16b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #8
	pmull v3.8h, v2.8b, v20.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v21.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v20.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v21.16b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #16
	pmull v3.8h, v2.8b, v21.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v22.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v21.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v22.16b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #24
	pmull v3.8h, v2.8b, v22.8b
	eor v4.16b, v4.16b, v3.16b
	pmull v3.8h, v2.8b, v23.8b
	eor v6.16b, v6.16b, v3.16b
	pmull2 v3.8h, v2.16b, v22.16b
	eor v5.16b, v5.16b, v3.16b
	pmull2 v3.8h, v2.16b, v23.16b
	eor v7.16b, v7.16b, v3.16b
	ext v6.16b, v6.16b, v6.16b, #15
	eor v4.16b, v4.16b, v6.16b
	ext v7.16b, v7.16b, v7.16b, #15
	eor v5.16b, v5.16b, v7.16b
	ext v2.16b, v1.16b, v1.16b, #8
	eor v1.16b, v1.16b, v2.16b
	pmull v6.8h, v1.8b, v27.8b
	pmull v7.8h, v1.8b, v28.8b
	ushr v2.2d, v1.2d, #8
	pmull v3.8h, v2.8b, v26.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v27.8b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #16
	pmull v3.8h, v2.8b, v25.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v26.8b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #24
	pmull v3.8h, v2.8b, v24.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v25.8b
	eor v7.16b, v7.16b, v3.16b
	ushr v2.2d, v1.2d, #32
	pmull v3.8h, v2.8b, v24.8b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #8
	pmull v3.8h, v2.8b, v28.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v29.8b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #16
	pmull v3.8h, v2.8b, v29.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v30.8b
	eor v7.16b, v7.16b, v3.16b
	shl v2.2d, v1.2d, #24
	pmull v3.8h, v2.8b, v30.8b
	eor v6.16b, v6.16b, v3.16b
	pmull v3.8h, v2.8b, v31.8b
	eor v7.16b, v7.16b, v3.16b
	ext v7.16b, v7.16b, v7.16b, #15
	eor v6.16b, v6.16b, v7.16b
	eor v6.16b, v6.16b, v4.16b
	eor v6.16b, v6.16b, v5.16b
	movi v2.2d, #0
	ext v3.16b, v2.16b, v6.16b, #8
	eor v5.16b, v5.16b, v3.16b
	ext v3.16b, v6.16b, v2.16b, #8
	eor v4.16b, v4.16b, v3.16b
	shl v1.2d, v5.2d, #63
	shl v3.2d, v5.2d, #62
	eor v1.16b, v1.16b, v3.16b
	shl v3.2d, v5.2d, #57
	eor v1.16b, v1.16b, v3.16b
	ext v3.16b, v2.16b, v1.16b, #8
	eor v5.16b, v5.16b, v3.16b
	ext v3.16b, v1.16b, v2.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v5.16b
	ushr v3.2d, v5.2d, #1
	eor v4.16b, v4.16b, v3.16b
	ushr v3.2d, v5.2d, #2
	eor v4.16b, v4.16b, v3.16b
	ushr v3.2d, v5.2d, #7
	eor v4.16b, v4.16b, v3.16b
	ext v0.16b, v4.16b, v4.16b, #8
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 22b
	rev64 v0.16b, v0.16b
	str q0, [x1, #0]
	b 21f
20:
21:
	ret
	.p2align 6
