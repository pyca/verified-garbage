// The functions of `src/internal/vg_ghash_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_aes:
	.arch_extension aes
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ushr v7.2d, v6.2d, #63
	shl v3.2d, v6.2d, #1
	ext v4.16b, v7.16b, v7.16b, #8
	eor v3.16b, v3.16b, v4.16b
	pmull v5.1q, v7.1d, v1.1d
	eor v24.16b, v3.16b, v5.16b
	ext v16.16b, v24.16b, v24.16b, #8
	ldr q0, [x1, #0]
	rev64 v0.16b, v0.16b
	lsr x5, x3, #3
	cbz x5, 20f
	pmull v5.1q, v24.1d, v24.1d
	pmull2 v3.1q, v24.2d, v24.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	pmull v5.1q, v25.1d, v24.1d
	pmull2 v3.1q, v25.2d, v24.2d
	pmull v4.1q, v25.1d, v16.1d
	pmull2 v7.1q, v25.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v26.16b, v5.16b, v7.16b
	ext v18.16b, v26.16b, v26.16b, #8
	pmull v5.1q, v25.1d, v25.1d
	pmull2 v3.1q, v25.2d, v25.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	pmull v5.1q, v26.1d, v25.1d
	pmull2 v3.1q, v26.2d, v25.2d
	pmull v4.1q, v26.1d, v17.1d
	pmull2 v7.1q, v26.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v28.16b, v5.16b, v7.16b
	ext v20.16b, v28.16b, v28.16b, #8
	pmull v5.1q, v26.1d, v26.1d
	pmull2 v3.1q, v26.2d, v26.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	pmull v5.1q, v27.1d, v26.1d
	pmull2 v3.1q, v27.2d, v26.2d
	pmull v4.1q, v27.1d, v18.1d
	pmull2 v7.1q, v27.2d, v18.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v30.16b, v5.16b, v7.16b
	ext v22.16b, v30.16b, v30.16b, #8
	pmull v5.1q, v27.1d, v27.1d
	pmull2 v3.1q, v27.2d, v27.2d
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v3.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
22:
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #16]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v30.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v30.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v22.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v22.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #32]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v29.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v29.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v21.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v21.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #48]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v28.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v28.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v20.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v20.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #64]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #80]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v18.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #96]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #112]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v31.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v31.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v23.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v23.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #128
	sub x3, x3, #8
	lsr x5, x3, #3
	cbnz x5, 22b
	lsr x6, x3, #2
	cbz x6, 23f
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #16]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v18.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #32]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #48]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #64
	sub x3, x3, #4
	lsr x5, x3, #3
	b 24f
23:
24:
	lsr x6, x3, #1
	cbz x6, 25f
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #16]
	rev64 v6.16b, v6.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #32
	sub x3, x3, #2
	lsr x5, x3, #3
	b 26f
25:
26:
	cbz x3, 27f
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #16
	sub x3, x3, #1
	lsr x5, x3, #3
	b 28f
27:
28:
	b 21f
20:
	cbz x3, 29f
211:
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	ldr q6, [x2, #0]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	pmull v7.1q, v6.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v6.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v6.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v6.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v0.16b, v5.16b, v7.16b
	add x2, x2, #16
	sub x3, x3, #1
	lsr x5, x3, #3
	cbnz x3, 211b
	b 210f
29:
210:
21:
	rev64 v0.16b, v0.16b
	str q0, [x1, #0]
	ret
	.arch_extension noaes
	.p2align 6
