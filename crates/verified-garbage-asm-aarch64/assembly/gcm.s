// The functions of `src/gcm.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_store_powers_aes:
	.arch_extension aes
	add x8, x5, #0
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
	cbz x5, 20f
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
	lsr x6, x3, #2
	cbz x6, 29f
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
	b 210f
29:
210:
	lsr x6, x3, #1
	cbz x6, 211f
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
	b 212f
211:
212:
	cbz x3, 213f
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
	b 214f
213:
214:
21:
	rev64 v0.16b, v0.16b
	str q0, [x1, #0]
	str q16, [x8, #16]
	str q17, [x8, #0]
	str q18, [x8, #48]
	str q19, [x8, #32]
	str q20, [x8, #80]
	str q21, [x8, #64]
	str q22, [x8, #112]
	str q23, [x8, #96]
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_init_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x3, sp, #0
	str x20, [x3, #136]
	str x21, [x3, #144]
	str x22, [x3, #152]
	str x23, [x3, #160]
	str x24, [x3, #168]
	str x25, [x3, #176]
	str x26, [x3, #184]
	str x27, [x3, #192]
	str x28, [x3, #200]
	str x30, [x3, #208]
	str x19, [x3, #128]
	add x19, x3, #0
	add x21, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch_aes}
	movz x9, #0, lsl #0
	str x9, [x21, #240]
	str x9, [x21, #248]
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x3, x21, #240
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_seal_aes:
	.arch_extension aes
	sub sp, sp, #2576
	add x16, sp, #0
	ldr x17, [sp, #2576]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	ldr x9, [sp, #8]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x9, x24, #12
	cbz x9, 28f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 210f
	lsr x14, x13, #2
	cbz x14, 212f
	lsr x14, x13, #3
	cbz x14, 214f
216:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 216b
	b 215f
214:
215:
	lsr x14, x13, #2
	cbz x14, 217f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 218f
217:
218:
	cbz x13, 219f
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	b 220f
219:
220:
	b 213f
212:
222:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 222b
213:
	b 211f
210:
211:
	cbz x25, 223f
	movz x3, #1, lsl #0
	b 224f
223:
	movz x3, #0, lsl #0
224:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 29f
28:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
29:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 225f
	lsr x14, x13, #2
	cbz x14, 227f
	lsr x14, x13, #3
	cbz x14, 229f
231:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 231b
	b 230f
229:
230:
	lsr x14, x13, #2
	cbz x14, 232f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 233f
232:
233:
	cbz x13, 234f
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
	b 235f
234:
235:
	b 228f
227:
237:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 237b
228:
	b 226f
225:
226:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 238f
	cbz x27, 240f
	movz x25, #0, lsl #0
	b 241f
240:
241:
	b 239f
238:
	movz x25, #0, lsl #0
239:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 242f
	lsr x14, x13, #2
	cbz x14, 244f
	lsr x14, x13, #3
	cbz x14, 246f
248:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 248b
	b 247f
246:
247:
	lsr x14, x13, #2
	cbz x14, 249f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 250f
249:
250:
	cbz x13, 251f
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
	b 252f
251:
252:
	b 245f
244:
254:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 254b
245:
	b 243f
242:
243:
	cbz x25, 255f
	movz x3, #1, lsl #0
	b 256f
255:
	movz x3, #0, lsl #0
256:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 257f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 259f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 261f
	add x10, x9, #0
	b 262f
261:
	add x10, x24, #0
262:
	b 260f
259:
	add x10, x9, #0
260:
	b 258f
257:
	movz x10, #0, lsl #0
258:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 266f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 267f
266:
	movz x4, #0, lsl #0
267:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 268f
	lsr x14, x13, #2
	cbz x14, 270f
	lsr x14, x13, #3
	cbz x14, 272f
274:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 274b
	b 273f
272:
273:
	lsr x14, x13, #2
	cbz x14, 275f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 276f
275:
276:
	cbz x13, 277f
279:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
	b 278f
277:
278:
	b 271f
270:
280:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 280b
271:
	b 269f
268:
269:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 281f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 283f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 285f
	add x10, x9, #0
	b 286f
285:
	add x10, x24, #0
286:
	b 284f
283:
	add x10, x9, #0
284:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 287f
289:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 289b
	b 288f
287:
288:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 290f
	movz x3, #0, lsl #0
	b 291f
290:
	movz x3, #1, lsl #0
291:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 292f
	lsr x14, x13, #2
	cbz x14, 294f
	lsr x14, x13, #3
	cbz x14, 296f
298:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 298b
	b 297f
296:
297:
	lsr x14, x13, #2
	cbz x14, 299f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2100f
299:
2100:
	cbz x13, 2101f
2103:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2103b
	b 2102f
2101:
2102:
	b 295f
294:
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
295:
	b 293f
292:
293:
	b 282f
281:
282:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 2105f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 2106f
2105:
	movz x9, #15, lsl #0
	and x25, x26, x9
2106:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 2107f
	lsr x14, x13, #2
	cbz x14, 2109f
	lsr x14, x13, #3
	cbz x14, 2111f
2113:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2113b
	b 2112f
2111:
2112:
	lsr x14, x13, #2
	cbz x14, 2114f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2115f
2114:
2115:
	cbz x13, 2116f
2118:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2118b
	b 2117f
2116:
2117:
	b 2110f
2109:
2119:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2119b
2110:
	b 2108f
2107:
2108:
	cbz x25, 2120f
	movz x3, #1, lsl #0
	b 2121f
2120:
	movz x3, #0, lsl #0
2121:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2122f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2124f
	lsr x14, x13, #2
	cbz x14, 2126f
	lsr x14, x13, #3
	cbz x14, 2128f
2130:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2130b
	b 2129f
2128:
2129:
	lsr x14, x13, #2
	cbz x14, 2131f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2132f
2131:
2132:
	cbz x13, 2133f
2135:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2135b
	b 2134f
2133:
2134:
	b 2127f
2126:
2136:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2136b
2127:
	b 2125f
2124:
2125:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2123f
2122:
2123:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x27, x23, #0
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2137f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2138f
2137:
	movz x4, #0, lsl #0
2138:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2139f
	lsr x9, x26, #4
	cbz x9, 2141f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2142f
2141:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2143f
	lsr x14, x13, #2
	cbz x14, 2145f
	lsr x14, x13, #3
	cbz x14, 2147f
2149:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2149b
	b 2148f
2147:
2148:
	lsr x14, x13, #2
	cbz x14, 2150f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2151f
2150:
2151:
	cbz x13, 2152f
2154:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2154b
	b 2153f
2152:
2153:
	b 2146f
2145:
2155:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2155b
2146:
	b 2144f
2143:
2144:
2142:
	b 2140f
2139:
2140:
	add x23, x27, #0
	add x24, x26, #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2156f
	lsr x9, x26, #4
	cbz x9, 2158f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2159f
2158:
	cbz x13, 2160f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2162f
	lsr x14, x13, #2
	cbz x14, 2164f
	lsr x14, x13, #3
	cbz x14, 2166f
2168:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2168b
	b 2167f
2166:
2167:
	lsr x14, x13, #2
	cbz x14, 2169f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2170f
2169:
2170:
	cbz x13, 2171f
2173:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2173b
	b 2172f
2171:
2172:
	b 2165f
2164:
2174:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2174b
2165:
	b 2163f
2162:
2163:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2161f
2160:
2161:
2159:
	b 2157f
2156:
2157:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
27:
	add sp, sp, #2576
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_open_aes:
	.arch_extension aes
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	add x28, x10, #0
	ldr x12, [sp, #0]
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 28f
	lsr x13, x28, #4
	cbz x13, 210f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 211f
210:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 212f
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
	b 213f
212:
213:
211:
	sub x9, x24, #12
	cbz x9, 215f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	cbz x25, 230f
	movz x3, #1, lsl #0
	b 231f
230:
	movz x3, #0, lsl #0
231:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 216f
215:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
216:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 232f
	lsr x14, x13, #2
	cbz x14, 234f
	lsr x14, x13, #3
	cbz x14, 236f
238:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 238b
	b 237f
236:
237:
	lsr x14, x13, #2
	cbz x14, 239f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 240f
239:
240:
	cbz x13, 241f
243:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 243b
	b 242f
241:
242:
	b 235f
234:
244:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 244b
235:
	b 233f
232:
233:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 245f
	cbz x27, 247f
	movz x25, #0, lsl #0
	b 248f
247:
248:
	b 246f
245:
	movz x25, #0, lsl #0
246:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 249f
	lsr x14, x13, #2
	cbz x14, 251f
	lsr x14, x13, #3
	cbz x14, 253f
255:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 255b
	b 254f
253:
254:
	lsr x14, x13, #2
	cbz x14, 256f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 257f
256:
257:
	cbz x13, 258f
260:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 260b
	b 259f
258:
259:
	b 252f
251:
261:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 261b
252:
	b 250f
249:
250:
	cbz x25, 262f
	movz x3, #1, lsl #0
	b 263f
262:
	movz x3, #0, lsl #0
263:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 264f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 266f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 268f
	add x10, x9, #0
	b 269f
268:
	add x10, x24, #0
269:
	b 267f
266:
	add x10, x9, #0
267:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 270f
272:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
	b 271f
270:
271:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 273f
	movz x3, #0, lsl #0
	b 274f
273:
	movz x3, #1, lsl #0
274:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 275f
	lsr x14, x13, #2
	cbz x14, 277f
	lsr x14, x13, #3
	cbz x14, 279f
281:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 281b
	b 280f
279:
280:
	lsr x14, x13, #2
	cbz x14, 282f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 283f
282:
283:
	cbz x13, 284f
286:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 286b
	b 285f
284:
285:
	b 278f
277:
287:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 287b
278:
	b 276f
275:
276:
	b 265f
264:
265:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 288f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 289f
288:
	movz x9, #15, lsl #0
	and x25, x26, x9
289:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 290f
	lsr x14, x13, #2
	cbz x14, 292f
	lsr x14, x13, #3
	cbz x14, 294f
296:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 296b
	b 295f
294:
295:
	lsr x14, x13, #2
	cbz x14, 297f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 298f
297:
298:
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	b 293f
292:
2102:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2102b
293:
	b 291f
290:
291:
	cbz x25, 2103f
	movz x3, #1, lsl #0
	b 2104f
2103:
	movz x3, #0, lsl #0
2104:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 2105f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2106f
2105:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2107f
2109:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2109b
	b 2108f
2107:
2108:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2110f
2112:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2112b
	b 2111f
2110:
2111:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2106:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2113f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2115f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2116f
2115:
	movz x4, #0, lsl #0
2116:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2117f
	lsr x14, x13, #2
	cbz x14, 2119f
	lsr x14, x13, #3
	cbz x14, 2121f
2123:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2123b
	b 2122f
2121:
2122:
	lsr x14, x13, #2
	cbz x14, 2124f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2125f
2124:
2125:
	cbz x13, 2126f
2128:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2128b
	b 2127f
2126:
2127:
	b 2120f
2119:
2129:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2129b
2120:
	b 2118f
2117:
2118:
	b 2114f
2113:
2114:
	add x0, x27, #0
	b 29f
28:
	movz x0, #0, lsl #0
29:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2130f
	lsr x13, x28, #4
	cbz x13, 2132f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2133f
2132:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2134f
2136:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2136b
	b 2135f
2134:
2135:
2133:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2137f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2139f
	lsr x14, x13, #2
	cbz x14, 2141f
	lsr x14, x13, #3
	cbz x14, 2143f
2145:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2145b
	b 2144f
2143:
2144:
	lsr x14, x13, #2
	cbz x14, 2146f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2147f
2146:
2147:
	cbz x13, 2148f
2150:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2150b
	b 2149f
2148:
2149:
	b 2142f
2141:
2151:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2151b
2142:
	b 2140f
2139:
2140:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2138f
2137:
2138:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2152f
	lsr x9, x26, #4
	cbz x9, 2154f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2155f
2154:
	cbz x13, 2156f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2158f
	lsr x14, x13, #2
	cbz x14, 2160f
	lsr x14, x13, #3
	cbz x14, 2162f
2164:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2164b
	b 2163f
2162:
2163:
	lsr x14, x13, #2
	cbz x14, 2165f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2166f
2165:
2166:
	cbz x13, 2167f
2169:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2169b
	b 2168f
2167:
2168:
	b 2161f
2160:
2170:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2170b
2161:
	b 2159f
2158:
2159:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2157f
2156:
2157:
2155:
	b 2153f
2152:
2153:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 2171f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2172f
2171:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2173f
2175:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2175b
	b 2174f
2173:
2174:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2176f
2178:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2178b
	b 2177f
2176:
2177:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2172:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2179f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2181f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2182f
2181:
	movz x4, #0, lsl #0
2182:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2183f
	lsr x9, x26, #4
	cbz x9, 2185f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2186f
2185:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2187f
	lsr x14, x13, #2
	cbz x14, 2189f
	lsr x14, x13, #3
	cbz x14, 2191f
2193:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2193b
	b 2192f
2191:
2192:
	lsr x14, x13, #2
	cbz x14, 2194f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2195f
2194:
2195:
	cbz x13, 2196f
2198:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2198b
	b 2197f
2196:
2197:
	b 2190f
2189:
2199:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2199b
2190:
	b 2188f
2187:
2188:
2186:
	b 2184f
2183:
2184:
	b 2180f
2179:
2180:
	add x0, x27, #0
	b 2131f
2130:
	movz x0, #0, lsl #0
2131:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
27:
	add sp, sp, #2592
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_init_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x4, sp, #0
	str x20, [x4, #136]
	str x21, [x4, #144]
	str x22, [x4, #152]
	str x23, [x4, #160]
	str x24, [x4, #168]
	str x25, [x4, #176]
	str x26, [x4, #184]
	str x27, [x4, #192]
	str x28, [x4, #200]
	str x30, [x4, #208]
	str x19, [x4, #128]
	add x19, x4, #0
	add x20, x3, #0
	add x21, x0, #0
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_aad_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x23, x3, #0
	add x24, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 20f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 22f
	add x10, x9, #0
	b 23f
22:
	add x10, x24, #0
23:
	b 21f
20:
	add x10, x9, #0
21:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 27f
	movz x3, #0, lsl #0
	b 28f
27:
	movz x3, #1, lsl #0
28:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_encrypt_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x6, #0
	add x27, x4, #0
	add x28, x5, #0
	movz x9, #15, lsl #0
	and x25, x3, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	b 220f
219:
	movz x10, #0, lsl #0
220:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 228f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 229f
228:
	movz x4, #0, lsl #0
229:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 252f
	movz x3, #0, lsl #0
	b 253f
252:
	movz x3, #1, lsl #0
253:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	b 244f
243:
244:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_decrypt_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x6, #0
	add x27, x4, #0
	add x28, x5, #0
	movz x9, #15, lsl #0
	and x25, x3, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 228f
	movz x3, #0, lsl #0
	b 229f
228:
	movz x3, #1, lsl #0
229:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	b 220f
219:
220:
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	b 244f
243:
	movz x10, #0, lsl #0
244:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 252f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 253f
252:
	movz x4, #0, lsl #0
253:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_finish_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x5, #0
	cbz x27, 20f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 21f
20:
	movz x9, #15, lsl #0
	and x25, x26, x9
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_stream_verify_aes:
	.arch_extension aes
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x6, #0
	add x12, x5, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	cbz x27, 27f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 28f
27:
	movz x9, #15, lsl #0
	and x25, x26, x9
28:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 224f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 225f
224:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 229f
231:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 231b
	b 230f
229:
230:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
225:
	movz x0, #1, lsl #0
	sub x0, x0, x10
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_seal_gather_aes:
	.arch_extension aes
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	ldr x11, [sp, #16]
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	ldr x6, [sp, #16]
	ldr x7, [sp, #24]
	bl {vg_aes_gcm_seal_aes}
	ldr x30, [sp, #8]
	add sp, sp, #16
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_seal_with_powers_aes:
	.arch_extension aes
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x9, x24, #12
	cbz x9, 28f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 210f
	lsr x14, x13, #2
	cbz x14, 212f
	lsr x14, x13, #3
	cbz x14, 214f
216:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 216b
	b 215f
214:
215:
	lsr x14, x13, #2
	cbz x14, 217f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 218f
217:
218:
	cbz x13, 219f
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	b 220f
219:
220:
	b 213f
212:
222:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 222b
213:
	b 211f
210:
211:
	cbz x25, 223f
	movz x3, #1, lsl #0
	b 224f
223:
	movz x3, #0, lsl #0
224:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 29f
28:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
29:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 225f
	lsr x14, x13, #2
	cbz x14, 227f
	lsr x14, x13, #3
	cbz x14, 229f
231:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 231b
	b 230f
229:
230:
	lsr x14, x13, #2
	cbz x14, 232f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 233f
232:
233:
	cbz x13, 234f
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
	b 235f
234:
235:
	b 228f
227:
237:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 237b
228:
	b 226f
225:
226:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 238f
	cbz x27, 240f
	movz x25, #0, lsl #0
	b 241f
240:
241:
	b 239f
238:
	movz x25, #0, lsl #0
239:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 242f
	lsr x14, x13, #2
	cbz x14, 244f
	lsr x14, x13, #3
	cbz x14, 246f
248:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 248b
	b 247f
246:
247:
	lsr x14, x13, #2
	cbz x14, 249f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 250f
249:
250:
	cbz x13, 251f
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
	b 252f
251:
252:
	b 245f
244:
254:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 254b
245:
	b 243f
242:
243:
	cbz x25, 255f
	movz x3, #1, lsl #0
	b 256f
255:
	movz x3, #0, lsl #0
256:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 257f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 259f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 261f
	add x10, x9, #0
	b 262f
261:
	add x10, x24, #0
262:
	b 260f
259:
	add x10, x9, #0
260:
	b 258f
257:
	movz x10, #0, lsl #0
258:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 266f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 267f
266:
	movz x4, #0, lsl #0
267:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 268f
	lsr x14, x13, #2
	cbz x14, 270f
	lsr x14, x13, #3
	cbz x14, 272f
274:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 274b
	b 273f
272:
273:
	lsr x14, x13, #2
	cbz x14, 275f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 276f
275:
276:
	cbz x13, 277f
279:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
	b 278f
277:
278:
	b 271f
270:
280:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 280b
271:
	b 269f
268:
269:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 281f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 283f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 285f
	add x10, x9, #0
	b 286f
285:
	add x10, x24, #0
286:
	b 284f
283:
	add x10, x9, #0
284:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 287f
289:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 289b
	b 288f
287:
288:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 290f
	movz x3, #0, lsl #0
	b 291f
290:
	movz x3, #1, lsl #0
291:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 292f
	lsr x14, x13, #2
	cbz x14, 294f
	lsr x14, x13, #3
	cbz x14, 296f
298:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 298b
	b 297f
296:
297:
	lsr x14, x13, #2
	cbz x14, 299f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2100f
299:
2100:
	cbz x13, 2101f
2103:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2103b
	b 2102f
2101:
2102:
	b 295f
294:
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
295:
	b 293f
292:
293:
	b 282f
281:
282:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 2105f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 2106f
2105:
	movz x9, #15, lsl #0
	and x25, x26, x9
2106:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 2107f
	lsr x14, x13, #2
	cbz x14, 2109f
	lsr x14, x13, #3
	cbz x14, 2111f
2113:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2113b
	b 2112f
2111:
2112:
	lsr x14, x13, #2
	cbz x14, 2114f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2115f
2114:
2115:
	cbz x13, 2116f
2118:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2118b
	b 2117f
2116:
2117:
	b 2110f
2109:
2119:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2119b
2110:
	b 2108f
2107:
2108:
	cbz x25, 2120f
	movz x3, #1, lsl #0
	b 2121f
2120:
	movz x3, #0, lsl #0
2121:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2122f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2124f
	lsr x14, x13, #2
	cbz x14, 2126f
	lsr x14, x13, #3
	cbz x14, 2128f
2130:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2130b
	b 2129f
2128:
2129:
	lsr x14, x13, #2
	cbz x14, 2131f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2132f
2131:
2132:
	cbz x13, 2133f
2135:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2135b
	b 2134f
2133:
2134:
	b 2127f
2126:
2136:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2136b
2127:
	b 2125f
2124:
2125:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2123f
2122:
2123:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x27, x23, #0
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2137f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2138f
2137:
	movz x4, #0, lsl #0
2138:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2139f
	lsr x9, x26, #4
	cbz x9, 2141f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2142f
2141:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2143f
	lsr x14, x13, #2
	cbz x14, 2145f
	lsr x14, x13, #3
	cbz x14, 2147f
2149:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2149b
	b 2148f
2147:
2148:
	lsr x14, x13, #2
	cbz x14, 2150f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2151f
2150:
2151:
	cbz x13, 2152f
2154:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2154b
	b 2153f
2152:
2153:
	b 2146f
2145:
2155:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2155b
2146:
	b 2144f
2143:
2144:
2142:
	b 2140f
2139:
2140:
	add x23, x27, #0
	add x24, x26, #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2156f
	ldr x5, [sp, #8]
	bl {vg_ghash_with_powers_aes}
	b 2157f
2156:
	bl {vg_ghash_aes}
2157:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2158f
	lsr x9, x26, #4
	cbz x9, 2160f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2161f
2160:
	cbz x13, 2162f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2164f
	lsr x14, x13, #2
	cbz x14, 2166f
	lsr x14, x13, #3
	cbz x14, 2168f
2170:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2170b
	b 2169f
2168:
2169:
	lsr x14, x13, #2
	cbz x14, 2171f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2172f
2171:
2172:
	cbz x13, 2173f
2175:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2175b
	b 2174f
2173:
2174:
	b 2167f
2166:
2176:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2176b
2167:
	b 2165f
2164:
2165:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2163f
2162:
2163:
2161:
	b 2159f
2158:
2159:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
27:
	add sp, sp, #2592
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_open_with_powers_aes:
	.arch_extension aes
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	ldr x17, [sp, #2608]
	str x17, [x16, #16]
	add x17, sp, #32
	str x17, [x16, #24]
	ldr x9, [sp, #24]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	add x28, x10, #0
	ldr x12, [sp, #0]
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 28f
	lsr x13, x28, #4
	cbz x13, 210f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 211f
210:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 212f
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
	b 213f
212:
213:
211:
	sub x9, x24, #12
	cbz x9, 215f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	cbz x25, 230f
	movz x3, #1, lsl #0
	b 231f
230:
	movz x3, #0, lsl #0
231:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 216f
215:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
216:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 232f
	lsr x14, x13, #2
	cbz x14, 234f
	lsr x14, x13, #3
	cbz x14, 236f
238:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 238b
	b 237f
236:
237:
	lsr x14, x13, #2
	cbz x14, 239f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 240f
239:
240:
	cbz x13, 241f
243:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 243b
	b 242f
241:
242:
	b 235f
234:
244:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 244b
235:
	b 233f
232:
233:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 245f
	cbz x27, 247f
	movz x25, #0, lsl #0
	b 248f
247:
248:
	b 246f
245:
	movz x25, #0, lsl #0
246:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 249f
	lsr x14, x13, #2
	cbz x14, 251f
	lsr x14, x13, #3
	cbz x14, 253f
255:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 255b
	b 254f
253:
254:
	lsr x14, x13, #2
	cbz x14, 256f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 257f
256:
257:
	cbz x13, 258f
260:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 260b
	b 259f
258:
259:
	b 252f
251:
261:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 261b
252:
	b 250f
249:
250:
	cbz x25, 262f
	movz x3, #1, lsl #0
	b 263f
262:
	movz x3, #0, lsl #0
263:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 264f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 266f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 268f
	add x10, x9, #0
	b 269f
268:
	add x10, x24, #0
269:
	b 267f
266:
	add x10, x9, #0
267:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 270f
272:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
	b 271f
270:
271:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 273f
	movz x3, #0, lsl #0
	b 274f
273:
	movz x3, #1, lsl #0
274:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 275f
	lsr x14, x13, #2
	cbz x14, 277f
	lsr x14, x13, #3
	cbz x14, 279f
281:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 281b
	b 280f
279:
280:
	lsr x14, x13, #2
	cbz x14, 282f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 283f
282:
283:
	cbz x13, 284f
286:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 286b
	b 285f
284:
285:
	b 278f
277:
287:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 287b
278:
	b 276f
275:
276:
	b 265f
264:
265:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 288f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 289f
288:
	movz x9, #15, lsl #0
	and x25, x26, x9
289:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 290f
	lsr x14, x13, #2
	cbz x14, 292f
	lsr x14, x13, #3
	cbz x14, 294f
296:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 296b
	b 295f
294:
295:
	lsr x14, x13, #2
	cbz x14, 297f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 298f
297:
298:
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	b 293f
292:
2102:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2102b
293:
	b 291f
290:
291:
	cbz x25, 2103f
	movz x3, #1, lsl #0
	b 2104f
2103:
	movz x3, #0, lsl #0
2104:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 2105f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2106f
2105:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2107f
2109:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2109b
	b 2108f
2107:
2108:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2110f
2112:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2112b
	b 2111f
2110:
2111:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2106:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2113f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2115f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2116f
2115:
	movz x4, #0, lsl #0
2116:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2117f
	lsr x14, x13, #2
	cbz x14, 2119f
	lsr x14, x13, #3
	cbz x14, 2121f
2123:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2123b
	b 2122f
2121:
2122:
	lsr x14, x13, #2
	cbz x14, 2124f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2125f
2124:
2125:
	cbz x13, 2126f
2128:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2128b
	b 2127f
2126:
2127:
	b 2120f
2119:
2129:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2129b
2120:
	b 2118f
2117:
2118:
	b 2114f
2113:
2114:
	add x0, x27, #0
	b 29f
28:
	movz x0, #0, lsl #0
29:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2130f
	lsr x13, x28, #4
	cbz x13, 2132f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2133f
2132:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2134f
2136:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2136b
	b 2135f
2134:
2135:
2133:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2137f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2139f
	lsr x14, x13, #2
	cbz x14, 2141f
	lsr x14, x13, #3
	cbz x14, 2143f
2145:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2145b
	b 2144f
2143:
2144:
	lsr x14, x13, #2
	cbz x14, 2146f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2147f
2146:
2147:
	cbz x13, 2148f
2150:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2150b
	b 2149f
2148:
2149:
	b 2142f
2141:
2151:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2151b
2142:
	b 2140f
2139:
2140:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2138f
2137:
2138:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2152f
	ldr x5, [sp, #16]
	bl {vg_ghash_with_powers_aes}
	b 2153f
2152:
	bl {vg_ghash_aes}
2153:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2154f
	lsr x9, x26, #4
	cbz x9, 2156f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2157f
2156:
	cbz x13, 2158f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2160f
	lsr x14, x13, #2
	cbz x14, 2162f
	lsr x14, x13, #3
	cbz x14, 2164f
2166:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2166b
	b 2165f
2164:
2165:
	lsr x14, x13, #2
	cbz x14, 2167f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2168f
2167:
2168:
	cbz x13, 2169f
2171:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2171b
	b 2170f
2169:
2170:
	b 2163f
2162:
2172:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2172b
2163:
	b 2161f
2160:
2161:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2159f
2158:
2159:
2157:
	b 2155f
2154:
2155:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 2173f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2174f
2173:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2175f
2177:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2177b
	b 2176f
2175:
2176:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2178f
2180:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2180b
	b 2179f
2178:
2179:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2174:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2181f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2183f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2184f
2183:
	movz x4, #0, lsl #0
2184:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2185f
	lsr x9, x26, #4
	cbz x9, 2187f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2188f
2187:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2189f
	lsr x14, x13, #2
	cbz x14, 2191f
	lsr x14, x13, #3
	cbz x14, 2193f
2195:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2195b
	b 2194f
2193:
2194:
	lsr x14, x13, #2
	cbz x14, 2196f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2197f
2196:
2197:
	cbz x13, 2198f
2200:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2200b
	b 2199f
2198:
2199:
	b 2192f
2191:
2201:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2201b
2192:
	b 2190f
2189:
2190:
2188:
	b 2186f
2185:
2186:
	b 2182f
2181:
2182:
	add x0, x27, #0
	b 2131f
2130:
	movz x0, #0, lsl #0
2131:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
27:
	add sp, sp, #2592
	ret
	.arch_extension noaes
	.p2align 6

// vg_aes_gcm_init_aes_sha3: the function `vg_aes_gcm_init_aes`

// vg_aes_gcm_seal_aes_sha3: the function `vg_aes_gcm_seal_aes`

// vg_aes_gcm_open_aes_sha3: the function `vg_aes_gcm_open_aes`

// vg_aes_gcm_stream_init_aes_sha3: the function `vg_aes_gcm_stream_init_aes`

// vg_aes_gcm_stream_aad_aes_sha3: the function `vg_aes_gcm_stream_aad_aes`

// vg_aes_gcm_stream_encrypt_aes_sha3: the function `vg_aes_gcm_stream_encrypt_aes`

// vg_aes_gcm_stream_decrypt_aes_sha3: the function `vg_aes_gcm_stream_decrypt_aes`

// vg_aes_gcm_stream_finish_aes_sha3: the function `vg_aes_gcm_stream_finish_aes`

// vg_aes_gcm_stream_verify_aes_sha3: the function `vg_aes_gcm_stream_verify_aes`

vg_aes_gcm_seal_gather_aes_sha3:
	.arch_extension aes
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	ldr x11, [sp, #16]
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	ldr x6, [sp, #16]
	ldr x7, [sp, #24]
	bl {vg_aes_gcm_seal_aes_sha3}
	ldr x30, [sp, #8]
	add sp, sp, #16
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_seal_with_powers_aes_sha3:
	.arch_extension aes
	.arch_extension sha3
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x9, x24, #12
	cbz x9, 28f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 210f
	lsr x14, x13, #2
	cbz x14, 212f
	lsr x14, x13, #3
	cbz x14, 214f
216:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 216b
	b 215f
214:
215:
	lsr x14, x13, #2
	cbz x14, 217f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 218f
217:
218:
	cbz x13, 219f
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	b 220f
219:
220:
	b 213f
212:
222:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 222b
213:
	b 211f
210:
211:
	cbz x25, 223f
	movz x3, #1, lsl #0
	b 224f
223:
	movz x3, #0, lsl #0
224:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 29f
28:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
29:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 225f
	lsr x14, x13, #2
	cbz x14, 227f
	lsr x14, x13, #3
	cbz x14, 229f
231:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 231b
	b 230f
229:
230:
	lsr x14, x13, #2
	cbz x14, 232f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 233f
232:
233:
	cbz x13, 234f
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
	b 235f
234:
235:
	b 228f
227:
237:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 237b
228:
	b 226f
225:
226:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 238f
	cbz x27, 240f
	movz x25, #0, lsl #0
	b 241f
240:
241:
	b 239f
238:
	movz x25, #0, lsl #0
239:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 242f
	lsr x14, x13, #2
	cbz x14, 244f
	lsr x14, x13, #3
	cbz x14, 246f
248:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 248b
	b 247f
246:
247:
	lsr x14, x13, #2
	cbz x14, 249f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 250f
249:
250:
	cbz x13, 251f
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
	b 252f
251:
252:
	b 245f
244:
254:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 254b
245:
	b 243f
242:
243:
	cbz x25, 255f
	movz x3, #1, lsl #0
	b 256f
255:
	movz x3, #0, lsl #0
256:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 257f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 259f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 261f
	add x10, x9, #0
	b 262f
261:
	add x10, x24, #0
262:
	b 260f
259:
	add x10, x9, #0
260:
	b 258f
257:
	movz x10, #0, lsl #0
258:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 266f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 267f
266:
	movz x4, #0, lsl #0
267:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 268f
	lsr x14, x13, #2
	cbz x14, 270f
	lsr x14, x13, #3
	cbz x14, 272f
274:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 274b
	b 273f
272:
273:
	lsr x14, x13, #2
	cbz x14, 275f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 276f
275:
276:
	cbz x13, 277f
279:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
	b 278f
277:
278:
	b 271f
270:
280:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 280b
271:
	b 269f
268:
269:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 281f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 283f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 285f
	add x10, x9, #0
	b 286f
285:
	add x10, x24, #0
286:
	b 284f
283:
	add x10, x9, #0
284:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 287f
289:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 289b
	b 288f
287:
288:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 290f
	movz x3, #0, lsl #0
	b 291f
290:
	movz x3, #1, lsl #0
291:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 292f
	lsr x14, x13, #2
	cbz x14, 294f
	lsr x14, x13, #3
	cbz x14, 296f
298:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 298b
	b 297f
296:
297:
	lsr x14, x13, #2
	cbz x14, 299f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2100f
299:
2100:
	cbz x13, 2101f
2103:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2103b
	b 2102f
2101:
2102:
	b 295f
294:
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
295:
	b 293f
292:
293:
	b 282f
281:
282:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 2105f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 2106f
2105:
	movz x9, #15, lsl #0
	and x25, x26, x9
2106:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 2107f
	lsr x14, x13, #2
	cbz x14, 2109f
	lsr x14, x13, #3
	cbz x14, 2111f
2113:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2113b
	b 2112f
2111:
2112:
	lsr x14, x13, #2
	cbz x14, 2114f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2115f
2114:
2115:
	cbz x13, 2116f
2118:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2118b
	b 2117f
2116:
2117:
	b 2110f
2109:
2119:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2119b
2110:
	b 2108f
2107:
2108:
	cbz x25, 2120f
	movz x3, #1, lsl #0
	b 2121f
2120:
	movz x3, #0, lsl #0
2121:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	add x9, x7, #31
	lsr x9, x9, #7
	cbz x9, 2122f
	add x9, x7, #256
	lsr x9, x9, #10
	cbz x9, 2124f
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2126f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2128f
	lsr x14, x13, #2
	cbz x14, 2130f
	lsr x14, x13, #3
	cbz x14, 2132f
2134:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2134b
	b 2133f
2132:
2133:
	lsr x14, x13, #2
	cbz x14, 2135f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2136f
2135:
2136:
	cbz x13, 2137f
2139:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2139b
	b 2138f
2137:
2138:
	b 2131f
2130:
2140:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2140b
2131:
	b 2129f
2128:
2129:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2127f
2126:
2127:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	lsr x9, x26, #7
	cbz x9, 2141f
	ldr x5, [sp, #8]
	ldr q16, [x5, #16]
	ext v24.16b, v16.16b, v16.16b, #8
	ldr q17, [x5, #0]
	ext v25.16b, v17.16b, v17.16b, #8
	ldr q18, [x5, #48]
	ext v26.16b, v18.16b, v18.16b, #8
	ldr q19, [x5, #32]
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q20, [x5, #80]
	ext v28.16b, v20.16b, v20.16b, #8
	ldr q21, [x5, #64]
	ext v29.16b, v21.16b, v21.16b, #8
	ldr q22, [x5, #112]
	ext v30.16b, v22.16b, v22.16b, #8
	ldr q23, [x5, #96]
	ext v31.16b, v23.16b, v23.16b, #8
	str q24, [x19, #512]
	str q25, [x19, #528]
	str q26, [x19, #544]
	str q27, [x19, #560]
	str q28, [x19, #576]
	str q29, [x19, #592]
	str q30, [x19, #608]
	str q31, [x19, #624]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #672]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #688]
	ldr w10, [x20, #60]
	rev w10, w10
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x20, #16]
	rev64 v16.16b, v16.16b
	add x9, x23, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 2143f
	cbz x14, 2145f
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 2147f
2149:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	ldr q0, [x20, #48]
	rev64 v21.16b, v21.16b
	mov v0.s[3], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	rev w12, w12
	ldr q1, [x20, #48]
	rev64 v22.16b, v22.16b
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q23, [x19, #608]
	rev w12, w12
	ldr q2, [x20, #48]
	ldr q24, [x19, #592]
	mov v2.s[3], w12
	add w12, w10, #3
	ldr q25, [x19, #640]
	rev w12, w12
	ldr q3, [x20, #48]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	trn2 v27.2d, v21.2d, v22.2d
	rev w12, w12
	ldr q4, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v4.s[3], w12
	add w12, w10, #5
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull v29.1q, v22.1d, v24.1d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	mov v6.s[3], w12
	add w12, w10, #7
	pmull v27.1q, v26.1d, v25.1d
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #48]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #576]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #560]
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #656]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #80]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #96]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	ldr q23, [x19, #544]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #528]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #672]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #112]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v21.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	ldr q22, [x9, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	rev64 v22.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v22.16b, v22.16b, v16.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #512]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #128]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #144]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #160]
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #176]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #192]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #208]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #224]
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #240]
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2149b
	b 2148f
2147:
2148:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
	b 2146f
2145:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 2150f
2152:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev w12, w12
	rev64 v22.16b, v22.16b
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	ldr q23, [x19, #608]
	add w12, w10, #2
	rev w12, w12
	ldr q24, [x19, #592]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	ldr q25, [x19, #640]
	add w12, w10, #3
	rev w12, w12
	trn1 v26.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	trn2 v27.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	eor v26.16b, v26.16b, v27.16b
	rev w12, w12
	ldr q4, [x20, #48]
	pmull v28.1q, v21.1d, v23.1d
	mov v4.s[3], w12
	add w12, w10, #5
	pmull2 v21.1q, v21.2d, v23.2d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull v29.1q, v22.1d, v24.1d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull2 v22.1q, v22.2d, v24.2d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull v27.1q, v26.1d, v25.1d
	mov v6.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	add w12, w10, #7
	rev w12, w12
	eor v18.16b, v28.16b, v29.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	eor v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #48]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q22, [x9, #64]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #576]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #560]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #656]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q21, [x9, #80]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v21.16b, v21.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	trn2 v27.2d, v21.2d, v22.2d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v26.16b, v26.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #112]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #0]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor v22.16b, v22.16b, v16.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #512]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q24, [x19, #624]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #688]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #176]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #144]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #160]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #176]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #192]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	pmull v26.1q, v20.1d, v17.1d
	ldr q31, [x9, #208]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q31, [x9, #224]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #240]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2152b
	b 2151f
2150:
2151:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
2146:
	b 2144f
2143:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	sub x11, x11, #1
	cbz x11, 2153f
2155:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev64 v22.16b, v22.16b
	rev w12, w12
	ldr q1, [x20, #48]
	ldr q23, [x19, #608]
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q24, [x19, #592]
	rev w12, w12
	ldr q25, [x19, #640]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	trn1 v26.2d, v21.2d, v22.2d
	add w12, w10, #3
	rev w12, w12
	trn2 v27.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v3.s[3], w12
	add w12, w10, #4
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q4, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v4.s[3], w12
	pmull v29.1q, v22.1d, v24.1d
	add w12, w10, #5
	rev w12, w12
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	pmull v27.1q, v26.1d, v25.1d
	add w12, w10, #6
	pmull2 v26.1q, v26.2d, v25.2d
	rev w12, w12
	ldr q6, [x20, #48]
	eor v18.16b, v28.16b, v29.16b
	mov v6.s[3], w12
	add w12, w10, #7
	eor v19.16b, v21.16b, v22.16b
	rev w12, w12
	eor v20.16b, v27.16b, v26.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q21, [x9, #48]
	ldr q30, [x21, #0]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #576]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q24, [x19, #560]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	ldr q25, [x19, #656]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v26.16b, v26.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #80]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v27.1q, v26.1d, v25.1d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #112]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #0]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v22.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v22.16b, v22.16b, v16.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q23, [x19, #512]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v26.16b, v26.16b, v27.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v28.1q, v21.1d, v23.1d
	ldr q30, [x21, #144]
	pmull2 v21.1q, v21.2d, v23.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #128]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #144]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x9, #160]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #176]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #192]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #208]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #224]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #240]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #128]
	str q1, [x9, #144]
	str q2, [x9, #160]
	str q3, [x9, #176]
	str q4, [x9, #192]
	str q5, [x9, #208]
	str q6, [x9, #224]
	str q7, [x9, #240]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2155b
	b 2154f
2153:
2154:
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
2144:
	rev64 v16.16b, v16.16b
	str q16, [x20, #16]
	rev w12, w10
	str w12, [x20, #60]
	b 2142f
2141:
2142:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x23, x23, x9
	add x27, x23, #0
	sub x24, x26, x9
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2156f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2157f
2156:
	movz x4, #0, lsl #0
2157:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2158f
	lsr x9, x26, #4
	cbz x9, 2160f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2161f
2160:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2162f
	lsr x14, x13, #2
	cbz x14, 2164f
	lsr x14, x13, #3
	cbz x14, 2166f
2168:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2168b
	b 2167f
2166:
2167:
	lsr x14, x13, #2
	cbz x14, 2169f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2170f
2169:
2170:
	cbz x13, 2171f
2173:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2173b
	b 2172f
2171:
2172:
	b 2165f
2164:
2174:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2174b
2165:
	b 2163f
2162:
2163:
2161:
	b 2159f
2158:
2159:
	add x23, x27, #0
	lsr x9, x26, #7
	lsl x9, x9, #7
	sub x24, x26, x9
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2175f
	ldr x5, [sp, #8]
	bl {vg_ghash_with_powers_aes}
	b 2176f
2175:
	bl {vg_ghash_aes}
2176:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2177f
	lsr x9, x26, #4
	cbz x9, 2179f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2180f
2179:
	cbz x13, 2181f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2183f
	lsr x14, x13, #2
	cbz x14, 2185f
	lsr x14, x13, #3
	cbz x14, 2187f
2189:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2189b
	b 2188f
2187:
2188:
	lsr x14, x13, #2
	cbz x14, 2190f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2191f
2190:
2191:
	cbz x13, 2192f
2194:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2194b
	b 2193f
2192:
2193:
	b 2186f
2185:
2195:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2195b
2186:
	b 2184f
2183:
2184:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2182f
2181:
2182:
2180:
	b 2178f
2177:
2178:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 2125f
2124:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2196f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2198f
	lsr x14, x13, #2
	cbz x14, 2200f
	lsr x14, x13, #3
	cbz x14, 2202f
2204:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2204b
	b 2203f
2202:
2203:
	lsr x14, x13, #2
	cbz x14, 2205f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2206f
2205:
2206:
	cbz x13, 2207f
2209:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2209b
	b 2208f
2207:
2208:
	b 2201f
2200:
2210:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2210b
2201:
	b 2199f
2198:
2199:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2197f
2196:
2197:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x27, x23, #0
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2211f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2212f
2211:
	movz x4, #0, lsl #0
2212:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2213f
	lsr x9, x26, #4
	cbz x9, 2215f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2216f
2215:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2217f
	lsr x14, x13, #2
	cbz x14, 2219f
	lsr x14, x13, #3
	cbz x14, 2221f
2223:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2223b
	b 2222f
2221:
2222:
	lsr x14, x13, #2
	cbz x14, 2224f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2225f
2224:
2225:
	cbz x13, 2226f
2228:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2228b
	b 2227f
2226:
2227:
	b 2220f
2219:
2229:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2229b
2220:
	b 2218f
2217:
2218:
2216:
	b 2214f
2213:
2214:
	add x23, x27, #0
	add x24, x26, #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2230f
	ldr x5, [sp, #8]
	bl {vg_ghash_with_powers_aes}
	b 2231f
2230:
	bl {vg_ghash_aes}
2231:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2232f
	lsr x9, x26, #4
	cbz x9, 2234f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2235f
2234:
	cbz x13, 2236f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2238f
	lsr x14, x13, #2
	cbz x14, 2240f
	lsr x14, x13, #3
	cbz x14, 2242f
2244:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2244b
	b 2243f
2242:
2243:
	lsr x14, x13, #2
	cbz x14, 2245f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2246f
2245:
2246:
	cbz x13, 2247f
2249:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2249b
	b 2248f
2247:
2248:
	b 2241f
2240:
2250:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2250b
2241:
	b 2239f
2238:
2239:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2237f
2236:
2237:
2235:
	b 2233f
2232:
2233:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
2125:
	b 2123f
2122:
	add x9, x7, #15
	lsr x9, x9, #5
	cbz x9, 2251f
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x26, x7, #0
	add x27, x6, #0
	add x24, x5, #0
	add x25, x7, #15
	lsr x25, x25, #4
	lsl x25, x25, #4
	ldr x5, [sp, #8]
	ldr q16, [x5, #16]
	ext v24.16b, v16.16b, v16.16b, #8
	ldr q17, [x5, #0]
	ext v25.16b, v17.16b, v17.16b, #8
	ldr q18, [x5, #48]
	ext v26.16b, v18.16b, v18.16b, #8
	ldr q19, [x5, #32]
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q20, [x5, #80]
	ext v28.16b, v20.16b, v20.16b, #8
	ldr q21, [x5, #64]
	ext v29.16b, v21.16b, v21.16b, #8
	ldr q22, [x5, #112]
	ext v30.16b, v22.16b, v22.16b, #8
	ldr q23, [x5, #96]
	ext v31.16b, v23.16b, v23.16b, #8
	str q24, [x19, #512]
	str q25, [x19, #528]
	str q26, [x19, #544]
	str q27, [x19, #560]
	str q28, [x19, #576]
	str q29, [x19, #592]
	str q30, [x19, #608]
	str q31, [x19, #624]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #672]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #688]
	movi v0.2d, #0
	str q0, [x19, #896]
	str q0, [x19, #912]
	str q0, [x19, #928]
	str q0, [x19, #944]
	str q0, [x19, #960]
	str q0, [x19, #976]
	str q0, [x19, #992]
	str q0, [x19, #1008]
	add x9, x19, #864
	sub x9, x9, x25
	str q0, [x9, #0]
	add x11, x19, #880
	sub x11, x11, x25
	add x12, x27, #0
	add x13, x26, #0
	lsr x14, x13, #4
	cbz x14, 2253f
	add x9, x12, x13
	sub x9, x9, #16
	add x10, x11, x13
	sub x10, x10, #16
2255:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2255b
	ldr q0, [x9, #0]
	str q0, [x10, #0]
	b 2254f
2253:
	cbz x13, 2256f
	lsr x14, x13, #2
	cbz x14, 2258f
	lsr x14, x13, #3
	cbz x14, 2260f
2262:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2262b
	b 2261f
2260:
2261:
	lsr x14, x13, #2
	cbz x14, 2263f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2264f
2263:
2264:
	cbz x13, 2265f
2267:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2267b
	b 2266f
2265:
2266:
	b 2259f
2258:
2268:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2268b
2259:
	b 2257f
2256:
2257:
2254:
	ldr w10, [x20, #60]
	rev w10, w10
	lsr x9, x25, #4
	add w10, w10, w9
	sub w10, w10, #7
	add x9, x19, #768
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 2269f
	cbz x14, 2271f
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	b 2272f
2271:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
2272:
	b 2270f
2269:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
2270:
	add x12, x19, #880
	sub x12, x12, x25
	add x11, x27, #0
	add x13, x26, #0
	lsr x14, x13, #4
	cbz x14, 2273f
	add x9, x12, x13
	sub x9, x9, #16
	add x10, x11, x13
	sub x10, x10, #16
2275:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2275b
	ldr q0, [x9, #0]
	str q0, [x10, #0]
	b 2274f
2273:
	cbz x13, 2276f
	lsr x14, x13, #2
	cbz x14, 2278f
	lsr x14, x13, #3
	cbz x14, 2280f
2282:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2282b
	b 2281f
2280:
2281:
	lsr x14, x13, #2
	cbz x14, 2283f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2284f
2283:
2284:
	cbz x13, 2285f
2287:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2287b
	b 2286f
2285:
2286:
	b 2279f
2278:
2288:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2288b
2279:
	b 2277f
2276:
2277:
2274:
	add x12, x19, #880
	sub x12, x12, x25
	add x11, x19, #1008
	sub x11, x11, x25
	lsr x14, x25, #4
	cbz x14, 2289f
2291:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2291b
	b 2290f
2289:
2290:
	add x9, x19, #1008
	sub x9, x9, x25
	add x9, x9, x26
	movi v0.2d, #0
	str q0, [x9, #0]
	add x12, x4, #0
	add x11, x19, #992
	sub x11, x11, x25
	add x13, x24, #0
	cbz x13, 2292f
	lsr x14, x13, #2
	cbz x14, 2294f
	lsr x14, x13, #3
	cbz x14, 2296f
2298:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2298b
	b 2297f
2296:
2297:
	lsr x14, x13, #2
	cbz x14, 2299f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2300f
2299:
2300:
	cbz x13, 2301f
2303:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2303b
	b 2302f
2301:
2302:
	b 2295f
2294:
2304:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2304b
2295:
	b 2293f
2292:
2293:
	lsl x9, x24, #3
	rev x9, x9
	str x9, [x19, #1008]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #1016]
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	movi v16.2d, #0
	add x9, x19, #896
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	rev64 v16.16b, v16.16b
	add x9, x19, #864
	sub x9, x9, x25
	ldr q0, [x9, #0]
	eor v16.16b, v16.16b, v0.16b
	str q16, [x19, #0]
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 2252f
2251:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2305f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2307f
	lsr x14, x13, #2
	cbz x14, 2309f
	lsr x14, x13, #3
	cbz x14, 2311f
2313:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2313b
	b 2312f
2311:
2312:
	lsr x14, x13, #2
	cbz x14, 2314f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2315f
2314:
2315:
	cbz x13, 2316f
2318:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2318b
	b 2317f
2316:
2317:
	b 2310f
2309:
2319:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2319b
2310:
	b 2308f
2307:
2308:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2306f
2305:
2306:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x27, x23, #0
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2320f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2321f
2320:
	movz x4, #0, lsl #0
2321:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2322f
	lsr x9, x26, #4
	cbz x9, 2324f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2325f
2324:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2326f
	lsr x14, x13, #2
	cbz x14, 2328f
	lsr x14, x13, #3
	cbz x14, 2330f
2332:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2332b
	b 2331f
2330:
2331:
	lsr x14, x13, #2
	cbz x14, 2333f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2334f
2333:
2334:
	cbz x13, 2335f
2337:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2337b
	b 2336f
2335:
2336:
	b 2329f
2328:
2338:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2338b
2329:
	b 2327f
2326:
2327:
2325:
	b 2323f
2322:
2323:
	add x23, x27, #0
	add x24, x26, #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2339f
	ldr x5, [sp, #8]
	bl {vg_ghash_with_powers_aes}
	b 2340f
2339:
	bl {vg_ghash_aes}
2340:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2341f
	lsr x9, x26, #4
	cbz x9, 2343f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2344f
2343:
	cbz x13, 2345f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2347f
	lsr x14, x13, #2
	cbz x14, 2349f
	lsr x14, x13, #3
	cbz x14, 2351f
2353:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2353b
	b 2352f
2351:
2352:
	lsr x14, x13, #2
	cbz x14, 2354f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2355f
2354:
2355:
	cbz x13, 2356f
2358:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2358b
	b 2357f
2356:
2357:
	b 2350f
2349:
2359:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2359b
2350:
	b 2348f
2347:
2348:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2346f
2345:
2346:
2344:
	b 2342f
2341:
2342:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
2252:
2123:
27:
	add sp, sp, #2592
	ret
	.arch_extension noaes
	.arch_extension nosha3
	.p2align 6

vg_aes_gcm_open_with_powers_aes_sha3:
	.arch_extension aes
	.arch_extension sha3
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	ldr x17, [sp, #2608]
	str x17, [x16, #16]
	add x17, sp, #32
	str x17, [x16, #24]
	ldr x9, [sp, #24]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	add x28, x10, #0
	ldr x12, [sp, #0]
	movz x10, #0, lsl #0
	lsr x9, x5, #4
	cbz x9, 20f
	sub x9, x5, #16
	cbz x9, 22f
	movz x10, #1, lsl #0
	b 23f
22:
23:
	b 21f
20:
21:
	sub x9, x24, #12
	cbz x9, 24f
	movz x10, #1, lsl #0
	b 25f
24:
25:
	cbz x10, 26f
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 28f
	lsr x13, x28, #4
	cbz x13, 210f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 211f
210:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 212f
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
	b 213f
212:
213:
211:
	sub x9, x24, #12
	cbz x9, 215f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash_aes}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	cbz x25, 230f
	movz x3, #1, lsl #0
	b 231f
230:
	movz x3, #0, lsl #0
231:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	b 216f
215:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
216:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 232f
	lsr x14, x13, #2
	cbz x14, 234f
	lsr x14, x13, #3
	cbz x14, 236f
238:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 238b
	b 237f
236:
237:
	lsr x14, x13, #2
	cbz x14, 239f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 240f
239:
240:
	cbz x13, 241f
243:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 243b
	b 242f
241:
242:
	b 235f
234:
244:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 244b
235:
	b 233f
232:
233:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 245f
	cbz x27, 247f
	movz x25, #0, lsl #0
	b 248f
247:
248:
	b 246f
245:
	movz x25, #0, lsl #0
246:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 249f
	lsr x14, x13, #2
	cbz x14, 251f
	lsr x14, x13, #3
	cbz x14, 253f
255:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 255b
	b 254f
253:
254:
	lsr x14, x13, #2
	cbz x14, 256f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 257f
256:
257:
	cbz x13, 258f
260:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 260b
	b 259f
258:
259:
	b 252f
251:
261:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 261b
252:
	b 250f
249:
250:
	cbz x25, 262f
	movz x3, #1, lsl #0
	b 263f
262:
	movz x3, #0, lsl #0
263:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 264f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 266f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 268f
	add x10, x9, #0
	b 269f
268:
	add x10, x24, #0
269:
	b 267f
266:
	add x10, x9, #0
267:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 270f
272:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
	b 271f
270:
271:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 273f
	movz x3, #0, lsl #0
	b 274f
273:
	movz x3, #1, lsl #0
274:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash_aes}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash_aes}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 275f
	lsr x14, x13, #2
	cbz x14, 277f
	lsr x14, x13, #3
	cbz x14, 279f
281:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 281b
	b 280f
279:
280:
	lsr x14, x13, #2
	cbz x14, 282f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 283f
282:
283:
	cbz x13, 284f
286:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 286b
	b 285f
284:
285:
	b 278f
277:
287:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 287b
278:
	b 276f
275:
276:
	b 265f
264:
265:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 288f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 289f
288:
	movz x9, #15, lsl #0
	and x25, x26, x9
289:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 290f
	lsr x14, x13, #2
	cbz x14, 292f
	lsr x14, x13, #3
	cbz x14, 294f
296:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 296b
	b 295f
294:
295:
	lsr x14, x13, #2
	cbz x14, 297f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 298f
297:
298:
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	b 293f
292:
2102:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2102b
293:
	b 291f
290:
291:
	cbz x25, 2103f
	movz x3, #1, lsl #0
	b 2104f
2103:
	movz x3, #0, lsl #0
2104:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash_aes}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 2105f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2106f
2105:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2107f
2109:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2109b
	b 2108f
2107:
2108:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2110f
2112:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2112b
	b 2111f
2110:
2111:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2106:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2113f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2115f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2116f
2115:
	movz x4, #0, lsl #0
2116:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2117f
	lsr x14, x13, #2
	cbz x14, 2119f
	lsr x14, x13, #3
	cbz x14, 2121f
2123:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2123b
	b 2122f
2121:
2122:
	lsr x14, x13, #2
	cbz x14, 2124f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2125f
2124:
2125:
	cbz x13, 2126f
2128:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2128b
	b 2127f
2126:
2127:
	b 2120f
2119:
2129:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2129b
2120:
	b 2118f
2117:
2118:
	b 2114f
2113:
2114:
	add x0, x27, #0
	b 29f
28:
	movz x0, #0, lsl #0
29:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 27f
26:
	add x9, x7, #31
	lsr x9, x9, #7
	cbz x9, 2130f
	add x9, x7, #256
	lsr x9, x9, #10
	cbz x9, 2132f
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2134f
	lsr x13, x28, #4
	cbz x13, 2136f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2137f
2136:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2138f
2140:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2140b
	b 2139f
2138:
2139:
2137:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2141f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2143f
	lsr x14, x13, #2
	cbz x14, 2145f
	lsr x14, x13, #3
	cbz x14, 2147f
2149:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2149b
	b 2148f
2147:
2148:
	lsr x14, x13, #2
	cbz x14, 2150f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2151f
2150:
2151:
	cbz x13, 2152f
2154:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2154b
	b 2153f
2152:
2153:
	b 2146f
2145:
2155:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2155b
2146:
	b 2144f
2143:
2144:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2142f
2141:
2142:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr q0, [x20, #48]
	str q0, [x19, #320]
	lsr x9, x26, #7
	cbz x9, 2156f
	ldr x5, [sp, #16]
	ldr q16, [x5, #16]
	ext v24.16b, v16.16b, v16.16b, #8
	ldr q17, [x5, #0]
	ext v25.16b, v17.16b, v17.16b, #8
	ldr q18, [x5, #48]
	ext v26.16b, v18.16b, v18.16b, #8
	ldr q19, [x5, #32]
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q20, [x5, #80]
	ext v28.16b, v20.16b, v20.16b, #8
	ldr q21, [x5, #64]
	ext v29.16b, v21.16b, v21.16b, #8
	ldr q22, [x5, #112]
	ext v30.16b, v22.16b, v22.16b, #8
	ldr q23, [x5, #96]
	ext v31.16b, v23.16b, v23.16b, #8
	str q24, [x19, #512]
	str q25, [x19, #528]
	str q26, [x19, #544]
	str q27, [x19, #560]
	str q28, [x19, #576]
	str q29, [x19, #592]
	str q30, [x19, #608]
	str q31, [x19, #624]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #672]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #688]
	ldr w10, [x20, #60]
	rev w10, w10
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x20, #16]
	rev64 v16.16b, v16.16b
	add x9, x23, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 2158f
	cbz x14, 2160f
2162:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	ldr q0, [x20, #48]
	rev64 v21.16b, v21.16b
	mov v0.s[3], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	rev w12, w12
	ldr q1, [x20, #48]
	rev64 v22.16b, v22.16b
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q23, [x19, #608]
	rev w12, w12
	ldr q2, [x20, #48]
	ldr q24, [x19, #592]
	mov v2.s[3], w12
	add w12, w10, #3
	ldr q25, [x19, #640]
	rev w12, w12
	ldr q3, [x20, #48]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	trn2 v27.2d, v21.2d, v22.2d
	rev w12, w12
	ldr q4, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v4.s[3], w12
	add w12, w10, #5
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull v29.1q, v22.1d, v24.1d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	mov v6.s[3], w12
	add w12, w10, #7
	pmull v27.1q, v26.1d, v25.1d
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #48]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #576]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #560]
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #656]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #80]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #96]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	ldr q23, [x19, #544]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #528]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #672]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #112]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v21.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	ldr q22, [x9, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	rev64 v22.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v22.16b, v22.16b, v16.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q23, [x19, #512]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v26.16b, v26.16b, v27.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #0]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2162b
	b 2161f
2160:
2163:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev w12, w12
	rev64 v22.16b, v22.16b
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	ldr q23, [x19, #608]
	add w12, w10, #2
	rev w12, w12
	ldr q24, [x19, #592]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	ldr q25, [x19, #640]
	add w12, w10, #3
	rev w12, w12
	trn1 v26.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	trn2 v27.2d, v21.2d, v22.2d
	mov v3.s[3], w12
	add w12, w10, #4
	eor v26.16b, v26.16b, v27.16b
	rev w12, w12
	ldr q4, [x20, #48]
	pmull v28.1q, v21.1d, v23.1d
	mov v4.s[3], w12
	add w12, w10, #5
	pmull2 v21.1q, v21.2d, v23.2d
	rev w12, w12
	ldr q5, [x20, #48]
	pmull v29.1q, v22.1d, v24.1d
	mov v5.s[3], w12
	add w12, w10, #6
	pmull2 v22.1q, v22.2d, v24.2d
	rev w12, w12
	ldr q6, [x20, #48]
	pmull v27.1q, v26.1d, v25.1d
	mov v6.s[3], w12
	pmull2 v26.1q, v26.2d, v25.2d
	add w12, w10, #7
	rev w12, w12
	eor v18.16b, v28.16b, v29.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	eor v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #48]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q22, [x9, #64]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #576]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #560]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #656]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q21, [x9, #80]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v21.16b, v21.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	trn2 v27.2d, v21.2d, v22.2d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v26.16b, v26.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #112]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v21.16b, v21.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #0]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	rev64 v22.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	eor v22.16b, v22.16b, v16.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #512]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q24, [x19, #624]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #688]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	trn2 v27.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v26.16b, v26.16b, v27.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x21, #176]
	pmull2 v22.1q, v22.2d, v24.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #0]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	pmull v26.1q, v20.1d, v17.1d
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2163b
2161:
	b 2159f
2158:
2164:
	add w12, w10, #0
	ldr q21, [x9, #16]
	rev w12, w12
	rev64 v21.16b, v21.16b
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	rev64 v22.16b, v22.16b
	rev w12, w12
	ldr q1, [x20, #48]
	ldr q23, [x19, #608]
	mov v1.s[3], w12
	add w12, w10, #2
	ldr q24, [x19, #592]
	rev w12, w12
	ldr q25, [x19, #640]
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	trn1 v26.2d, v21.2d, v22.2d
	add w12, w10, #3
	rev w12, w12
	trn2 v27.2d, v21.2d, v22.2d
	ldr q3, [x20, #48]
	eor v26.16b, v26.16b, v27.16b
	mov v3.s[3], w12
	add w12, w10, #4
	pmull v28.1q, v21.1d, v23.1d
	rev w12, w12
	ldr q4, [x20, #48]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v4.s[3], w12
	pmull v29.1q, v22.1d, v24.1d
	add w12, w10, #5
	rev w12, w12
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	pmull v27.1q, v26.1d, v25.1d
	add w12, w10, #6
	pmull2 v26.1q, v26.2d, v25.2d
	rev w12, w12
	ldr q6, [x20, #48]
	eor v18.16b, v28.16b, v29.16b
	mov v6.s[3], w12
	add w12, w10, #7
	eor v19.16b, v21.16b, v22.16b
	rev w12, w12
	eor v20.16b, v27.16b, v26.16b
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q21, [x9, #48]
	ldr q30, [x21, #0]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #64]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	rev64 v22.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #576]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q24, [x19, #560]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	ldr q25, [x19, #656]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v26.16b, v26.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #80]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	rev64 v21.16b, v21.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #96]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	rev64 v22.16b, v22.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q23, [x19, #544]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #528]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #672]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v27.1q, v26.1d, v25.1d
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #112]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	rev64 v21.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #0]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	rev64 v22.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v22.16b, v22.16b, v16.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q23, [x19, #512]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q24, [x19, #624]
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q25, [x19, #688]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v26.16b, v26.16b, v27.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v28.1q, v21.1d, v23.1d
	ldr q30, [x21, #144]
	pmull2 v21.1q, v21.2d, v23.2d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #0]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #64]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	pmull v26.1q, v20.1d, v17.1d
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	ext v18.16b, v18.16b, v18.16b, #8
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 2164b
2159:
	rev64 v16.16b, v16.16b
	str q16, [x20, #16]
	rev w12, w10
	str w12, [x20, #60]
	b 2157f
2156:
2157:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x23, x23, x9
	sub x24, x26, x9
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2165f
	ldr x5, [sp, #16]
	bl {vg_ghash_with_powers_aes}
	b 2166f
2165:
	bl {vg_ghash_aes}
2166:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2167f
	lsr x9, x26, #4
	cbz x9, 2169f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2170f
2169:
	cbz x13, 2171f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2173f
	lsr x14, x13, #2
	cbz x14, 2175f
	lsr x14, x13, #3
	cbz x14, 2177f
2179:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2179b
	b 2178f
2177:
2178:
	lsr x14, x13, #2
	cbz x14, 2180f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2181f
2180:
2181:
	cbz x13, 2182f
2184:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2184b
	b 2183f
2182:
2183:
	b 2176f
2175:
2185:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2185b
2176:
	b 2174f
2173:
2174:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2172f
2171:
2172:
2170:
	b 2168f
2167:
2168:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 2186f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2187f
2186:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2188f
2190:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2190b
	b 2189f
2188:
2189:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2191f
2193:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2193b
	b 2192f
2191:
2192:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2187:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2194f
	ldr x23, [x19, #232]
	ldr x26, [x19, #240]
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x23, x23, x9
	sub x24, x26, x9
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2196f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2197f
2196:
	movz x4, #0, lsl #0
2197:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2198f
	lsr x9, x26, #4
	cbz x9, 2200f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2201f
2200:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2202f
	lsr x14, x13, #2
	cbz x14, 2204f
	lsr x14, x13, #3
	cbz x14, 2206f
2208:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2208b
	b 2207f
2206:
2207:
	lsr x14, x13, #2
	cbz x14, 2209f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2210f
2209:
2210:
	cbz x13, 2211f
2213:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2213b
	b 2212f
2211:
2212:
	b 2205f
2204:
2214:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2214b
2205:
	b 2203f
2202:
2203:
2201:
	b 2199f
2198:
2199:
	b 2195f
2194:
	ldr q0, [x19, #320]
	str q0, [x20, #48]
	ldr x23, [x19, #232]
	ldr x26, [x19, #240]
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x24, x9, #0
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2215f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2216f
2215:
	movz x4, #0, lsl #0
2216:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2217f
	lsr x9, x26, #4
	cbz x9, 2219f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2220f
2219:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2221f
	lsr x14, x13, #2
	cbz x14, 2223f
	lsr x14, x13, #3
	cbz x14, 2225f
2227:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2227b
	b 2226f
2225:
2226:
	lsr x14, x13, #2
	cbz x14, 2228f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2229f
2228:
2229:
	cbz x13, 2230f
2232:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2232b
	b 2231f
2230:
2231:
	b 2224f
2223:
2233:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2233b
2224:
	b 2222f
2221:
2222:
2220:
	b 2218f
2217:
2218:
2195:
	add x0, x27, #0
	b 2135f
2134:
	movz x0, #0, lsl #0
2135:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 2133f
2132:
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2234f
	lsr x13, x28, #4
	cbz x13, 2236f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2237f
2236:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2238f
2240:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2240b
	b 2239f
2238:
2239:
2237:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2241f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2243f
	lsr x14, x13, #2
	cbz x14, 2245f
	lsr x14, x13, #3
	cbz x14, 2247f
2249:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2249b
	b 2248f
2247:
2248:
	lsr x14, x13, #2
	cbz x14, 2250f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2251f
2250:
2251:
	cbz x13, 2252f
2254:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2254b
	b 2253f
2252:
2253:
	b 2246f
2245:
2255:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2255b
2246:
	b 2244f
2243:
2244:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2242f
2241:
2242:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2256f
	ldr x5, [sp, #16]
	bl {vg_ghash_with_powers_aes}
	b 2257f
2256:
	bl {vg_ghash_aes}
2257:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2258f
	lsr x9, x26, #4
	cbz x9, 2260f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2261f
2260:
	cbz x13, 2262f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2264f
	lsr x14, x13, #2
	cbz x14, 2266f
	lsr x14, x13, #3
	cbz x14, 2268f
2270:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2270b
	b 2269f
2268:
2269:
	lsr x14, x13, #2
	cbz x14, 2271f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2272f
2271:
2272:
	cbz x13, 2273f
2275:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2275b
	b 2274f
2273:
2274:
	b 2267f
2266:
2276:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2276b
2267:
	b 2265f
2264:
2265:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2263f
2262:
2263:
2261:
	b 2259f
2258:
2259:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 2277f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2278f
2277:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2279f
2281:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2281b
	b 2280f
2279:
2280:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2282f
2284:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2284b
	b 2283f
2282:
2283:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2278:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2285f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2287f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2288f
2287:
	movz x4, #0, lsl #0
2288:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2289f
	lsr x9, x26, #4
	cbz x9, 2291f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2292f
2291:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2293f
	lsr x14, x13, #2
	cbz x14, 2295f
	lsr x14, x13, #3
	cbz x14, 2297f
2299:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2299b
	b 2298f
2297:
2298:
	lsr x14, x13, #2
	cbz x14, 2300f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2301f
2300:
2301:
	cbz x13, 2302f
2304:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2304b
	b 2303f
2302:
2303:
	b 2296f
2295:
2305:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2305b
2296:
	b 2294f
2293:
2294:
2292:
	b 2290f
2289:
2290:
	b 2286f
2285:
2286:
	add x0, x27, #0
	b 2235f
2234:
	movz x0, #0, lsl #0
2235:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
2133:
	b 2131f
2130:
	add x9, x7, #15
	lsr x9, x9, #5
	cbz x9, 2306f
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2308f
	lsr x13, x28, #4
	cbz x13, 2310f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2311f
2310:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2312f
2314:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2314b
	b 2313f
2312:
2313:
2311:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x26, x7, #0
	add x27, x6, #0
	add x24, x5, #0
	add x25, x7, #15
	lsr x25, x25, #4
	lsl x25, x25, #4
	ldr x5, [sp, #16]
	ldr q16, [x5, #16]
	ext v24.16b, v16.16b, v16.16b, #8
	ldr q17, [x5, #0]
	ext v25.16b, v17.16b, v17.16b, #8
	ldr q18, [x5, #48]
	ext v26.16b, v18.16b, v18.16b, #8
	ldr q19, [x5, #32]
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q20, [x5, #80]
	ext v28.16b, v20.16b, v20.16b, #8
	ldr q21, [x5, #64]
	ext v29.16b, v21.16b, v21.16b, #8
	ldr q22, [x5, #112]
	ext v30.16b, v22.16b, v22.16b, #8
	ldr q23, [x5, #96]
	ext v31.16b, v23.16b, v23.16b, #8
	str q24, [x19, #512]
	str q25, [x19, #528]
	str q26, [x19, #544]
	str q27, [x19, #560]
	str q28, [x19, #576]
	str q29, [x19, #592]
	str q30, [x19, #608]
	str q31, [x19, #624]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #672]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #688]
	movi v0.2d, #0
	str q0, [x19, #896]
	str q0, [x19, #912]
	str q0, [x19, #928]
	str q0, [x19, #944]
	str q0, [x19, #960]
	str q0, [x19, #976]
	str q0, [x19, #992]
	str q0, [x19, #1008]
	add x9, x19, #864
	sub x9, x9, x25
	str q0, [x9, #0]
	add x11, x19, #880
	sub x11, x11, x25
	add x12, x27, #0
	add x13, x26, #0
	lsr x14, x13, #4
	cbz x14, 2315f
	add x9, x12, x13
	sub x9, x9, #16
	add x10, x11, x13
	sub x10, x10, #16
2317:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2317b
	ldr q0, [x9, #0]
	str q0, [x10, #0]
	b 2316f
2315:
	cbz x13, 2318f
	lsr x14, x13, #2
	cbz x14, 2320f
	lsr x14, x13, #3
	cbz x14, 2322f
2324:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2324b
	b 2323f
2322:
2323:
	lsr x14, x13, #2
	cbz x14, 2325f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2326f
2325:
2326:
	cbz x13, 2327f
2329:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2329b
	b 2328f
2327:
2328:
	b 2321f
2320:
2330:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2330b
2321:
	b 2319f
2318:
2319:
2316:
	add x12, x19, #880
	sub x12, x12, x25
	add x11, x19, #1008
	sub x11, x11, x25
	lsr x14, x25, #4
	cbz x14, 2331f
2333:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2333b
	b 2332f
2331:
2332:
	add x9, x19, #1008
	sub x9, x9, x25
	add x9, x9, x26
	movi v0.2d, #0
	str q0, [x9, #0]
	add x12, x4, #0
	add x11, x19, #992
	sub x11, x11, x25
	add x13, x24, #0
	cbz x13, 2334f
	lsr x14, x13, #2
	cbz x14, 2336f
	lsr x14, x13, #3
	cbz x14, 2338f
2340:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2340b
	b 2339f
2338:
2339:
	lsr x14, x13, #2
	cbz x14, 2341f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2342f
2341:
2342:
	cbz x13, 2343f
2345:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2345b
	b 2344f
2343:
2344:
	b 2337f
2336:
2346:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2346b
2337:
	b 2335f
2334:
2335:
	lsl x9, x24, #3
	rev x9, x9
	str x9, [x19, #1008]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #1016]
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	movi v16.2d, #0
	add x9, x19, #896
	ldr q21, [x9, #16]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #32]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #608]
	ldr q24, [x19, #592]
	ldr q25, [x19, #640]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v28.16b, v29.16b
	eor v19.16b, v21.16b, v22.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #48]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #64]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #656]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #80]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #96]
	rev64 v22.16b, v22.16b
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #672]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	rev64 v21.16b, v21.16b
	ldr q22, [x9, #0]
	rev64 v22.16b, v22.16b
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #512]
	ldr q24, [x19, #624]
	ldr q25, [x19, #688]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	ldr w10, [x20, #60]
	rev w10, w10
	lsr x9, x25, #4
	add w10, w10, w9
	sub w10, w10, #7
	add x9, x19, #768
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 2347f
	cbz x14, 2349f
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #192]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #224]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
	b 2350f
2349:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #160]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #192]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
2350:
	b 2348f
2347:
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x20, #48]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x20, #48]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x20, #48]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x20, #48]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x20, #48]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x20, #48]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x20, #48]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x20, #48]
	mov v7.s[3], w12
	ldr q30, [x21, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x21, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x21, #160]
	ldr q31, [x9, #0]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	ldr q31, [x9, #16]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #32]
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #48]
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #64]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	ldr q31, [x9, #80]
	eor3 v5.16b, v5.16b, v31.16b, v30.16b
	ldr q31, [x9, #96]
	eor3 v6.16b, v6.16b, v31.16b, v30.16b
	ldr q31, [x9, #112]
	eor3 v7.16b, v7.16b, v31.16b, v30.16b
	add w10, w10, #8
	str q0, [x9, #0]
	str q1, [x9, #16]
	str q2, [x9, #32]
	str q3, [x9, #48]
	str q4, [x9, #64]
	str q5, [x9, #80]
	str q6, [x9, #96]
	str q7, [x9, #112]
2348:
	rev64 v16.16b, v16.16b
	add x9, x19, #864
	sub x9, x9, x25
	ldr q0, [x9, #0]
	eor v16.16b, v16.16b, v0.16b
	str q16, [x19, #112]
	lsr x9, x28, #4
	cbz x9, 2351f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2352f
2351:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2353f
2355:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2355b
	b 2354f
2353:
2354:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2356f
2358:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2358b
	b 2357f
2356:
2357:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2352:
	movz x24, #1, lsl #0
	sub x24, x24, x10
	cbz x24, 2359f
	add x12, x19, #880
	sub x12, x12, x25
	add x11, x27, #0
	add x13, x26, #0
	lsr x14, x13, #4
	cbz x14, 2361f
	add x9, x12, x13
	sub x9, x9, #16
	add x10, x11, x13
	sub x10, x10, #16
2363:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 2363b
	ldr q0, [x9, #0]
	str q0, [x10, #0]
	b 2362f
2361:
	cbz x13, 2364f
	lsr x14, x13, #2
	cbz x14, 2366f
	lsr x14, x13, #3
	cbz x14, 2368f
2370:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2370b
	b 2369f
2368:
2369:
	lsr x14, x13, #2
	cbz x14, 2371f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2372f
2371:
2372:
	cbz x13, 2373f
2375:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2375b
	b 2374f
2373:
2374:
	b 2367f
2366:
2376:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2376b
2367:
	b 2365f
2364:
2365:
2362:
	b 2360f
2359:
2360:
	add x0, x24, #0
	b 2309f
2308:
	movz x0, #0, lsl #0
2309:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	b 2307f
2306:
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 2377f
	lsr x13, x28, #4
	cbz x13, 2379f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 2380f
2379:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 2381f
2383:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2383b
	b 2382f
2381:
2382:
2380:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
	add x25, x5, #0
	add x27, x4, #0
	add x23, x6, #0
	add x26, x7, #0
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	add x0, x21, #240
	ldr q6, [x0, #0]
	rev64 v6.16b, v6.16b
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	movz x6, #3, lsl #0
	movz x7, #17920, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	mov v25.d[0], x7
	mov v25.d[1], x6
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	eor v24.16b, v5.16b, v7.16b
	ext v16.16b, v24.16b, v24.16b, #8
	str q16, [x19, #288]
	str q24, [x19, #304]
	movi v0.2d, #0
	add x13, x25, #0
	add x12, x27, #0
	cbz x13, 2384f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2386f
	lsr x14, x13, #2
	cbz x14, 2388f
	lsr x14, x13, #3
	cbz x14, 2390f
2392:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2392b
	b 2391f
2390:
2391:
	lsr x14, x13, #2
	cbz x14, 2393f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2394f
2393:
2394:
	cbz x13, 2395f
2397:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2397b
	b 2396f
2395:
2396:
	b 2389f
2388:
2398:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2398b
2389:
	b 2387f
2386:
2387:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2385f
2384:
2385:
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	add x24, x26, #0
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	lsr x9, x3, #1
	cbz x9, 2399f
	ldr x5, [sp, #16]
	bl {vg_ghash_with_powers_aes}
	b 2400f
2399:
	bl {vg_ghash_aes}
2400:
	ldr q16, [x19, #288]
	ldr q24, [x19, #304]
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x20, #16]
	rev64 v0.16b, v0.16b
	add x13, x24, #0
	add x12, x23, #0
	cbz x13, 2401f
	lsr x9, x26, #4
	cbz x9, 2403f
	movz x9, #16, lsl #0
	sub x9, x9, x13
	dup v6.16b, w9
	adrp x11, {VG_GCM_TAIL_IDX}
	add x11, x11, {VG_GCM_TAIL_IDX}
	ldr q7, [x11, #16]
	add v7.16b, v7.16b, v6.16b
	sub x11, x12, x9
	ldr q6, [x11, #0]
	tbl v6.16b, {v6.16b}, v7.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2404f
2403:
	cbz x13, 2405f
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	cbz x13, 2407f
	lsr x14, x13, #2
	cbz x14, 2409f
	lsr x14, x13, #3
	cbz x14, 2411f
2413:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2413b
	b 2412f
2411:
2412:
	lsr x14, x13, #2
	cbz x14, 2414f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2415f
2414:
2415:
	cbz x13, 2416f
2418:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2418b
	b 2417f
2416:
2417:
	b 2410f
2409:
2419:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2419b
2410:
	b 2408f
2407:
2408:
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	b 2406f
2405:
2406:
2404:
	b 2402f
2401:
2402:
	ldr x10, [x19, #224]
	lsl x9, x10, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	ldr q6, [x19, #96]
	rev64 v6.16b, v6.16b
	eor v6.16b, v6.16b, v0.16b
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
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
	rev64 v0.16b, v0.16b
	str q0, [x20, #16]
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32_aes}
	lsr x9, x28, #4
	cbz x9, 2420f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 2421f
2420:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 2422f
2424:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2424b
	b 2423f
2422:
2423:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2425f
2427:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2427b
	b 2426f
2425:
2426:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
2421:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2428f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32_aes}
	cbz x24, 2430f
	movz x4, #1, lsl #0
	movi v0.2d, #0
	str q0, [x20, #64]
	b 2431f
2430:
	movz x4, #0, lsl #0
2431:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32_aes}
	cbz x24, 2432f
	lsr x9, x26, #4
	cbz x9, 2434f
	movz x9, #16, lsl #0
	sub x9, x9, x24
	dup v1.16b, w9
	adrp x10, {VG_GCM_TAIL_IDX}
	add x10, x10, {VG_GCM_TAIL_IDX}
	ldr q0, [x10, #0]
	sub v0.16b, v0.16b, v1.16b
	ldr q2, [x20, #64]
	tbl v2.16b, {v2.16b}, v0.16b
	sub x10, x23, x9
	ldr q3, [x10, #0]
	eor v3.16b, v3.16b, v2.16b
	str q3, [x10, #0]
	b 2435f
2434:
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2436f
	lsr x14, x13, #2
	cbz x14, 2438f
	lsr x14, x13, #3
	cbz x14, 2440f
2442:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2442b
	b 2441f
2440:
2441:
	lsr x14, x13, #2
	cbz x14, 2443f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2444f
2443:
2444:
	cbz x13, 2445f
2447:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2447b
	b 2446f
2445:
2446:
	b 2439f
2438:
2448:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2448b
2439:
	b 2437f
2436:
2437:
2435:
	b 2433f
2432:
2433:
	b 2429f
2428:
2429:
	add x0, x27, #0
	b 2378f
2377:
	movz x0, #0, lsl #0
2378:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
2307:
2131:
27:
	add sp, sp, #2592
	ret
	.arch_extension noaes
	.arch_extension nosha3
	.p2align 6

vg_aes_gcm_init:
	sub sp, sp, #2560
	add x3, sp, #0
	str x20, [x3, #136]
	str x21, [x3, #144]
	str x22, [x3, #152]
	str x23, [x3, #160]
	str x24, [x3, #168]
	str x25, [x3, #176]
	str x26, [x3, #184]
	str x27, [x3, #192]
	str x28, [x3, #200]
	str x30, [x3, #208]
	str x19, [x3, #128]
	add x19, x3, #0
	add x21, x2, #0
	lsr x22, x1, #2
	add x22, x22, #6
	add x3, x19, #512
	bl {vg_aes_expand_key_scratch}
	movz x9, #0, lsl #0
	str x9, [x21, #240]
	str x9, [x21, #248]
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #96
	add x3, x21, #240
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32}
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_seal:
	sub sp, sp, #2576
	add x16, sp, #0
	ldr x17, [sp, #2576]
	str x17, [x16, #0]
	add x17, sp, #16
	str x17, [x16, #8]
	ldr x9, [sp, #8]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #0]
	str x10, [x19, #248]
	add x28, x10, #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 217f
	lsr x14, x13, #2
	cbz x14, 219f
	lsr x14, x13, #3
	cbz x14, 221f
223:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 223b
	b 222f
221:
222:
	lsr x14, x13, #2
	cbz x14, 224f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 225f
224:
225:
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	b 220f
219:
229:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 229b
220:
	b 218f
217:
218:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 230f
	cbz x27, 232f
	movz x25, #0, lsl #0
	b 233f
232:
233:
	b 231f
230:
	movz x25, #0, lsl #0
231:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 234f
	lsr x14, x13, #2
	cbz x14, 236f
	lsr x14, x13, #3
	cbz x14, 238f
240:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 240b
	b 239f
238:
239:
	lsr x14, x13, #2
	cbz x14, 241f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 242f
241:
242:
	cbz x13, 243f
245:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	b 237f
236:
246:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 246b
237:
	b 235f
234:
235:
	cbz x25, 247f
	movz x3, #1, lsl #0
	b 248f
247:
	movz x3, #0, lsl #0
248:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 249f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 251f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 253f
	add x10, x9, #0
	b 254f
253:
	add x10, x24, #0
254:
	b 252f
251:
	add x10, x9, #0
252:
	b 250f
249:
	movz x10, #0, lsl #0
250:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 255f
257:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 257b
	b 256f
255:
256:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32}
	cbz x24, 258f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 259f
258:
	movz x4, #0, lsl #0
259:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 260f
	lsr x14, x13, #2
	cbz x14, 262f
	lsr x14, x13, #3
	cbz x14, 264f
266:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 266b
	b 265f
264:
265:
	lsr x14, x13, #2
	cbz x14, 267f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 268f
267:
268:
	cbz x13, 269f
271:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 271b
	b 270f
269:
270:
	b 263f
262:
272:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 272b
263:
	b 261f
260:
261:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 273f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 275f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 277f
	add x10, x9, #0
	b 278f
277:
	add x10, x24, #0
278:
	b 276f
275:
	add x10, x9, #0
276:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 279f
281:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 281b
	b 280f
279:
280:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 282f
	movz x3, #0, lsl #0
	b 283f
282:
	movz x3, #1, lsl #0
283:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 284f
	lsr x14, x13, #2
	cbz x14, 286f
	lsr x14, x13, #3
	cbz x14, 288f
290:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 290b
	b 289f
288:
289:
	lsr x14, x13, #2
	cbz x14, 291f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 292f
291:
292:
	cbz x13, 293f
295:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 295b
	b 294f
293:
294:
	b 287f
286:
296:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 296b
287:
	b 285f
284:
285:
	b 274f
273:
274:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	ldr x28, [x19, #248]
	cbz x27, 297f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 298f
297:
	movz x9, #15, lsl #0
	and x25, x26, x9
298:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 299f
	lsr x14, x13, #2
	cbz x14, 2101f
	lsr x14, x13, #3
	cbz x14, 2103f
2105:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2105b
	b 2104f
2103:
2104:
	lsr x14, x13, #2
	cbz x14, 2106f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2107f
2106:
2107:
	cbz x13, 2108f
2110:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2110b
	b 2109f
2108:
2109:
	b 2102f
2101:
2111:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2111b
2102:
	b 2100f
299:
2100:
	cbz x25, 2112f
	movz x3, #1, lsl #0
	b 2113f
2112:
	movz x3, #0, lsl #0
2113:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2576
	ret
	.p2align 6

vg_aes_gcm_open:
	sub sp, sp, #2592
	add x16, sp, #0
	ldr x17, [sp, #2592]
	str x17, [x16, #0]
	ldr x17, [sp, #2600]
	str x17, [x16, #8]
	add x17, sp, #32
	str x17, [x16, #16]
	ldr x9, [sp, #16]
	str x20, [x9, #136]
	str x21, [x9, #144]
	str x22, [x9, #152]
	str x23, [x9, #160]
	str x24, [x9, #168]
	str x25, [x9, #176]
	str x26, [x9, #184]
	str x27, [x9, #192]
	str x28, [x9, #200]
	str x30, [x9, #208]
	str x19, [x9, #128]
	add x19, x9, #0
	add x20, x19, #16
	add x21, x0, #0
	add x22, x1, #0
	str x4, [x19, #216]
	str x5, [x19, #224]
	str x6, [x19, #232]
	str x7, [x19, #240]
	add x23, x2, #0
	add x24, x3, #0
	add x26, x3, #0
	movz x27, #0, lsl #0
	ldr x10, [sp, #8]
	str x10, [x19, #248]
	add x28, x10, #0
	ldr x12, [sp, #0]
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	sub x9, x24, #12
	cbz x9, 27f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 28f
27:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
28:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x23, [x19, #216]
	ldr x24, [x19, #224]
	movz x25, #0, lsl #0
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 224f
	lsr x14, x13, #2
	cbz x14, 226f
	lsr x14, x13, #3
	cbz x14, 228f
230:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 230b
	b 229f
228:
229:
	lsr x14, x13, #2
	cbz x14, 231f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 232f
231:
232:
	cbz x13, 233f
235:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 235b
	b 234f
233:
234:
	b 227f
226:
236:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 236b
227:
	b 225f
224:
225:
	ldr x9, [x19, #224]
	movz x10, #15, lsl #0
	and x25, x9, x10
	ldr x26, [x19, #240]
	movz x27, #0, lsl #0
	ldr x28, [x19, #232]
	cbz x26, 237f
	cbz x27, 239f
	movz x25, #0, lsl #0
	b 240f
239:
240:
	b 238f
237:
	movz x25, #0, lsl #0
238:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 241f
	lsr x14, x13, #2
	cbz x14, 243f
	lsr x14, x13, #3
	cbz x14, 245f
247:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 247b
	b 246f
245:
246:
	lsr x14, x13, #2
	cbz x14, 248f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 249f
248:
249:
	cbz x13, 250f
252:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 252b
	b 251f
250:
251:
	b 244f
243:
253:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 253b
244:
	b 242f
241:
242:
	cbz x25, 254f
	movz x3, #1, lsl #0
	b 255f
254:
	movz x3, #0, lsl #0
255:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 256f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 258f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 260f
	add x10, x9, #0
	b 261f
260:
	add x10, x24, #0
261:
	b 259f
258:
	add x10, x9, #0
259:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 262f
264:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 264b
	b 263f
262:
263:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 265f
	movz x3, #0, lsl #0
	b 266f
265:
	movz x3, #1, lsl #0
266:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 267f
	lsr x14, x13, #2
	cbz x14, 269f
	lsr x14, x13, #3
	cbz x14, 271f
273:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 273b
	b 272f
271:
272:
	lsr x14, x13, #2
	cbz x14, 274f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 275f
274:
275:
	cbz x13, 276f
278:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 278b
	b 277f
276:
277:
	b 270f
269:
279:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 279b
270:
	b 268f
267:
268:
	b 257f
256:
257:
	ldr x26, [x19, #224]
	ldr x27, [x19, #240]
	cbz x27, 280f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 281f
280:
	movz x9, #15, lsl #0
	and x25, x26, x9
281:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 282f
	lsr x14, x13, #2
	cbz x14, 284f
	lsr x14, x13, #3
	cbz x14, 286f
288:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 288b
	b 287f
286:
287:
	lsr x14, x13, #2
	cbz x14, 289f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 290f
289:
290:
	cbz x13, 291f
293:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 293b
	b 292f
291:
292:
	b 285f
284:
294:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 294b
285:
	b 283f
282:
283:
	cbz x25, 295f
	movz x3, #1, lsl #0
	b 296f
295:
	movz x3, #0, lsl #0
296:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32}
	ldr x28, [x19, #248]
	lsr x9, x28, #4
	cbz x9, 297f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 298f
297:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 299f
2101:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2101b
	b 2100f
299:
2100:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 2102f
2104:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2104b
	b 2103f
2102:
2103:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
298:
	movz x27, #1, lsl #0
	sub x27, x27, x10
	cbz x27, 2105f
	ldr x23, [x19, #232]
	ldr x24, [x19, #240]
	movz x25, #0, lsl #0
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32}
	cbz x24, 2107f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 2108f
2107:
	movz x4, #0, lsl #0
2108:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 2109f
	lsr x14, x13, #2
	cbz x14, 2111f
	lsr x14, x13, #3
	cbz x14, 2113f
2115:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 2115b
	b 2114f
2113:
2114:
	lsr x14, x13, #2
	cbz x14, 2116f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 2117f
2116:
2117:
	cbz x13, 2118f
2120:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2120b
	b 2119f
2118:
2119:
	b 2112f
2111:
2121:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 2121b
2112:
	b 2110f
2109:
2110:
	b 2106f
2105:
2106:
	add x0, x27, #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2592
	ret
	.p2align 6

vg_aes_gcm_stream_init:
	sub sp, sp, #2560
	add x4, sp, #0
	str x20, [x4, #136]
	str x21, [x4, #144]
	str x22, [x4, #152]
	str x23, [x4, #160]
	str x24, [x4, #168]
	str x25, [x4, #176]
	str x26, [x4, #184]
	str x27, [x4, #192]
	str x28, [x4, #200]
	str x30, [x4, #208]
	str x19, [x4, #128]
	add x19, x4, #0
	add x20, x3, #0
	add x21, x0, #0
	add x23, x1, #0
	add x24, x2, #0
	add x26, x2, #0
	movz x27, #0, lsl #0
	sub x9, x24, #12
	cbz x9, 20f
	movz x9, #0, lsl #0
	str x9, [x20, #0]
	str x9, [x20, #8]
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	movz x10, #15, lsl #0
	and x25, x24, x10
	bl {vg_ghash}
	add x12, x23, #0
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #0
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	b 21f
20:
	ldr w9, [x23, #0]
	ldr w10, [x23, #4]
	ldr w11, [x23, #8]
	movz w12, #256, lsl #16
	str w9, [x20, #0]
	str w10, [x20, #4]
	str w11, [x20, #8]
	str w12, [x20, #12]
21:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	ldr w12, [x20, #12]
	rev w12, w12
	add w12, w12, #1
	rev w12, w12
	str w9, [x20, #48]
	str w10, [x20, #52]
	str w11, [x20, #56]
	str w12, [x20, #60]
	movz x9, #0, lsl #0
	str x9, [x20, #16]
	str x9, [x20, #24]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_stream_aad:
	sub sp, sp, #2560
	add x5, sp, #0
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	str x30, [x5, #208]
	str x19, [x5, #128]
	add x19, x5, #0
	add x20, x1, #0
	add x21, x0, #0
	add x23, x3, #0
	add x24, x4, #0
	movz x9, #15, lsl #0
	and x25, x2, x9
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 20f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 22f
	add x10, x9, #0
	b 23f
22:
	add x10, x24, #0
23:
	b 21f
20:
	add x10, x9, #0
21:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 27f
	movz x3, #0, lsl #0
	b 28f
27:
	movz x3, #1, lsl #0
28:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_stream_encrypt:
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x6, #0
	add x27, x4, #0
	add x28, x5, #0
	movz x9, #15, lsl #0
	and x25, x3, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	b 220f
219:
	movz x10, #0, lsl #0
220:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32}
	cbz x24, 228f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 229f
228:
	movz x4, #0, lsl #0
229:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 252f
	movz x3, #0, lsl #0
	b 253f
252:
	movz x3, #1, lsl #0
253:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	b 244f
243:
244:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_stream_decrypt:
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x6, #0
	add x27, x4, #0
	add x28, x5, #0
	movz x9, #15, lsl #0
	and x25, x3, x9
	cbz x26, 20f
	cbz x27, 22f
	movz x25, #0, lsl #0
	b 23f
22:
23:
	b 21f
20:
	movz x25, #0, lsl #0
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 24f
	lsr x14, x13, #2
	cbz x14, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
216:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 216b
27:
	b 25f
24:
25:
	cbz x25, 217f
	movz x3, #1, lsl #0
	b 218f
217:
	movz x3, #0, lsl #0
218:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	movz x9, #15, lsl #0
	and x25, x27, x9
	add x23, x28, #0
	add x24, x26, #0
	cbz x26, 219f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 221f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 223f
	add x10, x9, #0
	b 224f
223:
	add x10, x24, #0
224:
	b 222f
221:
	add x10, x9, #0
222:
	add x11, x20, x25
	add x11, x11, #32
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 225f
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	b 226f
225:
226:
	add x23, x23, x10
	sub x24, x24, x10
	add x9, x25, x10
	sub x9, x9, #16
	cbz x9, 228f
	movz x3, #0, lsl #0
	b 229f
228:
	movz x3, #1, lsl #0
229:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x20, #32
	bl {vg_ghash}
	lsr x3, x24, #4
	add x2, x23, #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	lsl x9, x3, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_ghash}
	add x11, x20, #32
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 230f
	lsr x14, x13, #2
	cbz x14, 232f
	lsr x14, x13, #3
	cbz x14, 234f
236:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 236b
	b 235f
234:
235:
	lsr x14, x13, #2
	cbz x14, 237f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 238f
237:
238:
	cbz x13, 239f
241:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 241b
	b 240f
239:
240:
	b 233f
232:
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
233:
	b 231f
230:
231:
	b 220f
219:
220:
	add x23, x28, #0
	add x24, x26, #0
	cbz x25, 243f
	movz x9, #16, lsl #0
	sub x9, x9, x25
	lsr x10, x24, #4
	cbnz x10, 245f
	sub x11, x9, x24
	lsr x11, x11, #63
	cbz x11, 247f
	add x10, x9, #0
	b 248f
247:
	add x10, x24, #0
248:
	b 246f
245:
	add x10, x9, #0
246:
	b 244f
243:
	movz x10, #0, lsl #0
244:
	add x11, x20, x25
	add x11, x11, #64
	add x12, x23, #0
	add x13, x10, #0
	cbz x13, 249f
251:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 251b
	b 250f
249:
250:
	add x23, x23, x10
	sub x24, x24, x10
	lsr x4, x24, #4
	add x3, x23, #0
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	lsl x9, x4, #4
	add x23, x23, x9
	sub x24, x24, x9
	bl {vg_aes_ctr32}
	cbz x24, 252f
	movz x4, #1, lsl #0
	movz x9, #0, lsl #0
	str x9, [x20, #64]
	str x9, [x20, #72]
	b 253f
252:
	movz x4, #0, lsl #0
253:
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #48
	add x5, x19, #512
	add x3, x20, #64
	bl {vg_aes_ctr32}
	add x11, x20, #64
	add x12, x23, #0
	add x13, x24, #0
	cbz x13, 254f
	lsr x14, x13, #2
	cbz x14, 256f
	lsr x14, x13, #3
	cbz x14, 258f
260:
	ldr x14, [x12, #0]
	ldr x15, [x11, #0]
	eor x14, x14, x15
	str x14, [x12, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 260b
	b 259f
258:
259:
	lsr x14, x13, #2
	cbz x14, 261f
	ldr w14, [x12, #0]
	ldr w15, [x11, #0]
	eor w14, w14, w15
	str w14, [x12, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 262f
261:
262:
	cbz x13, 263f
265:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 265b
	b 264f
263:
264:
	b 257f
256:
266:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 266b
257:
	b 255f
254:
255:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_stream_finish:
	sub sp, sp, #2560
	add x6, sp, #0
	str x20, [x6, #136]
	str x21, [x6, #144]
	str x22, [x6, #152]
	str x23, [x6, #160]
	str x24, [x6, #168]
	str x25, [x6, #176]
	str x26, [x6, #184]
	str x27, [x6, #192]
	str x28, [x6, #200]
	str x30, [x6, #208]
	str x19, [x6, #128]
	add x19, x6, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x5, #0
	cbz x27, 20f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 21f
20:
	movz x9, #15, lsl #0
	and x25, x26, x9
21:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 22f
	lsr x14, x13, #2
	cbz x14, 24f
	lsr x14, x13, #3
	cbz x14, 26f
28:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 28b
	b 27f
26:
27:
	lsr x14, x13, #2
	cbz x14, 29f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 210f
29:
210:
	cbz x13, 211f
213:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 213b
	b 212f
211:
212:
	b 25f
24:
214:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 214b
25:
	b 23f
22:
23:
	cbz x25, 215f
	movz x3, #1, lsl #0
	b 216f
215:
	movz x3, #0, lsl #0
216:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #0]
	ldr x9, [x20, #24]
	str x9, [x19, #8]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #0
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32}
	ldr x9, [x19, #0]
	str x9, [x28, #0]
	ldr x9, [x19, #8]
	str x9, [x28, #8]
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_stream_verify:
	sub sp, sp, #2560
	add x7, sp, #0
	str x20, [x7, #136]
	str x21, [x7, #144]
	str x22, [x7, #152]
	str x23, [x7, #160]
	str x24, [x7, #168]
	str x25, [x7, #176]
	str x26, [x7, #184]
	str x27, [x7, #192]
	str x28, [x7, #200]
	str x30, [x7, #208]
	str x19, [x7, #128]
	add x19, x7, #0
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x26, x3, #0
	add x27, x4, #0
	add x28, x6, #0
	add x12, x5, #0
	sub x10, x28, #4
	movz x9, #13, lsl #0
	subs x10, x10, x9
	movz x9, #0, lsl #0
	movz x10, #1, lsl #0
	csel x9, x9, x10, hs
	cbz x9, 20f
	lsr x13, x28, #4
	cbz x13, 22f
	ldr q0, [x12, #0]
	str q0, [x19, #0]
	b 23f
22:
	add x11, x19, #0
	add x13, x28, #0
	cbz x13, 24f
26:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
23:
	cbz x27, 27f
	movz x9, #15, lsl #0
	and x25, x27, x9
	b 28f
27:
	movz x9, #15, lsl #0
	and x25, x26, x9
28:
	add x12, x20, #32
	movz x9, #0, lsl #0
	str x9, [x19, #96]
	str x9, [x19, #104]
	add x11, x19, #96
	add x13, x25, #0
	cbz x13, 29f
	lsr x14, x13, #2
	cbz x14, 211f
	lsr x14, x13, #3
	cbz x14, 213f
215:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 215b
	b 214f
213:
214:
	lsr x14, x13, #2
	cbz x14, 216f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 217f
216:
217:
	cbz x13, 218f
220:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 220b
	b 219f
218:
219:
	b 212f
211:
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
212:
	b 210f
29:
210:
	cbz x25, 222f
	movz x3, #1, lsl #0
	b 223f
222:
	movz x3, #0, lsl #0
223:
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	lsl x9, x26, #3
	rev x9, x9
	str x9, [x19, #96]
	lsl x9, x27, #3
	rev x9, x9
	str x9, [x19, #104]
	movz x3, #1, lsl #0
	add x0, x21, #240
	add x1, x20, #16
	add x4, x19, #512
	add x2, x19, #96
	bl {vg_ghash}
	ldr x9, [x20, #16]
	str x9, [x19, #112]
	ldr x9, [x20, #24]
	str x9, [x19, #120]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x20, #0
	add x3, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #512
	bl {vg_aes_ctr32}
	lsr x9, x28, #4
	cbz x9, 224f
	ldr x9, [x19, #112]
	ldr x10, [x19, #0]
	eor x9, x9, x10
	ldr x10, [x19, #120]
	ldr x11, [x19, #8]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	b 225f
224:
	movz x9, #0, lsl #0
	str x9, [x19, #256]
	str x9, [x19, #264]
	str x9, [x19, #272]
	str x9, [x19, #280]
	add x11, x19, #272
	add x12, x19, #0
	add x13, x28, #0
	cbz x13, 226f
228:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 228b
	b 227f
226:
227:
	add x11, x19, #256
	add x12, x19, #112
	add x13, x28, #0
	cbz x13, 229f
231:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 231b
	b 230f
229:
230:
	ldr x9, [x19, #256]
	ldr x10, [x19, #272]
	eor x9, x9, x10
	ldr x10, [x19, #264]
	ldr x11, [x19, #280]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
225:
	movz x0, #1, lsl #0
	sub x0, x0, x10
	b 21f
20:
	movz x0, #0, lsl #0
21:
	ldr x20, [x19, #136]
	ldr x21, [x19, #144]
	ldr x22, [x19, #152]
	ldr x23, [x19, #160]
	ldr x24, [x19, #168]
	ldr x25, [x19, #176]
	ldr x26, [x19, #184]
	ldr x27, [x19, #192]
	ldr x28, [x19, #200]
	ldr x30, [x19, #208]
	ldr x19, [x19, #128]
	add sp, sp, #2560
	ret
	.p2align 6

vg_aes_gcm_seal_gather:
	sub sp, sp, #16
	add x16, sp, #0
	str x30, [x16, #8]
	ldr x17, [sp, #32]
	str x17, [x16, #0]
	ldr x11, [sp, #16]
	cbz x7, 20f
22:
	ldr x12, [x6, #0]
	ldr x13, [x6, #8]
	add x6, x6, #16
	lsr x14, x13, #4
	cbz x14, 23f
25:
	ldr q0, [x12, #0]
	str q0, [x11, #0]
	add x12, x12, #16
	add x11, x11, #16
	sub x14, x14, #1
	cbnz x14, 25b
	b 24f
23:
24:
	movz x15, #15, lsl #0
	and x13, x13, x15
	cbz x13, 26f
	lsr x14, x13, #3
	cbz x14, 28f
210:
	ldr x14, [x12, #0]
	str x14, [x11, #0]
	add x12, x12, #8
	add x11, x11, #8
	sub x13, x13, #8
	lsr x14, x13, #3
	cbnz x14, 210b
	b 29f
28:
29:
	lsr x14, x13, #2
	cbz x14, 211f
	ldr w14, [x12, #0]
	str w14, [x11, #0]
	add x12, x12, #4
	add x11, x11, #4
	sub x13, x13, #4
	b 212f
211:
212:
	cbz x13, 213f
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	b 214f
213:
214:
	b 27f
26:
27:
	sub x7, x7, #1
	cbnz x7, 22b
	b 21f
20:
21:
	ldr x6, [sp, #16]
	ldr x7, [sp, #24]
	bl {vg_aes_gcm_seal}
	ldr x30, [sp, #8]
	add sp, sp, #16
	ret
	.p2align 6
