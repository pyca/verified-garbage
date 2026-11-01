// The functions of `src/internal/vg_ghash_with_powers_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash_with_powers_aes:
	.arch_extension aes
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
	movz x5, #49664, lsl #48
	dup v1.2d, x5
	ldr q0, [x1, #0]
	rev64 v0.16b, v0.16b
	lsr x5, x3, #3
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
	ret
	.arch_extension noaes
	.p2align 6
