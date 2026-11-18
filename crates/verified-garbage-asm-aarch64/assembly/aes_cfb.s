// The functions of `src/aes_cfb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_encrypt_aes:
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
22:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x22, #0]
	str x9, [x21, #0]
	ldr x9, [x22, #8]
	str x9, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x13, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	ret
	.p2align 6

vg_aes_cfb128_decrypt_aes:
	add x11, x2, #0
	add x2, x3, #0
	add x3, x4, #0
	add x4, x5, #0
	ldr q31, [x11, #0]
	ldr q16, [x0, #0]
	ldr q17, [x0, #16]
	ldr q18, [x0, #32]
	ldr q19, [x0, #48]
	ldr q20, [x0, #64]
	ldr q21, [x0, #80]
	ldr q22, [x0, #96]
	ldr q23, [x0, #112]
	ldr q24, [x0, #128]
	ldr q25, [x0, #144]
	ldr q26, [x0, #160]
	ldr q27, [x0, #176]
	ldr q28, [x0, #192]
	lsl x9, x1, #4
	add x9, x0, x9
	ldr q30, [x9, #0]
	sub x6, x1, #10
	sub x7, x1, #12
	lsr x13, x3, #3
	sub x9, x9, #16
	ldr q29, [x9, #0]
	sub x9, x3, #8
	lsr x13, x9, #63
	cbnz x13, 20f
	.p2align 4
22:
	orr v0.16b, v31.16b, v31.16b
	ldr q1, [x2, #0]
	ldr q2, [x2, #16]
	ldr q3, [x2, #32]
	ldr q4, [x2, #48]
	ldr q5, [x2, #64]
	ldr q6, [x2, #80]
	ldr q7, [x2, #96]
	aese v0.16b, v16.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v16.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v16.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v16.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v16.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v16.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v16.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v16.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v17.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v17.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v17.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v17.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v17.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v17.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v17.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v18.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v18.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v18.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v18.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v18.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v18.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v18.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v19.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v19.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v19.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v19.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v19.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v19.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v19.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v20.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v20.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v20.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v20.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v20.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v20.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v20.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v21.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v21.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v21.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v21.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v21.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v21.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v21.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v22.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v22.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v22.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v22.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v22.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v22.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v22.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v23.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v23.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v23.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v23.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v23.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v23.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v23.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v24.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v24.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v24.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v24.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v24.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v24.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v24.16b
	aesmc v7.16b, v7.16b
	cbz x6, 23f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v25.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v25.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v25.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v25.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v25.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v25.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v25.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v26.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v26.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v26.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v26.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v26.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v26.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v26.16b
	aesmc v7.16b, v7.16b
	cbz x7, 25f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v27.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v27.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v27.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v27.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v27.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v27.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v27.16b
	aesmc v7.16b, v7.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v28.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v28.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v28.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v28.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v28.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v28.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v28.16b
	aesmc v7.16b, v7.16b
	b 26f
25:
26:
	b 24f
23:
24:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	aese v1.16b, v29.16b
	eor v1.16b, v1.16b, v30.16b
	aese v2.16b, v29.16b
	eor v2.16b, v2.16b, v30.16b
	aese v3.16b, v29.16b
	eor v3.16b, v3.16b, v30.16b
	aese v4.16b, v29.16b
	eor v4.16b, v4.16b, v30.16b
	aese v5.16b, v29.16b
	eor v5.16b, v5.16b, v30.16b
	aese v6.16b, v29.16b
	eor v6.16b, v6.16b, v30.16b
	aese v7.16b, v29.16b
	eor v7.16b, v7.16b, v30.16b
	ldr q31, [x2, #0]
	eor v0.16b, v0.16b, v31.16b
	str q0, [x2, #0]
	ldr q31, [x2, #16]
	eor v1.16b, v1.16b, v31.16b
	str q1, [x2, #16]
	ldr q31, [x2, #32]
	eor v2.16b, v2.16b, v31.16b
	str q2, [x2, #32]
	ldr q31, [x2, #48]
	eor v3.16b, v3.16b, v31.16b
	str q3, [x2, #48]
	ldr q31, [x2, #64]
	eor v4.16b, v4.16b, v31.16b
	str q4, [x2, #64]
	ldr q31, [x2, #80]
	eor v5.16b, v5.16b, v31.16b
	str q5, [x2, #80]
	ldr q31, [x2, #96]
	eor v6.16b, v6.16b, v31.16b
	str q6, [x2, #96]
	ldr q31, [x2, #112]
	eor v7.16b, v7.16b, v31.16b
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	sub x9, x3, #8
	lsr x13, x9, #63
	cbz x13, 22b
	b 21f
20:
21:
	sub x9, x3, #4
	lsr x13, x9, #63
	cbnz x13, 27f
	orr v0.16b, v31.16b, v31.16b
	ldr q1, [x2, #0]
	ldr q2, [x2, #16]
	ldr q3, [x2, #32]
	aese v0.16b, v16.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v16.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v16.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v16.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v17.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v17.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v17.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v18.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v18.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v18.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v19.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v19.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v19.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v20.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v20.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v20.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v21.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v21.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v21.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v22.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v22.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v22.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v23.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v23.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v23.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v24.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v24.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v24.16b
	aesmc v3.16b, v3.16b
	cbz x6, 29f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v25.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v25.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v25.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v26.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v26.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v26.16b
	aesmc v3.16b, v3.16b
	cbz x7, 211f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v27.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v27.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v27.16b
	aesmc v3.16b, v3.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v28.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v28.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v28.16b
	aesmc v3.16b, v3.16b
	b 212f
211:
212:
	b 210f
29:
210:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	aese v1.16b, v29.16b
	eor v1.16b, v1.16b, v30.16b
	aese v2.16b, v29.16b
	eor v2.16b, v2.16b, v30.16b
	aese v3.16b, v29.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x2, #0]
	eor v0.16b, v0.16b, v31.16b
	str q0, [x2, #0]
	ldr q31, [x2, #16]
	eor v1.16b, v1.16b, v31.16b
	str q1, [x2, #16]
	ldr q31, [x2, #32]
	eor v2.16b, v2.16b, v31.16b
	str q2, [x2, #32]
	ldr q31, [x2, #48]
	eor v3.16b, v3.16b, v31.16b
	str q3, [x2, #48]
	add x2, x2, #64
	sub x3, x3, #4
	b 28f
27:
28:
	cbz x3, 213f
215:
	orr v0.16b, v31.16b, v31.16b
	aese v0.16b, v16.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v17.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v18.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v19.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v20.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v21.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v22.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v23.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v24.16b
	aesmc v0.16b, v0.16b
	cbz x6, 216f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	cbz x7, 218f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	b 219f
218:
219:
	b 217f
216:
217:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x2, #0]
	eor v0.16b, v0.16b, v31.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 215b
	b 214f
213:
214:
	str q31, [x11, #0]
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x11, #0, lsl #0
	movz x13, #0, lsl #0
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

vg_aes_cfb128_encrypt_final_aes:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_encrypt_aes_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x13, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final_aes:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_decrypt_aes_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_aes}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x13, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_cfb128_encrypt_neon:
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
22:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_neon}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x22, #0]
	str x9, [x21, #0]
	ldr x9, [x22, #8]
	str x9, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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

vg_aes_cfb128_decrypt_neon:
	sub x6, x4, #1
	cbz x6, 20f
	cbz x4, 22f
	movz w6, #1, lsl #0
	dup v16.16b, w6
	movz w6, #2, lsl #0
	dup v17.16b, w6
	movz w6, #4, lsl #0
	dup v18.16b, w6
	movz w6, #8, lsl #0
	dup v19.16b, w6
	movz w6, #16, lsl #0
	dup v20.16b, w6
	movz w6, #32, lsl #0
	dup v21.16b, w6
	movz w6, #64, lsl #0
	dup v22.16b, w6
	movz w6, #128, lsl #0
	dup v23.16b, w6
	add x7, x5, #128
	add x8, x1, #1
24:
	ldr q0, [x0, #0]
	and v1.16b, v0.16b, v16.16b
	cmeq v1.16b, v1.16b, v16.16b
	str q1, [x7, #0]
	and v1.16b, v0.16b, v17.16b
	cmeq v1.16b, v1.16b, v17.16b
	str q1, [x7, #16]
	and v1.16b, v0.16b, v18.16b
	cmeq v1.16b, v1.16b, v18.16b
	str q1, [x7, #32]
	and v1.16b, v0.16b, v19.16b
	cmeq v1.16b, v1.16b, v19.16b
	str q1, [x7, #48]
	and v1.16b, v0.16b, v20.16b
	cmeq v1.16b, v1.16b, v20.16b
	str q1, [x7, #64]
	and v1.16b, v0.16b, v21.16b
	cmeq v1.16b, v1.16b, v21.16b
	str q1, [x7, #80]
	and v1.16b, v0.16b, v22.16b
	cmeq v1.16b, v1.16b, v22.16b
	str q1, [x7, #96]
	and v1.16b, v0.16b, v23.16b
	cmeq v1.16b, v1.16b, v23.16b
	str q1, [x7, #112]
	add x0, x0, #16
	add x7, x7, #128
	sub x8, x8, #1
	cbnz x8, 24b
25:
	ldr q0, [x2, #0]
	sub x6, x4, #1
	cbnz x6, 26f
	b 27f
26:
	ldr q1, [x3, #0]
	sub x6, x4, #2
	cbnz x6, 28f
	b 29f
28:
	ldr q2, [x3, #16]
	sub x6, x4, #3
	cbnz x6, 210f
	b 211f
210:
	ldr q3, [x3, #32]
	sub x6, x4, #4
	cbnz x6, 212f
	b 213f
212:
	ldr q4, [x3, #48]
	sub x6, x4, #5
	cbnz x6, 214f
	b 215f
214:
	ldr q5, [x3, #64]
	sub x6, x4, #6
	cbnz x6, 216f
	b 217f
216:
	ldr q6, [x3, #80]
	sub x6, x4, #7
	cbnz x6, 218f
	b 219f
218:
	ldr q7, [x3, #96]
219:
217:
215:
213:
211:
29:
27:
	movz x6, #21845, lsl #0
	movk x6, #21845, lsl #16
	movk x6, #21845, lsl #32
	movk x6, #21845, lsl #48
	dup v29.2d, x6
	movz x6, #13107, lsl #0
	movk x6, #13107, lsl #16
	movk x6, #13107, lsl #32
	movk x6, #13107, lsl #48
	dup v30.2d, x6
	movz x6, #3855, lsl #0
	movk x6, #3855, lsl #16
	movk x6, #3855, lsl #32
	movk x6, #3855, lsl #48
	dup v31.2d, x6
	ushr v24.2d, v0.2d, #1
	eor v24.16b, v24.16b, v1.16b
	and v24.16b, v24.16b, v29.16b
	eor v1.16b, v1.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v2.2d, #1
	eor v24.16b, v24.16b, v3.16b
	and v24.16b, v24.16b, v29.16b
	eor v3.16b, v3.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v2.16b, v2.16b, v24.16b
	ushr v24.2d, v4.2d, #1
	eor v24.16b, v24.16b, v5.16b
	and v24.16b, v24.16b, v29.16b
	eor v5.16b, v5.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v4.16b, v4.16b, v24.16b
	ushr v24.2d, v6.2d, #1
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v29.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v6.16b, v6.16b, v24.16b
	ushr v24.2d, v0.2d, #2
	eor v24.16b, v24.16b, v2.16b
	and v24.16b, v24.16b, v30.16b
	eor v2.16b, v2.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v1.2d, #2
	eor v24.16b, v24.16b, v3.16b
	and v24.16b, v24.16b, v30.16b
	eor v3.16b, v3.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v1.16b, v1.16b, v24.16b
	ushr v24.2d, v4.2d, #2
	eor v24.16b, v24.16b, v6.16b
	and v24.16b, v24.16b, v30.16b
	eor v6.16b, v6.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v4.16b, v4.16b, v24.16b
	ushr v24.2d, v5.2d, #2
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v30.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v5.16b, v5.16b, v24.16b
	ushr v24.2d, v0.2d, #4
	eor v24.16b, v24.16b, v4.16b
	and v24.16b, v24.16b, v31.16b
	eor v4.16b, v4.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v1.2d, #4
	eor v24.16b, v24.16b, v5.16b
	and v24.16b, v24.16b, v31.16b
	eor v5.16b, v5.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v1.16b, v1.16b, v24.16b
	ushr v24.2d, v2.2d, #4
	eor v24.16b, v24.16b, v6.16b
	and v24.16b, v24.16b, v31.16b
	eor v6.16b, v6.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v2.16b, v2.16b, v24.16b
	ushr v24.2d, v3.2d, #4
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v31.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v3.16b, v3.16b, v24.16b
	add x8, x5, #128
	sub x9, x1, #1
	ldr q24, [x8, #0]
	eor v0.16b, v0.16b, v24.16b
	ldr q24, [x8, #16]
	eor v1.16b, v1.16b, v24.16b
	ldr q24, [x8, #32]
	eor v2.16b, v2.16b, v24.16b
	ldr q24, [x8, #48]
	eor v3.16b, v3.16b, v24.16b
	ldr q24, [x8, #64]
	eor v4.16b, v4.16b, v24.16b
	ldr q24, [x8, #80]
	eor v5.16b, v5.16b, v24.16b
	ldr q24, [x8, #96]
	eor v6.16b, v6.16b, v24.16b
	ldr q24, [x8, #112]
	eor v7.16b, v7.16b, v24.16b
220:
	add x8, x8, #128
	eor v5.16b, v6.16b, v5.16b
	eor v24.16b, v5.16b, v0.16b
	eor v25.16b, v4.16b, v2.16b
	eor v26.16b, v24.16b, v4.16b
	eor v4.16b, v7.16b, v4.16b
	eor v27.16b, v7.16b, v1.16b
	eor v1.16b, v24.16b, v1.16b
	eor v28.16b, v7.16b, v2.16b
	eor v29.16b, v27.16b, v25.16b
	eor v3.16b, v3.16b, v29.16b
	eor v2.16b, v3.16b, v2.16b
	eor v3.16b, v3.16b, v6.16b
	and v6.16b, v1.16b, v24.16b
	eor v30.16b, v2.16b, v0.16b
	eor v31.16b, v3.16b, v4.16b
	eor v16.16b, v24.16b, v7.16b
	eor v17.16b, v1.16b, v28.16b
	and v18.16b, v17.16b, v30.16b
	and v19.16b, v4.16b, v31.16b
	eor v20.16b, v2.16b, v5.16b
	eor v5.16b, v5.16b, v31.16b
	eor v7.16b, v7.16b, v5.16b
	eor v21.16b, v20.16b, v31.16b
	and v22.16b, v28.16b, v20.16b
	eor v22.16b, v22.16b, v19.16b
	eor v23.16b, v0.16b, v31.16b
	str q31, [x5, #0]
	and v31.16b, v25.16b, v21.16b
	eor v31.16b, v31.16b, v19.16b
	and v19.16b, v29.16b, v2.16b
	eor v18.16b, v18.16b, v19.16b
	eor v18.16b, v18.16b, v31.16b
	eor v18.16b, v18.16b, v3.16b
	and v3.16b, v26.16b, v0.16b
	eor v3.16b, v3.16b, v19.16b
	eor v3.16b, v3.16b, v22.16b
	and v19.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v19.16b
	eor v6.16b, v6.16b, v31.16b
	eor v31.16b, v20.16b, v28.16b
	eor v3.16b, v3.16b, v31.16b
	and v31.16b, v16.16b, v23.16b
	eor v31.16b, v31.16b, v19.16b
	eor v31.16b, v31.16b, v22.16b
	eor v31.16b, v31.16b, v7.16b
	eor v7.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v7.16b
	eor v7.16b, v18.16b, v3.16b
	and v18.16b, v18.16b, v6.16b
	eor v22.16b, v31.16b, v18.16b
	eor v18.16b, v3.16b, v18.16b
	and v19.16b, v7.16b, v22.16b
	eor v19.16b, v19.16b, v3.16b
	and v16.16b, v19.16b, v16.16b
	and v23.16b, v19.16b, v23.16b
	eor v3.16b, v6.16b, v31.16b
	and v18.16b, v18.16b, v3.16b
	eor v18.16b, v18.16b, v31.16b
	eor v6.16b, v6.16b, v18.16b
	and v0.16b, v18.16b, v0.16b
	and v26.16b, v18.16b, v26.16b
	eor v3.16b, v22.16b, v18.16b
	and v31.16b, v31.16b, v3.16b
	eor v6.16b, v31.16b, v6.16b
	eor v22.16b, v22.16b, v31.16b
	and v30.16b, v6.16b, v30.16b
	and v22.16b, v19.16b, v22.16b
	eor v7.16b, v7.16b, v22.16b
	and v24.16b, v7.16b, v24.16b
	and v1.16b, v7.16b, v1.16b
	eor v1.16b, v23.16b, v1.16b
	and v17.16b, v6.16b, v17.16b
	eor v23.16b, v0.16b, v23.16b
	eor v26.16b, v17.16b, v26.16b
	eor v22.16b, v7.16b, v6.16b
	eor v6.16b, v18.16b, v6.16b
	eor v18.16b, v19.16b, v18.16b
	eor v19.16b, v19.16b, v7.16b
	and v2.16b, v6.16b, v2.16b
	and v6.16b, v6.16b, v29.16b
	eor v6.16b, v6.16b, v17.16b
	and v28.16b, v22.16b, v28.16b
	and v5.16b, v19.16b, v5.16b
	and v19.16b, v19.16b, v27.16b
	eor v0.16b, v0.16b, v19.16b
	and v4.16b, v18.16b, v4.16b
	ldr q27, [x5, #0]
	and v27.16b, v18.16b, v27.16b
	eor v19.16b, v19.16b, v1.16b
	eor v18.16b, v18.16b, v22.16b
	and v22.16b, v22.16b, v20.16b
	eor v2.16b, v2.16b, v5.16b
	and v21.16b, v18.16b, v21.16b
	and v18.16b, v18.16b, v25.16b
	eor v28.16b, v18.16b, v28.16b
	eor v4.16b, v4.16b, v18.16b
	eor v22.16b, v21.16b, v22.16b
	eor v27.16b, v27.16b, v21.16b
	eor v5.16b, v5.16b, v27.16b
	eor v0.16b, v0.16b, v2.16b
	eor v16.16b, v16.16b, v0.16b
	eor v0.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v0.16b
	not v1.16b, v1.16b
	eor v4.16b, v24.16b, v4.16b
	eor v22.16b, v22.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v24.16b, v24.16b, v5.16b
	eor v16.16b, v16.16b, v22.16b
	eor v17.16b, v19.16b, v22.16b
	not v17.16b, v17.16b
	eor v30.16b, v30.16b, v6.16b
	eor v5.16b, v5.16b, v6.16b
	eor v20.16b, v2.16b, v30.16b
	eor v19.16b, v23.16b, v30.16b
	eor v18.16b, v26.16b, v16.16b
	eor v16.16b, v24.16b, v16.16b
	eor v21.16b, v28.16b, v16.16b
	not v21.16b, v21.16b
	eor v22.16b, v24.16b, v20.16b
	not v22.16b, v22.16b
	mov v23.16b, v5.16b
	mov v16.16b, v1.16b
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v16.16b, {v16.16b}, v25.16b
	tbl v17.16b, {v17.16b}, v25.16b
	tbl v18.16b, {v18.16b}, v25.16b
	tbl v19.16b, {v19.16b}, v25.16b
	tbl v20.16b, {v20.16b}, v25.16b
	tbl v21.16b, {v21.16b}, v25.16b
	tbl v22.16b, {v22.16b}, v25.16b
	tbl v23.16b, {v23.16b}, v25.16b
	movz x6, #513, lsl #0
	movk x6, #3, lsl #16
	movk x6, #1541, lsl #32
	movk x6, #1031, lsl #48
	movz x7, #2569, lsl #0
	movk x7, #2059, lsl #16
	movk x7, #3597, lsl #32
	movk x7, #3087, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v0.16b, {v16.16b}, v25.16b
	eor v16.16b, v16.16b, v0.16b
	tbl v1.16b, {v17.16b}, v25.16b
	eor v17.16b, v17.16b, v1.16b
	tbl v2.16b, {v18.16b}, v25.16b
	eor v18.16b, v18.16b, v2.16b
	tbl v3.16b, {v19.16b}, v25.16b
	eor v19.16b, v19.16b, v3.16b
	tbl v4.16b, {v20.16b}, v25.16b
	eor v20.16b, v20.16b, v4.16b
	tbl v5.16b, {v21.16b}, v25.16b
	eor v21.16b, v21.16b, v5.16b
	tbl v6.16b, {v22.16b}, v25.16b
	eor v22.16b, v22.16b, v6.16b
	tbl v7.16b, {v23.16b}, v25.16b
	eor v23.16b, v23.16b, v7.16b
	eor v0.16b, v0.16b, v23.16b
	rev32 v24.8h, v16.8h
	eor v0.16b, v0.16b, v24.16b
	eor v1.16b, v1.16b, v16.16b
	eor v1.16b, v1.16b, v23.16b
	rev32 v24.8h, v17.8h
	eor v1.16b, v1.16b, v24.16b
	eor v2.16b, v2.16b, v17.16b
	rev32 v24.8h, v18.8h
	eor v2.16b, v2.16b, v24.16b
	eor v3.16b, v3.16b, v18.16b
	eor v3.16b, v3.16b, v23.16b
	rev32 v24.8h, v19.8h
	eor v3.16b, v3.16b, v24.16b
	eor v4.16b, v4.16b, v19.16b
	eor v4.16b, v4.16b, v23.16b
	rev32 v24.8h, v20.8h
	eor v4.16b, v4.16b, v24.16b
	eor v5.16b, v5.16b, v20.16b
	rev32 v24.8h, v21.8h
	eor v5.16b, v5.16b, v24.16b
	eor v6.16b, v6.16b, v21.16b
	rev32 v24.8h, v22.8h
	eor v6.16b, v6.16b, v24.16b
	eor v7.16b, v7.16b, v22.16b
	rev32 v24.8h, v23.8h
	eor v7.16b, v7.16b, v24.16b
	ldr q24, [x8, #0]
	eor v0.16b, v0.16b, v24.16b
	ldr q24, [x8, #16]
	eor v1.16b, v1.16b, v24.16b
	ldr q24, [x8, #32]
	eor v2.16b, v2.16b, v24.16b
	ldr q24, [x8, #48]
	eor v3.16b, v3.16b, v24.16b
	ldr q24, [x8, #64]
	eor v4.16b, v4.16b, v24.16b
	ldr q24, [x8, #80]
	eor v5.16b, v5.16b, v24.16b
	ldr q24, [x8, #96]
	eor v6.16b, v6.16b, v24.16b
	ldr q24, [x8, #112]
	eor v7.16b, v7.16b, v24.16b
	sub x9, x9, #1
	cbnz x9, 220b
	add x8, x8, #128
	eor v5.16b, v6.16b, v5.16b
	eor v24.16b, v5.16b, v0.16b
	eor v25.16b, v4.16b, v2.16b
	eor v26.16b, v24.16b, v4.16b
	eor v4.16b, v7.16b, v4.16b
	eor v27.16b, v7.16b, v1.16b
	eor v1.16b, v24.16b, v1.16b
	eor v28.16b, v7.16b, v2.16b
	eor v29.16b, v27.16b, v25.16b
	eor v3.16b, v3.16b, v29.16b
	eor v2.16b, v3.16b, v2.16b
	eor v3.16b, v3.16b, v6.16b
	and v6.16b, v1.16b, v24.16b
	eor v30.16b, v2.16b, v0.16b
	eor v31.16b, v3.16b, v4.16b
	eor v16.16b, v24.16b, v7.16b
	eor v17.16b, v1.16b, v28.16b
	and v18.16b, v17.16b, v30.16b
	and v19.16b, v4.16b, v31.16b
	eor v20.16b, v2.16b, v5.16b
	eor v5.16b, v5.16b, v31.16b
	eor v7.16b, v7.16b, v5.16b
	eor v21.16b, v20.16b, v31.16b
	and v22.16b, v28.16b, v20.16b
	eor v22.16b, v22.16b, v19.16b
	eor v23.16b, v0.16b, v31.16b
	str q31, [x5, #0]
	and v31.16b, v25.16b, v21.16b
	eor v31.16b, v31.16b, v19.16b
	and v19.16b, v29.16b, v2.16b
	eor v18.16b, v18.16b, v19.16b
	eor v18.16b, v18.16b, v31.16b
	eor v18.16b, v18.16b, v3.16b
	and v3.16b, v26.16b, v0.16b
	eor v3.16b, v3.16b, v19.16b
	eor v3.16b, v3.16b, v22.16b
	and v19.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v19.16b
	eor v6.16b, v6.16b, v31.16b
	eor v31.16b, v20.16b, v28.16b
	eor v3.16b, v3.16b, v31.16b
	and v31.16b, v16.16b, v23.16b
	eor v31.16b, v31.16b, v19.16b
	eor v31.16b, v31.16b, v22.16b
	eor v31.16b, v31.16b, v7.16b
	eor v7.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v7.16b
	eor v7.16b, v18.16b, v3.16b
	and v18.16b, v18.16b, v6.16b
	eor v22.16b, v31.16b, v18.16b
	eor v18.16b, v3.16b, v18.16b
	and v19.16b, v7.16b, v22.16b
	eor v19.16b, v19.16b, v3.16b
	and v16.16b, v19.16b, v16.16b
	and v23.16b, v19.16b, v23.16b
	eor v3.16b, v6.16b, v31.16b
	and v18.16b, v18.16b, v3.16b
	eor v18.16b, v18.16b, v31.16b
	eor v6.16b, v6.16b, v18.16b
	and v0.16b, v18.16b, v0.16b
	and v26.16b, v18.16b, v26.16b
	eor v3.16b, v22.16b, v18.16b
	and v31.16b, v31.16b, v3.16b
	eor v6.16b, v31.16b, v6.16b
	eor v22.16b, v22.16b, v31.16b
	and v30.16b, v6.16b, v30.16b
	and v22.16b, v19.16b, v22.16b
	eor v7.16b, v7.16b, v22.16b
	and v24.16b, v7.16b, v24.16b
	and v1.16b, v7.16b, v1.16b
	eor v1.16b, v23.16b, v1.16b
	and v17.16b, v6.16b, v17.16b
	eor v23.16b, v0.16b, v23.16b
	eor v26.16b, v17.16b, v26.16b
	eor v22.16b, v7.16b, v6.16b
	eor v6.16b, v18.16b, v6.16b
	eor v18.16b, v19.16b, v18.16b
	eor v19.16b, v19.16b, v7.16b
	and v2.16b, v6.16b, v2.16b
	and v6.16b, v6.16b, v29.16b
	eor v6.16b, v6.16b, v17.16b
	and v28.16b, v22.16b, v28.16b
	and v5.16b, v19.16b, v5.16b
	and v19.16b, v19.16b, v27.16b
	eor v0.16b, v0.16b, v19.16b
	and v4.16b, v18.16b, v4.16b
	ldr q27, [x5, #0]
	and v27.16b, v18.16b, v27.16b
	eor v19.16b, v19.16b, v1.16b
	eor v18.16b, v18.16b, v22.16b
	and v22.16b, v22.16b, v20.16b
	eor v2.16b, v2.16b, v5.16b
	and v21.16b, v18.16b, v21.16b
	and v18.16b, v18.16b, v25.16b
	eor v28.16b, v18.16b, v28.16b
	eor v4.16b, v4.16b, v18.16b
	eor v22.16b, v21.16b, v22.16b
	eor v27.16b, v27.16b, v21.16b
	eor v5.16b, v5.16b, v27.16b
	eor v0.16b, v0.16b, v2.16b
	eor v16.16b, v16.16b, v0.16b
	eor v0.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v0.16b
	not v1.16b, v1.16b
	eor v4.16b, v24.16b, v4.16b
	eor v22.16b, v22.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v24.16b, v24.16b, v5.16b
	eor v16.16b, v16.16b, v22.16b
	eor v17.16b, v19.16b, v22.16b
	not v17.16b, v17.16b
	eor v30.16b, v30.16b, v6.16b
	eor v5.16b, v5.16b, v6.16b
	eor v20.16b, v2.16b, v30.16b
	eor v19.16b, v23.16b, v30.16b
	eor v18.16b, v26.16b, v16.16b
	eor v16.16b, v24.16b, v16.16b
	eor v21.16b, v28.16b, v16.16b
	not v21.16b, v21.16b
	eor v22.16b, v24.16b, v20.16b
	not v22.16b, v22.16b
	mov v23.16b, v5.16b
	mov v16.16b, v1.16b
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v16.16b, {v16.16b}, v25.16b
	tbl v17.16b, {v17.16b}, v25.16b
	tbl v18.16b, {v18.16b}, v25.16b
	tbl v19.16b, {v19.16b}, v25.16b
	tbl v20.16b, {v20.16b}, v25.16b
	tbl v21.16b, {v21.16b}, v25.16b
	tbl v22.16b, {v22.16b}, v25.16b
	tbl v23.16b, {v23.16b}, v25.16b
	ldr q24, [x8, #0]
	eor v16.16b, v16.16b, v24.16b
	ldr q24, [x8, #16]
	eor v17.16b, v17.16b, v24.16b
	ldr q24, [x8, #32]
	eor v18.16b, v18.16b, v24.16b
	ldr q24, [x8, #48]
	eor v19.16b, v19.16b, v24.16b
	ldr q24, [x8, #64]
	eor v20.16b, v20.16b, v24.16b
	ldr q24, [x8, #80]
	eor v21.16b, v21.16b, v24.16b
	ldr q24, [x8, #96]
	eor v22.16b, v22.16b, v24.16b
	ldr q24, [x8, #112]
	eor v23.16b, v23.16b, v24.16b
	movz x6, #21845, lsl #0
	movk x6, #21845, lsl #16
	movk x6, #21845, lsl #32
	movk x6, #21845, lsl #48
	dup v29.2d, x6
	movz x6, #13107, lsl #0
	movk x6, #13107, lsl #16
	movk x6, #13107, lsl #32
	movk x6, #13107, lsl #48
	dup v30.2d, x6
	movz x6, #3855, lsl #0
	movk x6, #3855, lsl #16
	movk x6, #3855, lsl #32
	movk x6, #3855, lsl #48
	dup v31.2d, x6
	ushr v24.2d, v16.2d, #1
	eor v24.16b, v24.16b, v17.16b
	and v24.16b, v24.16b, v29.16b
	eor v17.16b, v17.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v18.2d, #1
	eor v24.16b, v24.16b, v19.16b
	and v24.16b, v24.16b, v29.16b
	eor v19.16b, v19.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v18.16b, v18.16b, v24.16b
	ushr v24.2d, v20.2d, #1
	eor v24.16b, v24.16b, v21.16b
	and v24.16b, v24.16b, v29.16b
	eor v21.16b, v21.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v20.16b, v20.16b, v24.16b
	ushr v24.2d, v22.2d, #1
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v29.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v22.16b, v22.16b, v24.16b
	ushr v24.2d, v16.2d, #2
	eor v24.16b, v24.16b, v18.16b
	and v24.16b, v24.16b, v30.16b
	eor v18.16b, v18.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v17.2d, #2
	eor v24.16b, v24.16b, v19.16b
	and v24.16b, v24.16b, v30.16b
	eor v19.16b, v19.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v17.16b, v17.16b, v24.16b
	ushr v24.2d, v20.2d, #2
	eor v24.16b, v24.16b, v22.16b
	and v24.16b, v24.16b, v30.16b
	eor v22.16b, v22.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v20.16b, v20.16b, v24.16b
	ushr v24.2d, v21.2d, #2
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v30.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v21.16b, v21.16b, v24.16b
	ushr v24.2d, v16.2d, #4
	eor v24.16b, v24.16b, v20.16b
	and v24.16b, v24.16b, v31.16b
	eor v20.16b, v20.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v17.2d, #4
	eor v24.16b, v24.16b, v21.16b
	and v24.16b, v24.16b, v31.16b
	eor v21.16b, v21.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v17.16b, v17.16b, v24.16b
	ushr v24.2d, v18.2d, #4
	eor v24.16b, v24.16b, v22.16b
	and v24.16b, v24.16b, v31.16b
	eor v22.16b, v22.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v18.16b, v18.16b, v24.16b
	ushr v24.2d, v19.2d, #4
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v31.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v19.16b, v19.16b, v24.16b
	ldr q31, [x3, #0]
	eor v16.16b, v16.16b, v31.16b
	str q16, [x3, #0]
	sub x6, x4, #1
	cbnz x6, 221f
	b 222f
221:
	ldr q31, [x3, #16]
	eor v17.16b, v17.16b, v31.16b
	str q17, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 223f
	b 224f
223:
	ldr q31, [x3, #32]
	eor v18.16b, v18.16b, v31.16b
	str q18, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 225f
	b 226f
225:
	ldr q31, [x3, #48]
	eor v19.16b, v19.16b, v31.16b
	str q19, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 227f
	b 228f
227:
	ldr q31, [x3, #64]
	eor v20.16b, v20.16b, v31.16b
	str q20, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 229f
	b 230f
229:
	ldr q31, [x3, #80]
	eor v21.16b, v21.16b, v31.16b
	str q21, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 231f
	b 232f
231:
	ldr q31, [x3, #96]
	eor v22.16b, v22.16b, v31.16b
	str q22, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 233f
	b 234f
233:
	ldr q31, [x3, #112]
	eor v23.16b, v23.16b, v31.16b
	str q23, [x3, #112]
234:
232:
230:
228:
226:
224:
222:
	str q31, [x2, #0]
	sub x6, x4, #1
	lsr x6, x6, #3
	cbnz x6, 235f
	movz x4, #0, lsl #0
	b 236f
235:
	add x3, x3, #128
	sub x4, x4, #8
236:
	cbnz x4, 25b
	b 23f
22:
23:
	b 21f
20:
	ldr q0, [x2, #0]
	adrp x6, {VG_AES_VPERM}
	add x6, x6, {VG_AES_VPERM}
	ldr q16, [x6, #0]
	ldr q17, [x6, #16]
	ldr q18, [x6, #32]
	ldr q19, [x6, #48]
	ldr q20, [x6, #64]
	ldr q21, [x6, #80]
	ldr q22, [x6, #96]
	ldr q23, [x6, #112]
	ldr q24, [x6, #128]
	ldr q25, [x6, #144]
	ldr q26, [x6, #160]
	ldr q27, [x6, #176]
	ldr q28, [x6, #192]
	ldr q29, [x6, #208]
	ldr q30, [x6, #224]
	ldr q31, [x6, #240]
	ldr q5, [x0, #0]
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v1.16b, {v27.16b}, v1.16b
	tbl v0.16b, {v28.16b}, v0.16b
	eor v0.16b, v0.16b, v1.16b
	and v6.16b, v5.16b, v16.16b
	ushr v5.16b, v5.16b, #4
	tbl v6.16b, {v27.16b}, v6.16b
	tbl v5.16b, {v28.16b}, v5.16b
	eor v5.16b, v5.16b, v6.16b
	eor v0.16b, v0.16b, v5.16b
	sub x1, x1, #1
237:
	add x0, x0, #16
	ldr q5, [x0, #0]
	and v6.16b, v5.16b, v16.16b
	ushr v5.16b, v5.16b, #4
	tbl v6.16b, {v27.16b}, v6.16b
	tbl v5.16b, {v28.16b}, v5.16b
	eor v5.16b, v5.16b, v6.16b
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v2.16b, {v18.16b}, v1.16b
	eor v1.16b, v1.16b, v0.16b
	tbl v3.16b, {v17.16b}, v0.16b
	tbl v4.16b, {v17.16b}, v1.16b
	eor v3.16b, v3.16b, v2.16b
	eor v4.16b, v4.16b, v2.16b
	tbl v2.16b, {v17.16b}, v3.16b
	tbl v3.16b, {v17.16b}, v4.16b
	eor v2.16b, v2.16b, v1.16b
	eor v3.16b, v3.16b, v0.16b
	tbl v0.16b, {v19.16b}, v2.16b
	tbl v1.16b, {v20.16b}, v3.16b
	tbl v2.16b, {v21.16b}, v2.16b
	tbl v3.16b, {v22.16b}, v3.16b
	eor v0.16b, v0.16b, v1.16b
	eor v2.16b, v2.16b, v3.16b
	tbl v1.16b, {v2.16b}, v23.16b
	tbl v3.16b, {v0.16b}, v24.16b
	tbl v0.16b, {v0.16b}, v25.16b
	eor v1.16b, v1.16b, v3.16b
	eor v0.16b, v0.16b, v5.16b
	tbl v3.16b, {v1.16b}, v26.16b
	eor v0.16b, v0.16b, v1.16b
	eor v0.16b, v0.16b, v3.16b
	sub x1, x1, #1
	cbnz x1, 237b
	ldr q5, [x0, #16]
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v2.16b, {v18.16b}, v1.16b
	eor v1.16b, v1.16b, v0.16b
	tbl v3.16b, {v17.16b}, v0.16b
	tbl v4.16b, {v17.16b}, v1.16b
	eor v3.16b, v3.16b, v2.16b
	eor v4.16b, v4.16b, v2.16b
	tbl v2.16b, {v17.16b}, v3.16b
	tbl v3.16b, {v17.16b}, v4.16b
	eor v2.16b, v2.16b, v1.16b
	eor v3.16b, v3.16b, v0.16b
	tbl v0.16b, {v29.16b}, v2.16b
	tbl v1.16b, {v30.16b}, v3.16b
	eor v0.16b, v0.16b, v1.16b
	tbl v0.16b, {v0.16b}, v23.16b
	eor v5.16b, v5.16b, v31.16b
	eor v0.16b, v0.16b, v5.16b
	ldr q1, [x3, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x3, #0]
	str q1, [x2, #0]
21:
	movz x1, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
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

vg_aes_cfb128_encrypt_final_neon:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_encrypt_neon_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_neon}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final_neon:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_decrypt_neon_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks_neon}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_cfb128_encrypt:
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
22:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x22, #0]
	str x9, [x21, #0]
	ldr x9, [x22, #8]
	str x9, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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

vg_aes_cfb128_decrypt:
	str x19, [x5, #2064]
	str x20, [x5, #2072]
	str x21, [x5, #2080]
	str x22, [x5, #2088]
	str x23, [x5, #2096]
	str x30, [x5, #2104]
	str x24, [x5, #2112]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x22, x3, #0
	add x23, x4, #0
	add x24, x5, #0
	cbz x23, 20f
	sub x9, x23, #4
	lsr x9, x9, #63
	cbnz x9, 22f
24:
	ldr x9, [x22, #0]
	str x9, [x24, #2120]
	ldr x9, [x22, #8]
	str x9, [x24, #2128]
	ldr x9, [x22, #16]
	str x9, [x24, #2136]
	ldr x9, [x22, #24]
	str x9, [x24, #2144]
	ldr x9, [x22, #32]
	str x9, [x24, #2152]
	ldr x9, [x22, #40]
	str x9, [x24, #2160]
	ldr x9, [x22, #48]
	str x9, [x24, #2048]
	ldr x9, [x22, #56]
	str x9, [x24, #2056]
	ldr x9, [x24, #2120]
	str x9, [x22, #16]
	ldr x9, [x24, #2128]
	str x9, [x22, #24]
	ldr x9, [x24, #2136]
	str x9, [x22, #32]
	ldr x9, [x24, #2144]
	str x9, [x22, #40]
	ldr x9, [x24, #2152]
	str x9, [x22, #48]
	ldr x9, [x24, #2160]
	str x9, [x22, #56]
	ldr x9, [x21, #0]
	str x9, [x22, #0]
	ldr x9, [x21, #8]
	str x9, [x22, #8]
	add x0, x19, #0
	add x1, x20, #0
	add x2, x22, #0
	movz x3, #4, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x22, #0]
	ldr x10, [x24, #2120]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x24, #2128]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x22, #16]
	ldr x10, [x24, #2136]
	eor x9, x9, x10
	str x9, [x22, #16]
	ldr x9, [x22, #24]
	ldr x10, [x24, #2144]
	eor x9, x9, x10
	str x9, [x22, #24]
	ldr x9, [x22, #32]
	ldr x10, [x24, #2152]
	eor x9, x9, x10
	str x9, [x22, #32]
	ldr x9, [x22, #40]
	ldr x10, [x24, #2160]
	eor x9, x9, x10
	str x9, [x22, #40]
	ldr x9, [x22, #48]
	ldr x10, [x24, #2048]
	eor x9, x9, x10
	str x9, [x22, #48]
	ldr x9, [x22, #56]
	ldr x10, [x24, #2056]
	eor x9, x9, x10
	str x9, [x22, #56]
	ldr x9, [x24, #2048]
	str x9, [x21, #0]
	ldr x9, [x24, #2056]
	str x9, [x21, #8]
	add x22, x22, #64
	sub x23, x23, #4
	sub x9, x23, #4
	lsr x9, x9, #63
	cbz x9, 24b
	b 23f
22:
23:
	cbz x23, 25f
27:
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	ldr x9, [x22, #0]
	ldr x10, [x21, #0]
	eor x9, x9, x10
	str x9, [x22, #0]
	ldr x9, [x22, #8]
	ldr x10, [x21, #8]
	eor x9, x9, x10
	str x9, [x22, #8]
	ldr x9, [x21, #0]
	ldr x10, [x22, #0]
	eor x9, x9, x10
	str x9, [x21, #0]
	ldr x9, [x21, #8]
	ldr x10, [x22, #8]
	eor x9, x9, x10
	str x9, [x21, #8]
	add x22, x22, #16
	sub x23, x23, #1
	cbnz x23, 27b
	b 26f
25:
26:
	b 21f
20:
21:
	ldr x19, [x24, #2064]
	ldr x20, [x24, #2072]
	ldr x21, [x24, #2080]
	ldr x22, [x24, #2088]
	ldr x23, [x24, #2096]
	ldr x30, [x24, #2104]
	ldr x24, [x24, #2112]
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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

vg_aes_cfb128_encrypt_final:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_encrypt_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6

vg_aes_cfb128_decrypt_final:
	sub sp, sp, #64
	add x6, sp, #0
	str x19, [x6, #0]
	str x20, [x6, #8]
	str x21, [x6, #16]
	str x22, [x6, #24]
	str x23, [x6, #32]
	str x24, [x6, #40]
	str x30, [x6, #48]
	str x25, [x6, #56]
	add x19, x0, #0
	add x20, x1, #0
	add x21, x2, #0
	add x24, x5, #0
	add x25, x6, #0
	lsr x9, x4, #4
	lsl x10, x9, #4
	add x22, x3, x10
	sub x23, x4, x10
	add x4, x9, #0
	bl {vg_aes_cfb128_decrypt_core}
	cbz x23, 20f
	add x0, x19, #0
	add x1, x20, #0
	add x2, x21, #0
	movz x3, #1, lsl #0
	add x4, x24, #0
	bl {vg_aes_encrypt_blocks}
	add x9, x21, #0
22:
	ldrb w6, [x9, #0]
	ldrb w7, [x22, #0]
	eor x7, x7, x6
	strb w7, [x22, #0]
	add x9, x9, #1
	add x22, x22, #1
	sub x23, x23, #1
	cbnz x23, 22b
	b 21f
20:
21:
	ldr x19, [x25, #0]
	ldr x20, [x25, #8]
	ldr x21, [x25, #16]
	ldr x22, [x25, #24]
	ldr x23, [x25, #32]
	ldr x24, [x25, #40]
	ldr x30, [x25, #48]
	ldr x25, [x25, #56]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	add sp, sp, #64
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	sub sp, sp, #64
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add sp, sp, #64
	ret
	.p2align 6
