// The functions of `src/aes_cfb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cfb128_encrypt_aes:
	.arch_extension aes
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
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_cfb128_decrypt_aes:
	.arch_extension aes
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
	ret
	.arch_extension noaes
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
	ret
	.p2align 6
