// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt_aes:
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
	cbz x13, 20f
22:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
	ldr q7, [x2, #112]
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
	str q0, [x2, #0]
	str q1, [x2, #16]
	str q2, [x2, #32]
	str q3, [x2, #48]
	str q4, [x2, #64]
	str q5, [x2, #80]
	str q6, [x2, #96]
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	lsr x13, x3, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x3, 27f
29:
	ldr q0, [x2, #0]
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
	cbz x6, 210f
	aese v0.16b, v25.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v26.16b
	aesmc v0.16b, v0.16b
	cbz x7, 212f
	aese v0.16b, v27.16b
	aesmc v0.16b, v0.16b
	aese v0.16b, v28.16b
	aesmc v0.16b, v0.16b
	b 213f
212:
213:
	b 211f
210:
211:
	aese v0.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	ret
	.p2align 6

vg_aes_ecb_decrypt_aes:
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
	ldr q29, [x0, #208]
	aesimc v17.16b, v17.16b
	aesimc v18.16b, v18.16b
	aesimc v19.16b, v19.16b
	aesimc v20.16b, v20.16b
	aesimc v21.16b, v21.16b
	aesimc v22.16b, v22.16b
	aesimc v23.16b, v23.16b
	aesimc v24.16b, v24.16b
	aesimc v25.16b, v25.16b
	aesimc v26.16b, v26.16b
	aesimc v27.16b, v27.16b
	aesimc v28.16b, v28.16b
	aesimc v29.16b, v29.16b
	cbz x13, 20f
22:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
	ldr q7, [x2, #112]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v30.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v30.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v30.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v30.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v30.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v30.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v30.16b
	aesimc v7.16b, v7.16b
	cbz x6, 23f
	cbz x7, 25f
	aesd v0.16b, v29.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v29.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v29.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v29.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v29.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v29.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v29.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v29.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v28.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v28.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v28.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v28.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v28.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v28.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v28.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v28.16b
	aesimc v7.16b, v7.16b
	b 26f
25:
26:
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v27.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v27.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v27.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v27.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v27.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v27.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v27.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v26.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v26.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v26.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v26.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v26.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v26.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v26.16b
	aesimc v7.16b, v7.16b
	b 24f
23:
24:
	aesd v0.16b, v25.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v25.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v25.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v25.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v25.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v25.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v25.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v25.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v24.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v24.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v24.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v24.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v24.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v24.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v24.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v24.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v23.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v23.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v23.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v23.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v23.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v23.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v23.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v23.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v22.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v22.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v22.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v22.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v22.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v22.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v22.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v22.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v21.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v21.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v21.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v21.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v21.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v21.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v21.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v21.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v20.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v20.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v20.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v20.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v20.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v20.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v20.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v20.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v19.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v19.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v19.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v19.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v19.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v19.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v19.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v19.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v18.16b
	aesimc v0.16b, v0.16b
	aesd v1.16b, v18.16b
	aesimc v1.16b, v1.16b
	aesd v2.16b, v18.16b
	aesimc v2.16b, v2.16b
	aesd v3.16b, v18.16b
	aesimc v3.16b, v3.16b
	aesd v4.16b, v18.16b
	aesimc v4.16b, v4.16b
	aesd v5.16b, v18.16b
	aesimc v5.16b, v5.16b
	aesd v6.16b, v18.16b
	aesimc v6.16b, v6.16b
	aesd v7.16b, v18.16b
	aesimc v7.16b, v7.16b
	aesd v0.16b, v17.16b
	eor v0.16b, v0.16b, v16.16b
	aesd v1.16b, v17.16b
	eor v1.16b, v1.16b, v16.16b
	aesd v2.16b, v17.16b
	eor v2.16b, v2.16b, v16.16b
	aesd v3.16b, v17.16b
	eor v3.16b, v3.16b, v16.16b
	aesd v4.16b, v17.16b
	eor v4.16b, v4.16b, v16.16b
	aesd v5.16b, v17.16b
	eor v5.16b, v5.16b, v16.16b
	aesd v6.16b, v17.16b
	eor v6.16b, v6.16b, v16.16b
	aesd v7.16b, v17.16b
	eor v7.16b, v7.16b, v16.16b
	str q0, [x2, #0]
	str q1, [x2, #16]
	str q2, [x2, #32]
	str q3, [x2, #48]
	str q4, [x2, #64]
	str q5, [x2, #80]
	str q6, [x2, #96]
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	lsr x13, x3, #3
	cbnz x13, 22b
	b 21f
20:
21:
	cbz x3, 27f
29:
	ldr q0, [x2, #0]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	cbz x6, 210f
	cbz x7, 212f
	aesd v0.16b, v29.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v28.16b
	aesimc v0.16b, v0.16b
	b 213f
212:
213:
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
	b 211f
210:
211:
	aesd v0.16b, v25.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v24.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v23.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v22.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v21.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v20.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v19.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v18.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v17.16b
	eor v0.16b, v0.16b, v16.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	ret
	.p2align 6

vg_aes_ecb_encrypt:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x4, [sp, #8]
	bl {vg_aes_encrypt_blocks}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #2048, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_aes_ecb_decrypt:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x4, [sp, #8]
	bl {vg_aes_decrypt_blocks}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #2048, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6
