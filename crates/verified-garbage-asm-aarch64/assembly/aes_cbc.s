// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_decrypt_aes_sha3:
	sub x9, x1, #10
	sub x10, x1, #12
	cbz x9, 20f
	cbz x10, 22f
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
	sub x9, x3, #7
	lsr x13, x9, #63
	cbnz x13, 24f
	.p2align 4
26:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
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
	aesd v0.16b, v17.16b
	aesd v1.16b, v17.16b
	aesd v2.16b, v17.16b
	aesd v3.16b, v17.16b
	aesd v4.16b, v17.16b
	aesd v5.16b, v17.16b
	aesd v6.16b, v17.16b
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	eor3 v1.16b, v1.16b, v16.16b, v31.16b
	ldr q31, [x2, #16]
	str q1, [x2, #16]
	eor3 v2.16b, v2.16b, v16.16b, v31.16b
	ldr q31, [x2, #32]
	str q2, [x2, #32]
	eor3 v3.16b, v3.16b, v16.16b, v31.16b
	ldr q31, [x2, #48]
	str q3, [x2, #48]
	eor3 v4.16b, v4.16b, v16.16b, v31.16b
	ldr q31, [x2, #64]
	str q4, [x2, #64]
	eor3 v5.16b, v5.16b, v16.16b, v31.16b
	ldr q31, [x2, #80]
	str q5, [x2, #80]
	eor3 v6.16b, v6.16b, v16.16b, v31.16b
	ldr q31, [x2, #96]
	str q6, [x2, #96]
	add x2, x2, #112
	sub x3, x3, #7
	sub x9, x3, #7
	lsr x13, x9, #63
	cbz x13, 26b
	b 25f
24:
25:
	cbz x3, 27f
	.p2align 4
29:
	ldr q0, [x2, #0]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v29.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v28.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
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
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	str q31, [x11, #0]
	b 23f
22:
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
	sub x9, x3, #7
	lsr x13, x9, #63
	cbnz x13, 210f
	.p2align 4
212:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
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
	aesd v0.16b, v17.16b
	aesd v1.16b, v17.16b
	aesd v2.16b, v17.16b
	aesd v3.16b, v17.16b
	aesd v4.16b, v17.16b
	aesd v5.16b, v17.16b
	aesd v6.16b, v17.16b
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	eor3 v1.16b, v1.16b, v16.16b, v31.16b
	ldr q31, [x2, #16]
	str q1, [x2, #16]
	eor3 v2.16b, v2.16b, v16.16b, v31.16b
	ldr q31, [x2, #32]
	str q2, [x2, #32]
	eor3 v3.16b, v3.16b, v16.16b, v31.16b
	ldr q31, [x2, #48]
	str q3, [x2, #48]
	eor3 v4.16b, v4.16b, v16.16b, v31.16b
	ldr q31, [x2, #64]
	str q4, [x2, #64]
	eor3 v5.16b, v5.16b, v16.16b, v31.16b
	ldr q31, [x2, #80]
	str q5, [x2, #80]
	eor3 v6.16b, v6.16b, v16.16b, v31.16b
	ldr q31, [x2, #96]
	str q6, [x2, #96]
	add x2, x2, #112
	sub x3, x3, #7
	sub x9, x3, #7
	lsr x13, x9, #63
	cbz x13, 212b
	b 211f
210:
211:
	cbz x3, 213f
	.p2align 4
215:
	ldr q0, [x2, #0]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v27.16b
	aesimc v0.16b, v0.16b
	aesd v0.16b, v26.16b
	aesimc v0.16b, v0.16b
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
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 215b
	b 214f
213:
214:
	str q31, [x11, #0]
23:
	b 21f
20:
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
	sub x9, x3, #7
	lsr x13, x9, #63
	cbnz x13, 216f
	.p2align 4
218:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q4, [x2, #64]
	ldr q5, [x2, #80]
	ldr q6, [x2, #96]
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
	aesd v0.16b, v17.16b
	aesd v1.16b, v17.16b
	aesd v2.16b, v17.16b
	aesd v3.16b, v17.16b
	aesd v4.16b, v17.16b
	aesd v5.16b, v17.16b
	aesd v6.16b, v17.16b
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	eor3 v1.16b, v1.16b, v16.16b, v31.16b
	ldr q31, [x2, #16]
	str q1, [x2, #16]
	eor3 v2.16b, v2.16b, v16.16b, v31.16b
	ldr q31, [x2, #32]
	str q2, [x2, #32]
	eor3 v3.16b, v3.16b, v16.16b, v31.16b
	ldr q31, [x2, #48]
	str q3, [x2, #48]
	eor3 v4.16b, v4.16b, v16.16b, v31.16b
	ldr q31, [x2, #64]
	str q4, [x2, #64]
	eor3 v5.16b, v5.16b, v16.16b, v31.16b
	ldr q31, [x2, #80]
	str q5, [x2, #80]
	eor3 v6.16b, v6.16b, v16.16b, v31.16b
	ldr q31, [x2, #96]
	str q6, [x2, #96]
	add x2, x2, #112
	sub x3, x3, #7
	sub x9, x3, #7
	lsr x13, x9, #63
	cbz x13, 218b
	b 217f
216:
217:
	cbz x3, 219f
	.p2align 4
221:
	ldr q0, [x2, #0]
	aesd v0.16b, v30.16b
	aesimc v0.16b, v0.16b
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
	eor3 v0.16b, v0.16b, v16.16b, v31.16b
	ldr q31, [x2, #0]
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 221b
	b 220f
219:
220:
	str q31, [x11, #0]
21:
	ret
	.p2align 6

vg_aes_cbc_encrypt_aes:
	sub x9, x1, #10
	sub x10, x1, #12
	cbz x9, 20f
	cbz x10, 22f
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
	eor v7.16b, v16.16b, v30.16b
	eor v31.16b, v31.16b, v30.16b
	cbz x3, 24f
	ldr q0, [x2, #0]
	eor v0.16b, v0.16b, v7.16b
	.p2align 5
	movz x12, #0, lsl #0
26:
	aese v31.16b, v0.16b
	aesmc v31.16b, v31.16b
	sub x3, x3, #1
	aese v31.16b, v17.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v18.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v19.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v20.16b
	aesmc v31.16b, v31.16b
	cbz x3, 27f
	ldr q0, [x2, #16]
	eor v0.16b, v0.16b, v7.16b
	b 28f
27:
28:
	aese v31.16b, v21.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v22.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v23.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v24.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v25.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v26.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v27.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v28.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v29.16b
	eor v1.16b, v31.16b, v30.16b
	str q1, [x2, #0]
	add x2, x2, #16
	cbnz x3, 26b
	b 25f
24:
25:
	eor v31.16b, v31.16b, v30.16b
	str q31, [x11, #0]
	b 23f
22:
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
	eor v7.16b, v16.16b, v30.16b
	eor v31.16b, v31.16b, v30.16b
	cbz x3, 29f
	ldr q0, [x2, #0]
	eor v0.16b, v0.16b, v7.16b
	.p2align 5
	movz x12, #0, lsl #0
	movz x12, #0, lsl #0
	movz x12, #0, lsl #0
	movz x12, #0, lsl #0
	movz x12, #0, lsl #0
	movz x12, #0, lsl #0
211:
	aese v31.16b, v0.16b
	aesmc v31.16b, v31.16b
	sub x3, x3, #1
	aese v31.16b, v17.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v18.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v19.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v20.16b
	aesmc v31.16b, v31.16b
	cbz x3, 212f
	ldr q0, [x2, #16]
	eor v0.16b, v0.16b, v7.16b
	b 213f
212:
213:
	aese v31.16b, v21.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v22.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v23.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v24.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v25.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v26.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v29.16b
	eor v1.16b, v31.16b, v30.16b
	str q1, [x2, #0]
	add x2, x2, #16
	cbnz x3, 211b
	b 210f
29:
210:
	eor v31.16b, v31.16b, v30.16b
	str q31, [x11, #0]
23:
	b 21f
20:
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
	eor v7.16b, v16.16b, v30.16b
	eor v31.16b, v31.16b, v30.16b
	cbz x3, 214f
	ldr q0, [x2, #0]
	eor v0.16b, v0.16b, v7.16b
	.p2align 5
216:
	aese v31.16b, v0.16b
	aesmc v31.16b, v31.16b
	sub x3, x3, #1
	aese v31.16b, v17.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v18.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v19.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v20.16b
	aesmc v31.16b, v31.16b
	cbz x3, 217f
	ldr q0, [x2, #16]
	eor v0.16b, v0.16b, v7.16b
	b 218f
217:
218:
	aese v31.16b, v21.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v22.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v23.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v24.16b
	aesmc v31.16b, v31.16b
	aese v31.16b, v29.16b
	eor v1.16b, v31.16b, v30.16b
	str q1, [x2, #0]
	add x2, x2, #16
	cbnz x3, 216b
	b 215f
214:
215:
	eor v31.16b, v31.16b, v30.16b
	str q31, [x11, #0]
21:
	ret
	.p2align 6

vg_aes_cbc_decrypt_aes:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_aes_cbc_decrypt_unwiped_aes}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #2176, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_aes_cbc_encrypt:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_aes_cbc_encrypt_unwiped}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #2176, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6

vg_aes_cbc_decrypt:
	sub sp, sp, #32
	str x30, [sp, #0]
	str x5, [sp, #8]
	bl {vg_aes_cbc_decrypt_unwiped}
	str x0, [sp, #16]
	ldr x0, [sp, #8]
	movz x1, #2176, lsl #0
	bl {vg_zeroize}
	ldr x0, [sp, #16]
	ldr x30, [sp, #0]
	add sp, sp, #32
	ret
	.p2align 6
