// The functions of `src/internal/vg_aes_xts_decrypt_aes.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_xts_decrypt_aes:
	.arch_extension aes
	add x11, x2, #0
	add x2, x3, #0
	add x3, x4, #0
	ldr x14, [x11, #0]
	ldr x15, [x11, #8]
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
	add x12, x5, #0
	add x8, x5, #128
	str x14, [x12, #0]
	str x15, [x12, #8]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #16]
	str x15, [x12, #24]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #32]
	str x15, [x12, #40]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #48]
	str x15, [x12, #56]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #64]
	str x15, [x12, #72]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #80]
	str x15, [x12, #88]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #96]
	str x15, [x12, #104]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x12, #112]
	str x15, [x12, #120]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
22:
	ldr q0, [x2, #0]
	ldr q31, [x12, #0]
	eor v0.16b, v0.16b, v31.16b
	ldr q1, [x2, #16]
	ldr q31, [x12, #16]
	eor v1.16b, v1.16b, v31.16b
	ldr q2, [x2, #32]
	ldr q31, [x12, #32]
	eor v2.16b, v2.16b, v31.16b
	ldr q3, [x2, #48]
	ldr q31, [x12, #48]
	eor v3.16b, v3.16b, v31.16b
	ldr q4, [x2, #64]
	ldr q31, [x12, #64]
	eor v4.16b, v4.16b, v31.16b
	ldr q5, [x2, #80]
	ldr q31, [x12, #80]
	eor v5.16b, v5.16b, v31.16b
	ldr q6, [x2, #96]
	ldr q31, [x12, #96]
	eor v6.16b, v6.16b, v31.16b
	ldr q7, [x2, #112]
	ldr q31, [x12, #112]
	eor v7.16b, v7.16b, v31.16b
	str x14, [x8, #0]
	str x15, [x8, #8]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #16]
	str x15, [x8, #24]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #32]
	str x15, [x8, #40]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #48]
	str x15, [x8, #56]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #64]
	str x15, [x8, #72]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #80]
	str x15, [x8, #88]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #96]
	str x15, [x8, #104]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
	str x14, [x8, #112]
	str x15, [x8, #120]
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
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
	ldr q31, [x12, #0]
	eor v0.16b, v0.16b, v31.16b
	str q0, [x2, #0]
	ldr q31, [x12, #16]
	eor v1.16b, v1.16b, v31.16b
	str q1, [x2, #16]
	ldr q31, [x12, #32]
	eor v2.16b, v2.16b, v31.16b
	str q2, [x2, #32]
	ldr q31, [x12, #48]
	eor v3.16b, v3.16b, v31.16b
	str q3, [x2, #48]
	ldr q31, [x12, #64]
	eor v4.16b, v4.16b, v31.16b
	str q4, [x2, #64]
	ldr q31, [x12, #80]
	eor v5.16b, v5.16b, v31.16b
	str q5, [x2, #80]
	ldr q31, [x12, #96]
	eor v6.16b, v6.16b, v31.16b
	str q6, [x2, #96]
	ldr q31, [x12, #112]
	eor v7.16b, v7.16b, v31.16b
	str q7, [x2, #112]
	add x2, x2, #128
	sub x3, x3, #8
	lsr x13, x3, #3
	add x10, x12, #0
	add x12, x8, #0
	add x8, x10, #0
	cbnz x13, 22b
	ldr x14, [x12, #0]
	ldr x15, [x12, #8]
	b 21f
20:
21:
	cbz x3, 27f
29:
	ldr q0, [x2, #0]
	dup v31.2d, x14
	mov v31.d[1], x15
	str q31, [x5, #0]
	eor v0.16b, v0.16b, v31.16b
	adds x14, x14, x14
	adcs x15, x15, x15
	movz x9, #135, lsl #0
	movz x10, #0, lsl #0
	csel x9, x9, x10, hs
	eor x14, x14, x9
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
	ldr q31, [x5, #0]
	eor v0.16b, v0.16b, v31.16b
	str q0, [x2, #0]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 29b
	b 28f
27:
28:
	str x14, [x11, #0]
	str x15, [x11, #8]
	ret
	.arch_extension noaes
	.p2align 6
