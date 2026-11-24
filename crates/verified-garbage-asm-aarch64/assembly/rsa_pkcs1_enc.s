// The functions of `src/rsa_pkcs1_enc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_decrypt_precomputed_sha256_sha2:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x4, [x9, #168]
	str x2, [x9, #216]
	ldr x10, [sp, #288]
	str x10, [x9, #0]
	ldr x10, [sp, #296]
	str x10, [x9, #8]
	ldr x10, [sp, #304]
	str x10, [x9, #16]
	ldr x10, [sp, #312]
	str x10, [x9, #24]
	ldr x10, [sp, #320]
	str x10, [x9, #32]
	ldr x10, [sp, #328]
	str x10, [x9, #40]
	ldr x10, [sp, #336]
	str x10, [x9, #48]
	ldr x10, [sp, #344]
	str x10, [x9, #56]
	ldr x10, [sp, #352]
	str x10, [x9, #64]
	ldr x10, [sp, #360]
	str x10, [x9, #72]
	ldr x10, [sp, #368]
	str x10, [x9, #80]
	ldr x10, [sp, #376]
	str x10, [x9, #88]
	ldr x10, [sp, #384]
	str x10, [x9, #96]
	ldr x10, [sp, #392]
	str x10, [x9, #104]
	ldr x10, [sp, #400]
	str x10, [x9, #112]
	ldr x10, [sp, #408]
	str x10, [x9, #120]
	ldr x10, [sp, #416]
	str x10, [x9, #128]
	bl {vg_rsa_pkcs1_decrypt_precomputed_body_sha256_sha2}
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	ldr x12, [sp, #168]
	add x12, x12, #7
	lsr x12, x12, #3
	add x12, x12, x12
	movz x13, #0, lsl #0
20:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x11, [sp, #152]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x13, [sp, #168]
21:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 21b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #168]
	ldr x10, [sp, #216]
	ldr x8, [sp, #168]
	ldr x7, [sp, #168]
	ldr x10, [x10, #0]
	sub x9, x9, x10
	movz x14, #1, lsl #0
	add x7, x7, #7
	lsr x7, x7, #3
22:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	orr x13, x7, x7
23:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 23b
	lsr x9, x9, #1
	add x14, x14, x14
	lsr x8, x8, #1
	cbnz x8, 22b
	ldr x11, [sp, #96]
	add x11, x11, #1024
	ldr x12, [sp, #152]
	ldr x13, [sp, #168]
24:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 24b
	ldr x0, [sp, #224]
	add sp, sp, #272
	ldr x30, [sp], #16
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
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
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
	add w0, w0, #0
	sub sp, sp, #3776
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #59, lsl #0
25:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 25b
	add sp, sp, #3776
	ret
	.p2align 6

vg_rsa_pkcs1_decrypt_precomputed:
	str x30, [sp, #-16]!
	sub sp, sp, #272
	add x9, sp, #0
	str x0, [x9, #152]
	str x4, [x9, #168]
	str x2, [x9, #216]
	ldr x10, [sp, #288]
	str x10, [x9, #0]
	ldr x10, [sp, #296]
	str x10, [x9, #8]
	ldr x10, [sp, #304]
	str x10, [x9, #16]
	ldr x10, [sp, #312]
	str x10, [x9, #24]
	ldr x10, [sp, #320]
	str x10, [x9, #32]
	ldr x10, [sp, #328]
	str x10, [x9, #40]
	ldr x10, [sp, #336]
	str x10, [x9, #48]
	ldr x10, [sp, #344]
	str x10, [x9, #56]
	ldr x10, [sp, #352]
	str x10, [x9, #64]
	ldr x10, [sp, #360]
	str x10, [x9, #72]
	ldr x10, [sp, #368]
	str x10, [x9, #80]
	ldr x10, [sp, #376]
	str x10, [x9, #88]
	ldr x10, [sp, #384]
	str x10, [x9, #96]
	ldr x10, [sp, #392]
	str x10, [x9, #104]
	ldr x10, [sp, #400]
	str x10, [x9, #112]
	ldr x10, [sp, #408]
	str x10, [x9, #120]
	ldr x10, [sp, #416]
	str x10, [x9, #128]
	bl {vg_rsa_pkcs1_decrypt_precomputed_body}
	add x9, sp, #0
	str x0, [x9, #224]
	ldr x10, [sp, #392]
	str x10, [x9, #96]
	ldr x11, [sp, #96]
	add x11, x11, #1024
	ldr x12, [sp, #168]
	add x12, x12, #7
	lsr x12, x12, #3
	add x12, x12, x12
	movz x13, #0, lsl #0
20:
	str x13, [x11, #0]
	add x11, x11, #8
	sub x12, x12, #1
	cbnz x12, 20b
	ldr x11, [sp, #152]
	ldr x12, [sp, #96]
	add x12, x12, #1024
	ldr x13, [sp, #168]
21:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 21b
	ldr x17, [sp, #96]
	add x17, x17, #1024
	ldr x9, [sp, #168]
	ldr x10, [sp, #216]
	ldr x8, [sp, #168]
	ldr x7, [sp, #168]
	ldr x10, [x10, #0]
	sub x9, x9, x10
	movz x14, #1, lsl #0
	add x7, x7, #7
	lsr x7, x7, #3
22:
	orr x11, x17, x17
	add x12, x17, x14
	movz x15, #1, lsl #0
	and x15, x9, x15
	movz x16, #0, lsl #0
	sub x15, x16, x15
	orr x13, x7, x7
23:
	ldr x10, [x11, #0]
	ldr x16, [x12, #0]
	eor x16, x16, x10
	and x16, x16, x15
	eor x10, x10, x16
	str x10, [x11, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 23b
	lsr x9, x9, #1
	add x14, x14, x14
	lsr x8, x8, #1
	cbnz x8, 22b
	ldr x11, [sp, #96]
	add x11, x11, #1024
	ldr x12, [sp, #152]
	ldr x13, [sp, #168]
24:
	ldrb w10, [x11, #0]
	strb w10, [x12, #0]
	add x11, x11, #1
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 24b
	ldr x0, [sp, #224]
	add sp, sp, #272
	ldr x30, [sp], #16
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
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
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
	add w0, w0, #0
	sub sp, sp, #3776
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #59, lsl #0
25:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 25b
	add sp, sp, #3776
	ret
	.p2align 6

vg_rsa_pkcs1_encrypt_random:
	str x30, [sp, #-16]!
	sub sp, sp, #1088
	ldr x9, [sp, #1104]
	ldr x11, [sp, #1112]
	ldr x12, [sp, #1120]
	sub x15, x4, x9
	sub x15, x15, #3
	str x15, [sp, #48]
	add x14, sp, #64
	orr x16, x15, x15
	cbnz x12, 20f
	b 21f
20:
22:
	ldrb w17, [x11, #0]
	add x11, x11, #1
	sub x12, x12, #1
	cbz x17, 23f
	strb w17, [x14, #0]
	add x14, x14, #1
	sub x16, x16, #1
	b 24f
23:
24:
	mul x9, x12, x16
	cbnz x9, 22b
21:
	cbz x16, 25f
	orr x9, x0, x0
	orr x10, x4, x4
	movz x13, #0, lsl #0
27:
	strb w13, [x9, #0]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 27b
	movz x10, #1024, lsl #0
	add x9, sp, #64
28:
	strb w13, [x9, #0]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 28b
	add x11, x15, #128
	ldr x12, [sp, #1120]
	sub x10, x15, x16
	add x9, x15, x12
	sub x9, x9, x10
	subs x17, x11, x9
	csel x9, x11, x9, lo
	subs x17, x12, x11
	movz x13, #0, lsl #0
	csel x14, x12, x13, hs
	csel x9, x13, x9, hs
	movz x10, #3, lsl #0
	csel x0, x10, x13, hs
	str x14, [x2, #0]
	str x9, [x2, #8]
	b 26f
25:
	ldr x9, [sp, #1120]
	sub x9, x9, x12
	ldr x10, [sp, #1128]
	ldr x11, [sp, #1136]
	ldr x13, [sp, #1144]
	ldr x14, [sp, #1152]
	ldr x8, [sp, #1104]
	add x16, sp, #64
	movz x17, #0, lsl #0
	str x9, [x2, #0]
	str x17, [x2, #8]
	str x16, [sp, #0]
	str x15, [sp, #8]
	str x10, [sp, #16]
	str x11, [sp, #24]
	str x13, [sp, #32]
	str x14, [sp, #40]
	orr x2, x3, x3
	orr x3, x4, x4
	orr x4, x5, x5
	orr x5, x6, x6
	orr x6, x7, x7
	orr x7, x8, x8
	bl {vg_rsa_pkcs1_encrypt_precomputed}
	movz x9, #2, lsl #0
	sub w0, w9, w0
	movz x12, #1024, lsl #0
	add x13, sp, #64
	movz x14, #0, lsl #0
29:
	strb w14, [x13, #0]
	add x13, x13, #1
	sub x12, x12, #1
	cbnz x12, 29b
26:
	add sp, sp, #1088
	ldr x30, [sp], #16
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
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
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
	movi v31.2d, #0
	tst x1, x1
	add w0, w0, #0
	sub sp, sp, #2208
	movi v31.2d, #0
	add x9, sp, #0
	movz x10, #34, lsl #0
210:
	str q31, [x9, #0]
	str q31, [x9, #16]
	str q31, [x9, #32]
	str q31, [x9, #48]
	add x9, x9, #64
	sub x10, x10, #1
	cbnz x10, 210b
	str q31, [x9, #0]
	str q31, [x9, #16]
	add sp, sp, #2208
	ret
	.p2align 6
