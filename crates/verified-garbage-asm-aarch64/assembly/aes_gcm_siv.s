// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal_aes:
	.arch_extension aes
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch_aes}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	lsr x10, x28, #10
	cbz x10, 24f
	movz x10, #64, lsl #0
	b 25f
24:
	lsr x10, x28, #4
25:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
26:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 26b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
29:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 29b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 28f
27:
28:
	lsr x9, x26, #7
	cbz x9, 213f
	ldr q6, [x19, #64]
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v24.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v24.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v24.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v24.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v25.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v16.2d
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
	str q24, [x19, #480]
	str q25, [x19, #496]
	str q26, [x19, #512]
	str q27, [x19, #528]
	str q28, [x19, #544]
	str q29, [x19, #560]
	str q30, [x19, #576]
	str q31, [x19, #592]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #608]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #624]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	add x9, x25, #0
	lsr x11, x26, #7
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x19, #80]
	rev64 v16.16b, v16.16b
215:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #80]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor v27.16b, v27.16b, v19.16b
	eor v27.16b, v27.16b, v18.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor v16.16b, v18.16b, v20.16b
	eor v16.16b, v16.16b, v26.16b
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 215b
	rev64 v16.16b, v16.16b
	str q16, [x19, #80]
	b 214f
213:
214:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 216f
218:
	lsr x10, x28, #10
	cbz x10, 219f
	movz x10, #64, lsl #0
	b 220f
219:
	lsr x10, x28, #4
220:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
221:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 221b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 218b
	b 217f
216:
217:
	cbz x28, 222f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
224:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 224b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 225f
	movz x10, #64, lsl #0
	b 226f
225:
	lsr x10, x28, #4
226:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
227:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 227b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 223f
222:
223:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 228f
	movz x10, #64, lsl #0
	b 229f
228:
	lsr x10, x28, #4
229:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
230:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 230b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #0
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	lsr x9, x26, #7
	cbz x9, 231f
	ldr w10, [x19, #96]
	add x15, x19, #240
	add x9, x25, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 233f
	cbz x14, 235f
237:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
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
	ldr q30, [x15, #192]
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
	ldr q30, [x15, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbnz x11, 237b
	b 236f
235:
238:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #192]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbnz x11, 238b
236:
	b 234f
233:
239:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #160]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbnz x11, 239b
234:
	str w10, [x19, #96]
	b 232f
231:
232:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 240f
242:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32_aes}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 242b
	b 241f
240:
241:
	cbz x28, 243f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
245:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	ldr x9, [x19, #216]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #3824
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_siv_open_aes:
	.arch_extension aes
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	ldr x9, [x19, #216]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch_aes}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	lsr x10, x28, #10
	cbz x10, 24f
	movz x10, #64, lsl #0
	b 25f
24:
	lsr x10, x28, #4
25:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
26:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 26b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
29:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 29b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 28f
27:
28:
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	lsr x9, x26, #7
	cbz x9, 213f
	ldr q6, [x19, #64]
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v24.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v24.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v24.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v24.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v25.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v16.2d
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
	str q24, [x19, #480]
	str q25, [x19, #496]
	str q26, [x19, #512]
	str q27, [x19, #528]
	str q28, [x19, #544]
	str q29, [x19, #560]
	str q30, [x19, #576]
	str q31, [x19, #592]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #608]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #624]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	ldr w10, [x19, #96]
	add x15, x19, #240
	add x9, x25, #0
	lsr x11, x26, #7
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x19, #80]
	rev64 v16.16b, v16.16b
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 215f
	cbz x14, 217f
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
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
	ldr q30, [x15, #192]
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
	ldr q30, [x15, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbz x11, 219f
221:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	ext v22.16b, v22.16b, v22.16b, #8
	add w12, w10, #2
	ldr q2, [x19, #96]
	ldr q23, [x19, #576]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q24, [x19, #560]
	ldr q3, [x19, #96]
	ldr q25, [x19, #608]
	mov v3.s[0], w12
	add w12, w10, #4
	trn1 v26.2d, v21.2d, v22.2d
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	trn2 v27.2d, v21.2d, v22.2d
	add w12, w10, #5
	ldr q5, [x19, #96]
	eor v26.16b, v26.16b, v27.16b
	mov v5.s[0], w12
	add w12, w10, #6
	pmull v28.1q, v21.1d, v23.1d
	ldr q6, [x19, #96]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v6.s[0], w12
	add w12, w10, #7
	pmull v29.1q, v22.1d, v24.1d
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x15, #0]
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
	eor v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v20.16b, v27.16b, v26.16b
	ldr q30, [x15, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #48]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q22, [x9, #64]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q23, [x19, #544]
	ldr q30, [x15, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q24, [x19, #528]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q25, [x19, #624]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v26.16b, v26.16b, v27.16b
	ldr q30, [x15, #48]
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
	pmull v27.1q, v26.1d, v25.1d
	ldr q30, [x15, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v18.16b, v18.16b, v28.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v18.16b, v18.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v19.16b, v19.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v19.16b, v19.16b, v22.16b
	ldr q30, [x15, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v20.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v20.16b, v20.16b, v26.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #80]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #96]
	ldr q22, [x9, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q23, [x19, #512]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q24, [x19, #496]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #640]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #112]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v26.16b, v26.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #128]
	pmull v29.1q, v22.1d, v24.1d
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
	eor v18.16b, v18.16b, v28.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #144]
	eor v18.16b, v18.16b, v29.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v19.16b, v19.16b, v21.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v19.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v20.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v20.16b, v20.16b, v26.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #160]
	ldr q21, [x9, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q22, [x9, #0]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v22.16b, v22.16b, v16.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #176]
	ldr q23, [x19, #480]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q24, [x19, #592]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q25, [x19, #656]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #192]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v21.1q, v21.2d, v23.2d
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
	ldr q30, [x15, #208]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	eor v18.16b, v18.16b, v28.16b
	aese v4.16b, v30.16b
	eor v18.16b, v18.16b, v29.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	eor v19.16b, v19.16b, v21.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
	eor v19.16b, v19.16b, v22.16b
	ldr q31, [x9, #128]
	eor v0.16b, v0.16b, v31.16b
	eor v20.16b, v20.16b, v27.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #144]
	eor v20.16b, v20.16b, v26.16b
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x9, #160]
	ext v27.16b, v19.16b, v19.16b, #8
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	eor v27.16b, v27.16b, v19.16b
	ldr q31, [x9, #176]
	eor v3.16b, v3.16b, v31.16b
	eor v27.16b, v27.16b, v18.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #192]
	eor v20.16b, v20.16b, v27.16b
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q31, [x9, #208]
	pmull v26.1q, v20.1d, v17.1d
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ext v18.16b, v18.16b, v18.16b, #8
	ldr q31, [x9, #224]
	eor v6.16b, v6.16b, v31.16b
	ext v26.16b, v26.16b, v26.16b, #8
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #240]
	eor v16.16b, v18.16b, v20.16b
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
	eor v16.16b, v16.16b, v26.16b
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
	cbnz x11, 221b
	b 220f
219:
220:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #80]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor v27.16b, v27.16b, v19.16b
	eor v27.16b, v27.16b, v18.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor v16.16b, v18.16b, v20.16b
	eor v16.16b, v16.16b, v26.16b
	add x9, x9, #128
	b 218f
217:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #192]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbz x11, 222f
224:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	ldr q1, [x19, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q23, [x19, #576]
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	ldr q24, [x19, #560]
	add w12, w10, #3
	ldr q25, [x19, #608]
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	trn1 v26.2d, v21.2d, v22.2d
	add w12, w10, #4
	ldr q4, [x19, #96]
	trn2 v27.2d, v21.2d, v22.2d
	mov v4.s[0], w12
	eor v26.16b, v26.16b, v27.16b
	add w12, w10, #5
	ldr q5, [x19, #96]
	pmull v28.1q, v21.1d, v23.1d
	mov v5.s[0], w12
	pmull2 v21.1q, v21.2d, v23.2d
	add w12, w10, #6
	ldr q6, [x19, #96]
	pmull v29.1q, v22.1d, v24.1d
	mov v6.s[0], w12
	add w12, w10, #7
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q7, [x19, #96]
	pmull v27.1q, v26.1d, v25.1d
	mov v7.s[0], w12
	ldr q30, [x15, #0]
	pmull2 v26.1q, v26.2d, v25.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v18.16b, v28.16b, v29.16b
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
	ldr q21, [x9, #48]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q30, [x15, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q22, [x9, #64]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q23, [x19, #544]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #528]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #624]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #32]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v26.16b, v26.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x15, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
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
	eor v18.16b, v18.16b, v28.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v18.16b, v18.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #64]
	eor v19.16b, v19.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v19.16b, v19.16b, v22.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v20.16b, v20.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v20.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q21, [x9, #80]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q30, [x15, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q22, [x9, #96]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q23, [x19, #512]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q24, [x19, #496]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #640]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #96]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v26.16b, v26.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x15, #112]
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
	eor v18.16b, v18.16b, v28.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v18.16b, v18.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #128]
	eor v19.16b, v19.16b, v21.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v19.16b, v19.16b, v22.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v20.16b, v20.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v20.16b, v20.16b, v26.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q21, [x9, #112]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q30, [x15, #144]
	ldr q22, [x9, #0]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v22.16b, v22.16b, v16.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #480]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q24, [x19, #592]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #160]
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
	eor v26.16b, v26.16b, v27.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x15, #176]
	pmull v29.1q, v22.1d, v24.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	eor v18.16b, v18.16b, v28.16b
	aese v7.16b, v30.16b
	eor v18.16b, v18.16b, v29.16b
	ldr q30, [x15, #192]
	ldr q31, [x9, #128]
	eor v19.16b, v19.16b, v21.16b
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	eor v19.16b, v19.16b, v22.16b
	ldr q31, [x9, #144]
	eor v20.16b, v20.16b, v27.16b
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q31, [x9, #160]
	eor v2.16b, v2.16b, v31.16b
	pmull v26.1q, v19.1d, v17.1d
	eor v2.16b, v2.16b, v30.16b
	ext v27.16b, v19.16b, v19.16b, #8
	ldr q31, [x9, #176]
	eor v3.16b, v3.16b, v31.16b
	eor v27.16b, v27.16b, v19.16b
	eor v3.16b, v3.16b, v30.16b
	eor v27.16b, v27.16b, v18.16b
	ldr q31, [x9, #192]
	eor v4.16b, v4.16b, v31.16b
	eor v20.16b, v20.16b, v27.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #208]
	eor v20.16b, v20.16b, v26.16b
	eor v5.16b, v5.16b, v31.16b
	pmull v26.1q, v20.1d, v17.1d
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #224]
	ext v18.16b, v18.16b, v18.16b, #8
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #240]
	eor v16.16b, v18.16b, v20.16b
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
	eor v16.16b, v16.16b, v26.16b
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
	cbnz x11, 224b
	b 223f
222:
223:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #80]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor v27.16b, v27.16b, v19.16b
	eor v27.16b, v27.16b, v18.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor v16.16b, v18.16b, v20.16b
	eor v16.16b, v16.16b, v26.16b
	add x9, x9, #128
218:
	b 216f
215:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #160]
	ldr q31, [x9, #0]
	eor v0.16b, v0.16b, v31.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #16]
	eor v1.16b, v1.16b, v31.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #32]
	eor v2.16b, v2.16b, v31.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #48]
	eor v3.16b, v3.16b, v31.16b
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #64]
	eor v4.16b, v4.16b, v31.16b
	eor v4.16b, v4.16b, v30.16b
	ldr q31, [x9, #80]
	eor v5.16b, v5.16b, v31.16b
	eor v5.16b, v5.16b, v30.16b
	ldr q31, [x9, #96]
	eor v6.16b, v6.16b, v31.16b
	eor v6.16b, v6.16b, v30.16b
	ldr q31, [x9, #112]
	eor v7.16b, v7.16b, v31.16b
	eor v7.16b, v7.16b, v30.16b
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
	cbz x11, 225f
227:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	ldr q22, [x9, #32]
	add w12, w10, #1
	ldr q1, [x19, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	mov v1.s[0], w12
	ldr q23, [x19, #576]
	add w12, w10, #2
	ldr q2, [x19, #96]
	ldr q24, [x19, #560]
	mov v2.s[0], w12
	ldr q25, [x19, #608]
	add w12, w10, #3
	ldr q3, [x19, #96]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[0], w12
	trn2 v27.2d, v21.2d, v22.2d
	add w12, w10, #4
	eor v26.16b, v26.16b, v27.16b
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	pmull v28.1q, v21.1d, v23.1d
	add w12, w10, #5
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	pmull v29.1q, v22.1d, v24.1d
	add w12, w10, #6
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	pmull v27.1q, v26.1d, v25.1d
	add w12, w10, #7
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	eor v18.16b, v28.16b, v29.16b
	ldr q30, [x15, #0]
	eor v19.16b, v21.16b, v22.16b
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
	ext v21.16b, v21.16b, v21.16b, #8
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #64]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #16]
	ldr q23, [x19, #544]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q24, [x19, #528]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q25, [x19, #624]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn1 v26.2d, v21.2d, v22.2d
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
	pmull v28.1q, v21.1d, v23.1d
	ldr q30, [x15, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v18.16b, v18.16b, v28.16b
	ldr q30, [x15, #48]
	eor v18.16b, v18.16b, v29.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v19.16b, v19.16b, v21.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v19.16b, v19.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v20.16b, v20.16b, v27.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v20.16b, v20.16b, v26.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q21, [x9, #80]
	ldr q30, [x15, #64]
	ext v21.16b, v21.16b, v21.16b, #8
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #96]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q23, [x19, #512]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #496]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #640]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #80]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v26.16b, v26.16b, v27.16b
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
	pmull v29.1q, v22.1d, v24.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x15, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v18.16b, v18.16b, v28.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor v18.16b, v18.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v19.16b, v19.16b, v21.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v19.16b, v19.16b, v22.16b
	ldr q30, [x15, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor v20.16b, v20.16b, v27.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v20.16b, v20.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q21, [x9, #112]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q22, [x9, #0]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q30, [x15, #128]
	eor v22.16b, v22.16b, v16.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #480]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q24, [x19, #592]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #656]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #144]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v3.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v6.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v7.16b, v30.16b
	ldr q30, [x15, #160]
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q31, [x9, #128]
	eor v18.16b, v18.16b, v28.16b
	eor v0.16b, v0.16b, v31.16b
	eor v18.16b, v18.16b, v29.16b
	eor v0.16b, v0.16b, v30.16b
	ldr q31, [x9, #144]
	eor v19.16b, v19.16b, v21.16b
	eor v1.16b, v1.16b, v31.16b
	eor v19.16b, v19.16b, v22.16b
	eor v1.16b, v1.16b, v30.16b
	ldr q31, [x9, #160]
	eor v20.16b, v20.16b, v27.16b
	eor v2.16b, v2.16b, v31.16b
	eor v20.16b, v20.16b, v26.16b
	eor v2.16b, v2.16b, v30.16b
	ldr q31, [x9, #176]
	pmull v26.1q, v19.1d, v17.1d
	eor v3.16b, v3.16b, v31.16b
	ext v27.16b, v19.16b, v19.16b, #8
	eor v3.16b, v3.16b, v30.16b
	ldr q31, [x9, #192]
	eor v27.16b, v27.16b, v19.16b
	eor v4.16b, v4.16b, v31.16b
	eor v27.16b, v27.16b, v18.16b
	eor v4.16b, v4.16b, v30.16b
	eor v20.16b, v20.16b, v27.16b
	ldr q31, [x9, #208]
	eor v5.16b, v5.16b, v31.16b
	eor v20.16b, v20.16b, v26.16b
	eor v5.16b, v5.16b, v30.16b
	pmull v26.1q, v20.1d, v17.1d
	ldr q31, [x9, #224]
	eor v6.16b, v6.16b, v31.16b
	ext v18.16b, v18.16b, v18.16b, #8
	eor v6.16b, v6.16b, v30.16b
	ext v26.16b, v26.16b, v26.16b, #8
	ldr q31, [x9, #240]
	eor v7.16b, v7.16b, v31.16b
	eor v16.16b, v18.16b, v20.16b
	eor v7.16b, v7.16b, v30.16b
	eor v16.16b, v16.16b, v26.16b
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
	cbnz x11, 227b
	b 226f
225:
226:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
	trn1 v26.2d, v21.2d, v22.2d
	trn2 v27.2d, v21.2d, v22.2d
	eor v26.16b, v26.16b, v27.16b
	pmull v28.1q, v21.1d, v23.1d
	pmull2 v21.1q, v21.2d, v23.2d
	pmull v29.1q, v22.1d, v24.1d
	pmull2 v22.1q, v22.2d, v24.2d
	pmull v27.1q, v26.1d, v25.1d
	pmull2 v26.1q, v26.2d, v25.2d
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #80]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	eor v18.16b, v18.16b, v28.16b
	eor v18.16b, v18.16b, v29.16b
	eor v19.16b, v19.16b, v21.16b
	eor v19.16b, v19.16b, v22.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor v27.16b, v27.16b, v19.16b
	eor v27.16b, v27.16b, v18.16b
	eor v20.16b, v20.16b, v27.16b
	eor v20.16b, v20.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor v16.16b, v18.16b, v20.16b
	eor v16.16b, v16.16b, v26.16b
	add x9, x9, #128
216:
	str w10, [x19, #96]
	rev64 v16.16b, v16.16b
	str q16, [x19, #80]
	b 214f
213:
214:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 228f
230:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32_aes}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 230b
	b 229f
228:
229:
	cbz x28, 231f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
233:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 233b
	b 232f
231:
232:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 234f
236:
	lsr x10, x28, #10
	cbz x10, 237f
	movz x10, #64, lsl #0
	b 238f
237:
	lsr x10, x28, #4
238:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
239:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 239b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 236b
	b 235f
234:
235:
	cbz x28, 240f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 243f
	movz x10, #64, lsl #0
	b 244f
243:
	lsr x10, x28, #4
244:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
245:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 245b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 241f
240:
241:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 246f
	movz x10, #64, lsl #0
	b 247f
246:
	lsr x10, x28, #4
247:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
248:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 248b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	ldr x10, [x19, #224]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #232]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x27, #1, lsl #0
	sub x27, x27, x10
	movz x9, #0, lsl #0
	sub x11, x9, x27
	add x12, x25, #0
	dup v16.16b, w11
	lsr x14, x26, #4
	lsl x9, x14, #4
	sub x13, x26, x9
	cbz x14, 249f
251:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 251b
	b 250f
249:
250:
	cbz x13, 252f
254:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 254b
	b 253f
252:
253:
	add x0, x27, #0
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
	add sp, sp, #3824
	ret
	.arch_extension noaes
	.p2align 6

vg_aes_gcm_siv_seal_aes_sha3:
	.arch_extension aes
	.arch_extension sha3
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch_aes}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	lsr x10, x28, #10
	cbz x10, 24f
	movz x10, #64, lsl #0
	b 25f
24:
	lsr x10, x28, #4
25:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
26:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 26b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
29:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 29b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 28f
27:
28:
	lsr x9, x26, #7
	cbz x9, 213f
	ldr q6, [x19, #64]
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v24.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v24.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v24.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v24.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v25.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v16.2d
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
	str q24, [x19, #480]
	str q25, [x19, #496]
	str q26, [x19, #512]
	str q27, [x19, #528]
	str q28, [x19, #544]
	str q29, [x19, #560]
	str q30, [x19, #576]
	str q31, [x19, #592]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #608]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #624]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	add x9, x25, #0
	lsr x11, x26, #7
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x19, #80]
	rev64 v16.16b, v16.16b
215:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 215b
	rev64 v16.16b, v16.16b
	str q16, [x19, #80]
	b 214f
213:
214:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 216f
218:
	lsr x10, x28, #10
	cbz x10, 219f
	movz x10, #64, lsl #0
	b 220f
219:
	lsr x10, x28, #4
220:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
221:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 221b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 218b
	b 217f
216:
217:
	cbz x28, 222f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
224:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 224b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 225f
	movz x10, #64, lsl #0
	b 226f
225:
	lsr x10, x28, #4
226:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
227:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 227b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 223f
222:
223:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 228f
	movz x10, #64, lsl #0
	b 229f
228:
	lsr x10, x28, #4
229:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
230:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 230b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #0
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	lsr x9, x26, #7
	cbz x9, 231f
	ldr w10, [x19, #96]
	add x15, x19, #240
	add x9, x25, #0
	lsr x11, x26, #7
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 233f
	cbz x14, 235f
237:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
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
	ldr q30, [x15, #192]
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
	ldr q30, [x15, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
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
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 237b
	b 236f
235:
238:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #192]
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
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 238b
236:
	b 234f
233:
239:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #160]
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
	add x9, x9, #128
	sub x11, x11, #1
	cbnz x11, 239b
234:
	str w10, [x19, #96]
	b 232f
231:
232:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 240f
242:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32_aes}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 242b
	b 241f
240:
241:
	cbz x28, 243f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
245:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 245b
	b 244f
243:
244:
	ldr x9, [x19, #216]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #3824
	ret
	.arch_extension noaes
	.arch_extension nosha3
	.p2align 6

vg_aes_gcm_siv_open_aes_sha3:
	.arch_extension aes
	.arch_extension sha3
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	ldr x9, [x19, #216]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch_aes}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	lsr x10, x28, #10
	cbz x10, 24f
	movz x10, #64, lsl #0
	b 25f
24:
	lsr x10, x28, #4
25:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
26:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 26b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
29:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 29b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 28f
27:
28:
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	lsr x9, x26, #7
	cbz x9, 213f
	ldr q6, [x19, #64]
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v24.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v24.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v24.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v24.2d, v16.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v25.16b, v5.16b, v7.16b
	ext v17.16b, v25.16b, v25.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v25.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v25.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v25.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v25.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v27.16b, v5.16b, v7.16b
	ext v19.16b, v27.16b, v27.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v24.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v24.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v16.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v16.2d
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v25.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v25.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v17.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v17.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v29.16b, v5.16b, v7.16b
	ext v21.16b, v29.16b, v29.16b, #8
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v26.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v26.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v18.1d
	eor v4.16b, v4.16b, v7.16b
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
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	pmull v7.1q, v27.1d, v27.1d
	eor v5.16b, v5.16b, v7.16b
	pmull2 v7.1q, v27.2d, v27.2d
	eor v3.16b, v3.16b, v7.16b
	pmull v7.1q, v27.1d, v19.1d
	eor v4.16b, v4.16b, v7.16b
	pmull2 v7.1q, v27.2d, v19.2d
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v3.1d, v1.1d
	ext v3.16b, v3.16b, v3.16b, #8
	eor v4.16b, v4.16b, v3.16b
	eor v4.16b, v4.16b, v7.16b
	pmull v7.1q, v4.1d, v1.1d
	ext v5.16b, v5.16b, v5.16b, #8
	eor v5.16b, v5.16b, v4.16b
	ext v7.16b, v7.16b, v7.16b, #8
	eor v31.16b, v5.16b, v7.16b
	ext v23.16b, v31.16b, v31.16b, #8
	str q24, [x19, #480]
	str q25, [x19, #496]
	str q26, [x19, #512]
	str q27, [x19, #528]
	str q28, [x19, #544]
	str q29, [x19, #560]
	str q30, [x19, #576]
	str q31, [x19, #592]
	eor v2.16b, v30.16b, v22.16b
	eor v3.16b, v29.16b, v21.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #608]
	eor v2.16b, v28.16b, v20.16b
	eor v3.16b, v27.16b, v19.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #624]
	eor v2.16b, v26.16b, v18.16b
	eor v3.16b, v25.16b, v17.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #640]
	eor v2.16b, v24.16b, v16.16b
	eor v3.16b, v31.16b, v23.16b
	ext v4.16b, v2.16b, v3.16b, #8
	str q4, [x19, #656]
	ldr w10, [x19, #96]
	add x15, x19, #240
	add x9, x25, #0
	lsr x11, x26, #7
	movz x12, #49664, lsl #48
	dup v17.2d, x12
	ldr q16, [x19, #80]
	rev64 v16.16b, v16.16b
	sub x13, x22, #10
	sub x14, x22, #12
	cbz x13, 215f
	cbz x14, 217f
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
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
	ldr q30, [x15, #192]
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
	ldr q30, [x15, #208]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
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
	cbz x11, 219f
221:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	ext v22.16b, v22.16b, v22.16b, #8
	add w12, w10, #2
	ldr q2, [x19, #96]
	ldr q23, [x19, #576]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q24, [x19, #560]
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	ldr q25, [x19, #608]
	add w12, w10, #4
	ldr q4, [x19, #96]
	trn1 v26.2d, v21.2d, v22.2d
	mov v4.s[0], w12
	add w12, w10, #5
	trn2 v27.2d, v21.2d, v22.2d
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	eor v26.16b, v26.16b, v27.16b
	add w12, w10, #6
	ldr q6, [x19, #96]
	pmull v28.1q, v21.1d, v23.1d
	mov v6.s[0], w12
	add w12, w10, #7
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x15, #0]
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
	eor v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #16]
	eor v19.16b, v21.16b, v22.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q21, [x9, #48]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q22, [x9, #64]
	ldr q30, [x15, #32]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q23, [x19, #544]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q24, [x19, #528]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #624]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #48]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v26.16b, v26.16b, v27.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x15, #64]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #80]
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q21, [x9, #80]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q30, [x15, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q22, [x9, #96]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #512]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #496]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q25, [x19, #640]
	ldr q30, [x15, #112]
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
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #128]
	pmull2 v21.1q, v21.2d, v23.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x15, #144]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #112]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #160]
	ext v21.16b, v21.16b, v21.16b, #8
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #0]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v22.16b, v22.16b, v16.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q23, [x19, #480]
	ldr q30, [x15, #176]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q24, [x19, #592]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q25, [x19, #656]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #192]
	eor v26.16b, v26.16b, v27.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v22.1q, v22.2d, v24.2d
	ldr q30, [x15, #208]
	aese v0.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #224]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #128]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	pmull v26.1q, v19.1d, v17.1d
	ldr q31, [x9, #144]
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
	cbnz x11, 221b
	b 220f
219:
220:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
	b 218f
217:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
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
	ldr q30, [x15, #160]
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
	ldr q30, [x15, #176]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #192]
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
	cbz x11, 222f
224:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	ext v22.16b, v22.16b, v22.16b, #8
	add w12, w10, #2
	ldr q2, [x19, #96]
	ldr q23, [x19, #576]
	mov v2.s[0], w12
	ldr q24, [x19, #560]
	add w12, w10, #3
	ldr q3, [x19, #96]
	ldr q25, [x19, #608]
	mov v3.s[0], w12
	add w12, w10, #4
	trn1 v26.2d, v21.2d, v22.2d
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	trn2 v27.2d, v21.2d, v22.2d
	add w12, w10, #5
	eor v26.16b, v26.16b, v27.16b
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	pmull v28.1q, v21.1d, v23.1d
	add w12, w10, #6
	ldr q6, [x19, #96]
	pmull2 v21.1q, v21.2d, v23.2d
	mov v6.s[0], w12
	add w12, w10, #7
	pmull v29.1q, v22.1d, v24.1d
	ldr q7, [x19, #96]
	pmull2 v22.1q, v22.2d, v24.2d
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	eor v18.16b, v28.16b, v29.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	eor v19.16b, v21.16b, v22.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v20.16b, v27.16b, v26.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #16]
	ldr q21, [x9, #48]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q22, [x9, #64]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q23, [x19, #544]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #32]
	ldr q24, [x19, #528]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q25, [x19, #624]
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
	ldr q30, [x15, #48]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #64]
	pmull2 v26.1q, v26.2d, v25.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q21, [x9, #80]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q30, [x15, #80]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q22, [x9, #96]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #512]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #496]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q25, [x19, #640]
	ldr q30, [x15, #96]
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
	eor v26.16b, v26.16b, v27.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull2 v21.1q, v21.2d, v23.2d
	ldr q30, [x15, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	pmull2 v22.1q, v22.2d, v24.2d
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
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q30, [x15, #128]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q21, [x9, #112]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q22, [x9, #0]
	ldr q30, [x15, #144]
	ext v22.16b, v22.16b, v22.16b, #8
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v22.16b, v22.16b, v16.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q23, [x19, #480]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #592]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ldr q25, [x19, #656]
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #160]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	eor v26.16b, v26.16b, v27.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #176]
	pmull v29.1q, v22.1d, v24.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v4.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #192]
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q31, [x9, #128]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #144]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	ldr q31, [x9, #160]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #176]
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	ldr q31, [x9, #192]
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
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
	cbnz x11, 224b
	b 223f
222:
223:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
218:
	b 216f
215:
	add w12, w10, #0
	ldr q0, [x19, #96]
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q1, [x19, #96]
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q2, [x19, #96]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q3, [x19, #96]
	mov v3.s[0], w12
	add w12, w10, #4
	ldr q4, [x19, #96]
	mov v4.s[0], w12
	add w12, w10, #5
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	add w12, w10, #6
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	add w12, w10, #7
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	ldr q30, [x15, #0]
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
	ldr q30, [x15, #16]
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
	ldr q30, [x15, #32]
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
	ldr q30, [x15, #48]
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
	ldr q30, [x15, #64]
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
	ldr q30, [x15, #80]
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
	ldr q30, [x15, #96]
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
	ldr q30, [x15, #112]
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
	ldr q30, [x15, #128]
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
	ldr q30, [x15, #144]
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	aese v2.16b, v30.16b
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	aese v5.16b, v30.16b
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	ldr q30, [x15, #160]
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
	cbz x11, 225f
227:
	add w12, w10, #0
	ldr q21, [x9, #16]
	ldr q0, [x19, #96]
	ext v21.16b, v21.16b, v21.16b, #8
	mov v0.s[0], w12
	add w12, w10, #1
	ldr q22, [x9, #32]
	ldr q1, [x19, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	mov v1.s[0], w12
	add w12, w10, #2
	ldr q23, [x19, #576]
	ldr q2, [x19, #96]
	ldr q24, [x19, #560]
	mov v2.s[0], w12
	add w12, w10, #3
	ldr q25, [x19, #608]
	ldr q3, [x19, #96]
	trn1 v26.2d, v21.2d, v22.2d
	mov v3.s[0], w12
	add w12, w10, #4
	trn2 v27.2d, v21.2d, v22.2d
	ldr q4, [x19, #96]
	eor v26.16b, v26.16b, v27.16b
	mov v4.s[0], w12
	add w12, w10, #5
	pmull v28.1q, v21.1d, v23.1d
	ldr q5, [x19, #96]
	mov v5.s[0], w12
	pmull2 v21.1q, v21.2d, v23.2d
	add w12, w10, #6
	pmull v29.1q, v22.1d, v24.1d
	ldr q6, [x19, #96]
	mov v6.s[0], w12
	pmull2 v22.1q, v22.2d, v24.2d
	add w12, w10, #7
	pmull v27.1q, v26.1d, v25.1d
	ldr q7, [x19, #96]
	mov v7.s[0], w12
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x15, #0]
	eor v18.16b, v28.16b, v29.16b
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	eor v19.16b, v21.16b, v22.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v20.16b, v27.16b, v26.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q21, [x9, #48]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q22, [x9, #64]
	ldr q30, [x15, #16]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q23, [x19, #544]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q24, [x19, #528]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q25, [x19, #624]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	trn2 v27.2d, v21.2d, v22.2d
	ldr q30, [x15, #32]
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
	pmull2 v21.1q, v21.2d, v23.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #48]
	pmull v27.1q, v26.1d, v25.1d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v26.1q, v26.2d, v25.2d
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
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
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q21, [x9, #80]
	ldr q30, [x15, #64]
	ext v21.16b, v21.16b, v21.16b, #8
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	ldr q22, [x9, #96]
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	ldr q23, [x19, #512]
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ldr q24, [x19, #496]
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q25, [x19, #640]
	ldr q30, [x15, #80]
	trn1 v26.2d, v21.2d, v22.2d
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	eor v26.16b, v26.16b, v27.16b
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	pmull v28.1q, v21.1d, v23.1d
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	pmull v29.1q, v22.1d, v24.1d
	ldr q30, [x15, #96]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	pmull2 v22.1q, v22.2d, v24.2d
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
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q30, [x15, #112]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q21, [x9, #112]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ext v21.16b, v21.16b, v21.16b, #8
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	ldr q22, [x9, #0]
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	ext v22.16b, v22.16b, v22.16b, #8
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	eor v22.16b, v22.16b, v16.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	ldr q30, [x15, #128]
	ldr q23, [x19, #480]
	aese v0.16b, v30.16b
	aesmc v0.16b, v0.16b
	ldr q24, [x19, #592]
	aese v1.16b, v30.16b
	aesmc v1.16b, v1.16b
	aese v2.16b, v30.16b
	aesmc v2.16b, v2.16b
	ldr q25, [x19, #656]
	aese v3.16b, v30.16b
	aesmc v3.16b, v3.16b
	trn1 v26.2d, v21.2d, v22.2d
	aese v4.16b, v30.16b
	aesmc v4.16b, v4.16b
	aese v5.16b, v30.16b
	aesmc v5.16b, v5.16b
	trn2 v27.2d, v21.2d, v22.2d
	aese v6.16b, v30.16b
	aesmc v6.16b, v6.16b
	aese v7.16b, v30.16b
	aesmc v7.16b, v7.16b
	eor v26.16b, v26.16b, v27.16b
	ldr q30, [x15, #144]
	pmull v28.1q, v21.1d, v23.1d
	aese v0.16b, v30.16b
	aese v1.16b, v30.16b
	pmull2 v21.1q, v21.2d, v23.2d
	aese v2.16b, v30.16b
	pmull v29.1q, v22.1d, v24.1d
	aese v3.16b, v30.16b
	aese v4.16b, v30.16b
	pmull2 v22.1q, v22.2d, v24.2d
	aese v5.16b, v30.16b
	pmull v27.1q, v26.1d, v25.1d
	aese v6.16b, v30.16b
	aese v7.16b, v30.16b
	pmull2 v26.1q, v26.2d, v25.2d
	ldr q30, [x15, #160]
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	ldr q31, [x9, #128]
	eor3 v0.16b, v0.16b, v31.16b, v30.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	ldr q31, [x9, #144]
	eor3 v1.16b, v1.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q31, [x9, #160]
	pmull v26.1q, v19.1d, v17.1d
	eor3 v2.16b, v2.16b, v31.16b, v30.16b
	ldr q31, [x9, #176]
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v3.16b, v3.16b, v31.16b, v30.16b
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	ldr q31, [x9, #192]
	eor3 v4.16b, v4.16b, v31.16b, v30.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
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
	cbnz x11, 227b
	b 226f
225:
226:
	ldr q21, [x9, #16]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #32]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #576]
	ldr q24, [x19, #560]
	ldr q25, [x19, #608]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #64]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #544]
	ldr q24, [x19, #528]
	ldr q25, [x19, #624]
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
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #96]
	ext v22.16b, v22.16b, v22.16b, #8
	ldr q23, [x19, #512]
	ldr q24, [x19, #496]
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
	eor3 v18.16b, v18.16b, v28.16b, v29.16b
	eor3 v19.16b, v19.16b, v21.16b, v22.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	ldr q21, [x9, #112]
	ext v21.16b, v21.16b, v21.16b, #8
	ldr q22, [x9, #0]
	ext v22.16b, v22.16b, v22.16b, #8
	eor v22.16b, v22.16b, v16.16b
	ldr q23, [x19, #480]
	ldr q24, [x19, #592]
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
	pmull v26.1q, v19.1d, v17.1d
	ext v27.16b, v19.16b, v19.16b, #8
	eor3 v27.16b, v27.16b, v19.16b, v18.16b
	eor3 v20.16b, v20.16b, v27.16b, v26.16b
	pmull v26.1q, v20.1d, v17.1d
	ext v18.16b, v18.16b, v18.16b, #8
	ext v26.16b, v26.16b, v26.16b, #8
	eor3 v16.16b, v18.16b, v20.16b, v26.16b
	add x9, x9, #128
216:
	str w10, [x19, #96]
	rev64 v16.16b, v16.16b
	str q16, [x19, #80]
	b 214f
213:
214:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 228f
230:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32_aes}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 230b
	b 229f
228:
229:
	cbz x28, 231f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
233:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 233b
	b 232f
231:
232:
	lsr x9, x26, #7
	lsl x9, x9, #7
	add x27, x25, x9
	sub x28, x26, x9
	lsr x9, x28, #4
	cbz x9, 234f
236:
	lsr x10, x28, #10
	cbz x10, 237f
	movz x10, #64, lsl #0
	b 238f
237:
	lsr x10, x28, #4
238:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
239:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 239b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	cbnz x9, 236b
	b 235f
234:
235:
	cbz x28, 240f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
242:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 242b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 243f
	movz x10, #64, lsl #0
	b 244f
243:
	lsr x10, x28, #4
244:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
245:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 245b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	b 241f
240:
241:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 246f
	movz x10, #64, lsl #0
	b 247f
246:
	lsr x10, x28, #4
247:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
248:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 248b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash_aes}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32_aes}
	ldr x9, [x19, #0]
	ldr x10, [x19, #224]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #232]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x27, #1, lsl #0
	sub x27, x27, x10
	movz x9, #0, lsl #0
	sub x11, x9, x27
	add x12, x25, #0
	dup v16.16b, w11
	lsr x14, x26, #4
	lsl x9, x14, #4
	sub x13, x26, x9
	cbz x14, 249f
251:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 251b
	b 250f
249:
250:
	cbz x13, 252f
254:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 254b
	b 253f
252:
253:
	add x0, x27, #0
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
	add sp, sp, #3824
	ret
	.arch_extension noaes
	.arch_extension nosha3
	.p2align 6

vg_aes_gcm_siv_seal:
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	lsr x10, x28, #10
	cbz x10, 24f
	movz x10, #64, lsl #0
	b 25f
24:
	lsr x10, x28, #4
25:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
26:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 26b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 27f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
29:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 29b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	b 28f
27:
28:
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	cbz x9, 213f
215:
	lsr x10, x28, #10
	cbz x10, 216f
	movz x10, #64, lsl #0
	b 217f
216:
	lsr x10, x28, #4
217:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
218:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 218b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	cbnz x9, 215b
	b 214f
213:
214:
	cbz x28, 219f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
221:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 221b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 222f
	movz x10, #64, lsl #0
	b 223f
222:
	lsr x10, x28, #4
223:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
224:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 224b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	b 220f
219:
220:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 225f
	movz x10, #64, lsl #0
	b 226f
225:
	lsr x10, x28, #4
226:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
227:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 227b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #0]
	str x9, [x19, #8]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #0
	bl {vg_aes_ctr32}
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	cbz x9, 228f
230:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 230b
	b 229f
228:
229:
	cbz x28, 231f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
233:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 233b
	b 232f
231:
232:
	ldr x9, [x19, #216]
	ldr x10, [x19, #0]
	str x10, [x9, #0]
	ldr x10, [x19, #8]
	str x10, [x9, #8]
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
	add sp, sp, #3824
	ret
	.p2align 6

vg_aes_gcm_siv_open:
	sub sp, sp, #3824
	add x16, sp, #0
	add x17, sp, #16
	str x17, [x16, #0]
	ldr x9, [sp, #0]
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
	add x20, x2, #0
	add x21, x0, #0
	add x22, x1, #0
	add x23, x3, #0
	add x24, x4, #0
	add x25, x5, #0
	add x26, x6, #0
	str x7, [x19, #216]
	ldr x9, [x19, #216]
	ldr x10, [x9, #0]
	str x10, [x19, #0]
	ldr x10, [x9, #8]
	str x10, [x19, #8]
	movz x27, #0, lsl #0
20:
	ldr w9, [x20, #0]
	ldr w10, [x20, #4]
	ldr w11, [x20, #8]
	str w27, [x19, #112]
	str w9, [x19, #116]
	str w10, [x19, #120]
	str w11, [x19, #124]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x21, #0
	add x1, x22, #0
	add x2, x19, #112
	add x3, x19, #224
	movz x4, #1, lsl #0
	add x5, x19, #1760
	bl {vg_aes_ctr32}
	ldr x9, [x19, #224]
	lsl x10, x27, #3
	add x10, x19, x10
	str x9, [x10, #16]
	add x27, x27, #1
	lsr x10, x22, #1
	sub x10, x10, #1
	sub x10, x10, x27
	cbnz x10, 20b
	add x0, x19, #32
	sub x1, x22, #6
	lsl x1, x1, #2
	add x2, x19, #240
	add x3, x19, #1760
	bl {vg_aes_expand_key_scratch}
	ldr x9, [x19, #16]
	ldr x10, [x19, #24]
	movz x11, #1, lsl #0
	and x12, x9, x11
	movz x13, #0, lsl #0
	sub x12, x13, x12
	lsr x9, x9, #1
	and x13, x10, x11
	ror x13, x13, #1
	orr x9, x9, x13
	lsr x10, x10, #1
	movz x11, #57600, lsl #48
	and x11, x11, x12
	eor x10, x10, x11
	rev x10, x10
	rev x9, x9
	str x10, [x19, #64]
	str x9, [x19, #72]
	movz x9, #0, lsl #0
	str x9, [x19, #80]
	str x9, [x19, #88]
	ldr x9, [x19, #0]
	str x9, [x19, #96]
	ldr x9, [x19, #8]
	movz x10, #32768, lsl #48
	orr x9, x9, x10
	str x9, [x19, #104]
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	cbz x9, 21f
23:
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x27, #0
	bl {vg_aes_ctr32}
	ldr w9, [x19, #96]
	add w9, w9, #1
	str w9, [x19, #96]
	add x27, x27, #16
	sub x28, x28, #16
	lsr x9, x28, #4
	cbnz x9, 23b
	b 22f
21:
22:
	cbz x28, 24f
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32}
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
26:
	ldrb w14, [x12, #0]
	ldrb w15, [x11, #0]
	eor w14, w14, w15
	strb w14, [x12, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 26b
	b 25f
24:
25:
	add x27, x23, #0
	add x28, x24, #0
	lsr x9, x28, #4
	cbz x9, 27f
29:
	lsr x10, x28, #10
	cbz x10, 210f
	movz x10, #64, lsl #0
	b 211f
210:
	lsr x10, x28, #4
211:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
212:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 212b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	cbnz x9, 29b
	b 28f
27:
28:
	cbz x28, 213f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
215:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 215b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 216f
	movz x10, #64, lsl #0
	b 217f
216:
	lsr x10, x28, #4
217:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
218:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 218b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	b 214f
213:
214:
	add x27, x25, #0
	add x28, x26, #0
	lsr x9, x28, #4
	cbz x9, 219f
221:
	lsr x10, x28, #10
	cbz x10, 222f
	movz x10, #64, lsl #0
	b 223f
222:
	lsr x10, x28, #4
223:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
224:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 224b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	cbnz x9, 221b
	b 220f
219:
220:
	cbz x28, 225f
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x11, x19, #224
	add x12, x27, #0
	add x13, x28, #0
227:
	ldrb w14, [x12, #0]
	strb w14, [x11, #0]
	add x12, x12, #1
	add x11, x11, #1
	sub x13, x13, #1
	cbnz x13, 227b
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 228f
	movz x10, #64, lsl #0
	b 229f
228:
	lsr x10, x28, #4
229:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
230:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 230b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	b 226f
225:
226:
	lsl x9, x24, #3
	str x9, [x19, #224]
	lsl x9, x26, #3
	str x9, [x19, #232]
	add x27, x19, #224
	movz x28, #16, lsl #0
	lsr x10, x28, #10
	cbz x10, 231f
	movz x10, #64, lsl #0
	b 232f
231:
	lsr x10, x28, #4
232:
	add x11, x27, #0
	add x14, x19, #480
	add x15, x10, #0
233:
	ldr x12, [x11, #0]
	ldr x13, [x11, #8]
	rev x12, x12
	rev x13, x13
	str x13, [x14, #0]
	str x12, [x14, #8]
	add x11, x11, #16
	add x14, x14, #16
	sub x15, x15, #1
	cbnz x15, 233b
	lsl x9, x10, #4
	add x27, x27, x9
	sub x28, x28, x9
	add x0, x19, #64
	add x1, x19, #80
	add x4, x19, #1504
	add x2, x19, #480
	add x3, x10, #0
	bl {vg_ghash}
	lsr x9, x28, #4
	ldr x9, [x19, #88]
	rev x9, x9
	ldr x10, [x19, #80]
	rev x10, x10
	ldr x11, [x20, #0]
	eor x9, x9, x11
	ldr w11, [x20, #8]
	eor x10, x10, x11
	lsl x10, x10, #1
	lsr x10, x10, #1
	str x9, [x19, #96]
	str x10, [x19, #104]
	ldr x9, [x19, #96]
	str x9, [x19, #112]
	ldr x9, [x19, #104]
	str x9, [x19, #120]
	movz x9, #0, lsl #0
	str x9, [x19, #224]
	str x9, [x19, #232]
	add x0, x19, #240
	add x1, x22, #0
	add x2, x19, #112
	movz x4, #1, lsl #0
	add x5, x19, #1760
	add x3, x19, #224
	bl {vg_aes_ctr32}
	ldr x9, [x19, #0]
	ldr x10, [x19, #224]
	eor x9, x9, x10
	ldr x10, [x19, #8]
	ldr x11, [x19, #232]
	eor x10, x10, x11
	orr x9, x9, x10
	movz x11, #0, lsl #0
	sub x12, x11, #1
	adds x9, x9, x12
	adcs x10, x11, x11
	movz x27, #1, lsl #0
	sub x27, x27, x10
	movz x9, #0, lsl #0
	sub x11, x9, x27
	add x12, x25, #0
	dup v16.16b, w11
	lsr x14, x26, #4
	lsl x9, x14, #4
	sub x13, x26, x9
	cbz x14, 234f
236:
	ldr q17, [x12, #0]
	and v17.16b, v17.16b, v16.16b
	str q17, [x12, #0]
	add x12, x12, #16
	sub x14, x14, #1
	cbnz x14, 236b
	b 235f
234:
235:
	cbz x13, 237f
239:
	ldrb w14, [x12, #0]
	and w14, w14, w11
	strb w14, [x12, #0]
	add x12, x12, #1
	sub x13, x13, #1
	cbnz x13, 239b
	b 238f
237:
238:
	add x0, x27, #0
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
	add sp, sp, #3824
	ret
	.p2align 6
