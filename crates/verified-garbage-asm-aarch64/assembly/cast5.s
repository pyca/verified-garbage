// The functions of `src/cast5.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_expand_key:
	movz x9, #0, lsl #0
	str x9, [x3, #16]
	str x9, [x3, #24]
	add x4, x3, #16
20:
	ldrb w9, [x0, #0]
	strb w9, [x4, #0]
	add x0, x0, #1
	add x4, x4, #1
	sub x1, x1, #1
	cbnz x1, 20b
	movz x1, #2, lsl #0
	add x15, x30, #0
	movz x6, #64, lsl #0
	dup v2.16b, w6
	movz x6, #128, lsl #0
	dup v3.16b, w6
21:
	ldrb w10, [x3, #29]
	mov v16.b[4], w10
	ldrb w10, [x3, #31]
	mov v17.b[4], w10
	ldrb w10, [x3, #28]
	mov v18.b[4], w10
	ldrb w10, [x3, #30]
	mov v19.b[4], w10
	ldrb w10, [x3, #25]
	mov v16.b[5], w10
	ldrb w10, [x3, #27]
	mov v17.b[5], w10
	ldrb w10, [x3, #24]
	mov v18.b[5], w10
	ldrb w10, [x3, #26]
	mov v19.b[5], w10
	bl {vg_cast5_key_sboxes}
	str q7, [x3, #48]
	umov w0, v5.s[0]
	ldr w10, [x3, #56]
	eor w0, w0, w10
	ldr w10, [x3, #16]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #32]
	ldrb w10, [x3, #32]
	mov v16.b[4], w10
	ldrb w10, [x3, #34]
	mov v17.b[4], w10
	ldrb w10, [x3, #33]
	mov v18.b[4], w10
	ldrb w10, [x3, #35]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #60]
	eor w0, w0, w10
	ldr w10, [x3, #24]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #36]
	ldrb w10, [x3, #39]
	mov v16.b[4], w10
	ldrb w10, [x3, #38]
	mov v17.b[4], w10
	ldrb w10, [x3, #37]
	mov v18.b[4], w10
	ldrb w10, [x3, #36]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #48]
	eor w0, w0, w10
	ldr w10, [x3, #28]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #40]
	ldrb w10, [x3, #42]
	mov v16.b[4], w10
	ldrb w10, [x3, #41]
	mov v17.b[4], w10
	ldrb w10, [x3, #43]
	mov v18.b[4], w10
	ldrb w10, [x3, #40]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #52]
	eor w0, w0, w10
	ldr w10, [x3, #20]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #44]
	ldrb w10, [x3, #37]
	mov v16.b[4], w10
	ldrb w10, [x3, #39]
	mov v17.b[4], w10
	ldrb w10, [x3, #36]
	mov v18.b[4], w10
	ldrb w10, [x3, #38]
	mov v19.b[4], w10
	ldrb w10, [x3, #33]
	mov v16.b[5], w10
	ldrb w10, [x3, #35]
	mov v17.b[5], w10
	ldrb w10, [x3, #32]
	mov v18.b[5], w10
	ldrb w10, [x3, #34]
	mov v19.b[5], w10
	ldrb w10, [x3, #40]
	mov v16.b[0], w10
	ldrb w10, [x3, #41]
	mov v17.b[0], w10
	ldrb w10, [x3, #39]
	mov v18.b[0], w10
	ldrb w10, [x3, #38]
	mov v19.b[0], w10
	ldrb w10, [x3, #42]
	mov v16.b[1], w10
	ldrb w10, [x3, #43]
	mov v17.b[1], w10
	ldrb w10, [x3, #37]
	mov v18.b[1], w10
	ldrb w10, [x3, #36]
	mov v19.b[1], w10
	ldrb w10, [x3, #44]
	mov v16.b[2], w10
	ldrb w10, [x3, #45]
	mov v17.b[2], w10
	ldrb w10, [x3, #35]
	mov v18.b[2], w10
	ldrb w10, [x3, #34]
	mov v19.b[2], w10
	ldrb w10, [x3, #46]
	mov v16.b[3], w10
	ldrb w10, [x3, #47]
	mov v17.b[3], w10
	ldrb w10, [x3, #33]
	mov v18.b[3], w10
	ldrb w10, [x3, #32]
	mov v19.b[3], w10
	ldrb w10, [x3, #34]
	mov v16.b[8], w10
	ldrb w10, [x3, #38]
	mov v17.b[8], w10
	ldrb w10, [x3, #41]
	mov v18.b[8], w10
	ldrb w10, [x3, #44]
	mov v19.b[8], w10
	bl {vg_cast5_key_sboxes}
	str q7, [x3, #48]
	eor v4.16b, v4.16b, v6.16b
	str q4, [x2, #0]
	umov w0, v5.s[0]
	ldr w10, [x3, #56]
	eor w0, w0, w10
	ldr w10, [x3, #40]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #16]
	ldrb w10, [x3, #16]
	mov v16.b[4], w10
	ldrb w10, [x3, #18]
	mov v17.b[4], w10
	ldrb w10, [x3, #17]
	mov v18.b[4], w10
	ldrb w10, [x3, #19]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #60]
	eor w0, w0, w10
	ldr w10, [x3, #32]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #20]
	ldrb w10, [x3, #23]
	mov v16.b[4], w10
	ldrb w10, [x3, #22]
	mov v17.b[4], w10
	ldrb w10, [x3, #21]
	mov v18.b[4], w10
	ldrb w10, [x3, #20]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #48]
	eor w0, w0, w10
	ldr w10, [x3, #36]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #24]
	ldrb w10, [x3, #26]
	mov v16.b[4], w10
	ldrb w10, [x3, #25]
	mov v17.b[4], w10
	ldrb w10, [x3, #27]
	mov v18.b[4], w10
	ldrb w10, [x3, #24]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #52]
	eor w0, w0, w10
	ldr w10, [x3, #44]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #28]
	ldrb w10, [x3, #29]
	mov v16.b[4], w10
	ldrb w10, [x3, #31]
	mov v17.b[4], w10
	ldrb w10, [x3, #28]
	mov v18.b[4], w10
	ldrb w10, [x3, #30]
	mov v19.b[4], w10
	ldrb w10, [x3, #25]
	mov v16.b[5], w10
	ldrb w10, [x3, #27]
	mov v17.b[5], w10
	ldrb w10, [x3, #24]
	mov v18.b[5], w10
	ldrb w10, [x3, #26]
	mov v19.b[5], w10
	ldrb w10, [x3, #19]
	mov v16.b[0], w10
	ldrb w10, [x3, #18]
	mov v17.b[0], w10
	ldrb w10, [x3, #28]
	mov v18.b[0], w10
	ldrb w10, [x3, #29]
	mov v19.b[0], w10
	ldrb w10, [x3, #17]
	mov v16.b[1], w10
	ldrb w10, [x3, #16]
	mov v17.b[1], w10
	ldrb w10, [x3, #30]
	mov v18.b[1], w10
	ldrb w10, [x3, #31]
	mov v19.b[1], w10
	ldrb w10, [x3, #23]
	mov v16.b[2], w10
	ldrb w10, [x3, #22]
	mov v17.b[2], w10
	ldrb w10, [x3, #24]
	mov v18.b[2], w10
	ldrb w10, [x3, #25]
	mov v19.b[2], w10
	ldrb w10, [x3, #21]
	mov v16.b[3], w10
	ldrb w10, [x3, #20]
	mov v17.b[3], w10
	ldrb w10, [x3, #26]
	mov v18.b[3], w10
	ldrb w10, [x3, #27]
	mov v19.b[3], w10
	ldrb w10, [x3, #24]
	mov v16.b[8], w10
	ldrb w10, [x3, #29]
	mov v17.b[8], w10
	ldrb w10, [x3, #19]
	mov v18.b[8], w10
	ldrb w10, [x3, #23]
	mov v19.b[8], w10
	bl {vg_cast5_key_sboxes}
	str q7, [x3, #48]
	eor v4.16b, v4.16b, v6.16b
	str q4, [x2, #16]
	umov w0, v5.s[0]
	ldr w10, [x3, #56]
	eor w0, w0, w10
	ldr w10, [x3, #16]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #32]
	ldrb w10, [x3, #32]
	mov v16.b[4], w10
	ldrb w10, [x3, #34]
	mov v17.b[4], w10
	ldrb w10, [x3, #33]
	mov v18.b[4], w10
	ldrb w10, [x3, #35]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #60]
	eor w0, w0, w10
	ldr w10, [x3, #24]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #36]
	ldrb w10, [x3, #39]
	mov v16.b[4], w10
	ldrb w10, [x3, #38]
	mov v17.b[4], w10
	ldrb w10, [x3, #37]
	mov v18.b[4], w10
	ldrb w10, [x3, #36]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #48]
	eor w0, w0, w10
	ldr w10, [x3, #28]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #40]
	ldrb w10, [x3, #42]
	mov v16.b[4], w10
	ldrb w10, [x3, #41]
	mov v17.b[4], w10
	ldrb w10, [x3, #43]
	mov v18.b[4], w10
	ldrb w10, [x3, #40]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #52]
	eor w0, w0, w10
	ldr w10, [x3, #20]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #44]
	ldrb w10, [x3, #37]
	mov v16.b[4], w10
	ldrb w10, [x3, #39]
	mov v17.b[4], w10
	ldrb w10, [x3, #36]
	mov v18.b[4], w10
	ldrb w10, [x3, #38]
	mov v19.b[4], w10
	ldrb w10, [x3, #33]
	mov v16.b[5], w10
	ldrb w10, [x3, #35]
	mov v17.b[5], w10
	ldrb w10, [x3, #32]
	mov v18.b[5], w10
	ldrb w10, [x3, #34]
	mov v19.b[5], w10
	ldrb w10, [x3, #35]
	mov v16.b[0], w10
	ldrb w10, [x3, #34]
	mov v17.b[0], w10
	ldrb w10, [x3, #44]
	mov v18.b[0], w10
	ldrb w10, [x3, #45]
	mov v19.b[0], w10
	ldrb w10, [x3, #33]
	mov v16.b[1], w10
	ldrb w10, [x3, #32]
	mov v17.b[1], w10
	ldrb w10, [x3, #46]
	mov v18.b[1], w10
	ldrb w10, [x3, #47]
	mov v19.b[1], w10
	ldrb w10, [x3, #39]
	mov v16.b[2], w10
	ldrb w10, [x3, #38]
	mov v17.b[2], w10
	ldrb w10, [x3, #40]
	mov v18.b[2], w10
	ldrb w10, [x3, #41]
	mov v19.b[2], w10
	ldrb w10, [x3, #37]
	mov v16.b[3], w10
	ldrb w10, [x3, #36]
	mov v17.b[3], w10
	ldrb w10, [x3, #42]
	mov v18.b[3], w10
	ldrb w10, [x3, #43]
	mov v19.b[3], w10
	ldrb w10, [x3, #41]
	mov v16.b[8], w10
	ldrb w10, [x3, #44]
	mov v17.b[8], w10
	ldrb w10, [x3, #34]
	mov v18.b[8], w10
	ldrb w10, [x3, #38]
	mov v19.b[8], w10
	bl {vg_cast5_key_sboxes}
	str q7, [x3, #48]
	eor v4.16b, v4.16b, v6.16b
	str q4, [x2, #32]
	umov w0, v5.s[0]
	ldr w10, [x3, #56]
	eor w0, w0, w10
	ldr w10, [x3, #40]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #16]
	ldrb w10, [x3, #16]
	mov v16.b[4], w10
	ldrb w10, [x3, #18]
	mov v17.b[4], w10
	ldrb w10, [x3, #17]
	mov v18.b[4], w10
	ldrb w10, [x3, #19]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #60]
	eor w0, w0, w10
	ldr w10, [x3, #32]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #20]
	ldrb w10, [x3, #23]
	mov v16.b[4], w10
	ldrb w10, [x3, #22]
	mov v17.b[4], w10
	ldrb w10, [x3, #21]
	mov v18.b[4], w10
	ldrb w10, [x3, #20]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #48]
	eor w0, w0, w10
	ldr w10, [x3, #36]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #24]
	ldrb w10, [x3, #26]
	mov v16.b[4], w10
	ldrb w10, [x3, #25]
	mov v17.b[4], w10
	ldrb w10, [x3, #27]
	mov v18.b[4], w10
	ldrb w10, [x3, #24]
	mov v19.b[4], w10
	bl {vg_cast5_key_sboxes}
	umov w0, v5.s[0]
	ldr w10, [x3, #52]
	eor w0, w0, w10
	ldr w10, [x3, #44]
	rev w10, w10
	eor w0, w0, w10
	rev w10, w0
	str w10, [x3, #28]
	ldrb w10, [x3, #24]
	mov v16.b[0], w10
	ldrb w10, [x3, #25]
	mov v17.b[0], w10
	ldrb w10, [x3, #23]
	mov v18.b[0], w10
	ldrb w10, [x3, #22]
	mov v19.b[0], w10
	ldrb w10, [x3, #26]
	mov v16.b[1], w10
	ldrb w10, [x3, #27]
	mov v17.b[1], w10
	ldrb w10, [x3, #21]
	mov v18.b[1], w10
	ldrb w10, [x3, #20]
	mov v19.b[1], w10
	ldrb w10, [x3, #28]
	mov v16.b[2], w10
	ldrb w10, [x3, #29]
	mov v17.b[2], w10
	ldrb w10, [x3, #19]
	mov v18.b[2], w10
	ldrb w10, [x3, #18]
	mov v19.b[2], w10
	ldrb w10, [x3, #30]
	mov v16.b[3], w10
	ldrb w10, [x3, #31]
	mov v17.b[3], w10
	ldrb w10, [x3, #17]
	mov v18.b[3], w10
	ldrb w10, [x3, #16]
	mov v19.b[3], w10
	ldrb w10, [x3, #19]
	mov v16.b[8], w10
	ldrb w10, [x3, #23]
	mov v17.b[8], w10
	ldrb w10, [x3, #24]
	mov v18.b[8], w10
	ldrb w10, [x3, #29]
	mov v19.b[8], w10
	bl {vg_cast5_key_sboxes}
	eor v4.16b, v4.16b, v6.16b
	str q4, [x2, #48]
	add x2, x2, #64
	sub x1, x1, #1
	cbnz x1, 21b
	add x30, x15, #0
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
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
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x1, x1
	movz x0, #0, lsl #0
	ret
	.p2align 6

vg_cast5_ecb_encrypt:
	add x16, x1, #0
	add x1, x2, #0
	add x2, x3, #0
	add x3, x4, #0
	str q8, [x3, #128]
	str q9, [x3, #144]
	str q10, [x3, #160]
	str q11, [x3, #176]
	str q12, [x3, #192]
	str q13, [x3, #208]
	str q14, [x3, #224]
	str q15, [x3, #240]
	movz x6, #64, lsl #0
	dup v2.16b, w6
	movz x6, #128, lsl #0
	dup v3.16b, w6
	lsr x8, x2, #4
	cbz x8, 20f
22:
	add x4, x1, #0
	add x10, x30, #0
	add x14, x16, #0
	bl {vg_cast5_batch_encrypt}
	add x30, x10, #0
	add x1, x1, #128
	sub x2, x2, #16
	lsr x8, x2, #4
	cbnz x8, 22b
	b 21f
20:
21:
	cbz x2, 23f
	add x11, x1, #0
	add x12, x3, #0
	add x13, x2, #0
25:
	ldr x10, [x11, #0]
	str x10, [x12, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 25b
	add x4, x3, #0
	add x10, x30, #0
	add x14, x16, #0
	bl {vg_cast5_batch_encrypt}
	add x30, x10, #0
	add x11, x3, #0
	add x12, x1, #0
	add x13, x2, #0
26:
	ldr x10, [x11, #0]
	str x10, [x12, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 26b
	b 24f
23:
24:
	ldr q8, [x3, #128]
	ldr q9, [x3, #144]
	ldr q10, [x3, #160]
	ldr q11, [x3, #176]
	ldr q12, [x3, #192]
	ldr q13, [x3, #208]
	ldr q14, [x3, #224]
	ldr q15, [x3, #240]
	movz x6, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x13, #0, lsl #0
	movz x15, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
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
	tst x6, x6
	mov v8.d[1], x6
	mov v9.d[1], x6
	mov v10.d[1], x6
	mov v11.d[1], x6
	mov v12.d[1], x6
	mov v13.d[1], x6
	mov v14.d[1], x6
	mov v15.d[1], x6
	ret
	.p2align 6

vg_cast5_ecb_decrypt:
	add x16, x1, #0
	add x1, x2, #0
	add x2, x3, #0
	add x3, x4, #0
	str q8, [x3, #128]
	str q9, [x3, #144]
	str q10, [x3, #160]
	str q11, [x3, #176]
	str q12, [x3, #192]
	str q13, [x3, #208]
	str q14, [x3, #224]
	str q15, [x3, #240]
	movz x6, #64, lsl #0
	dup v2.16b, w6
	movz x6, #128, lsl #0
	dup v3.16b, w6
	lsr x8, x2, #4
	cbz x8, 20f
22:
	add x4, x1, #0
	add x10, x30, #0
	add x14, x16, #0
	bl {vg_cast5_batch_decrypt}
	add x30, x10, #0
	add x1, x1, #128
	sub x2, x2, #16
	lsr x8, x2, #4
	cbnz x8, 22b
	b 21f
20:
21:
	cbz x2, 23f
	add x11, x1, #0
	add x12, x3, #0
	add x13, x2, #0
25:
	ldr x10, [x11, #0]
	str x10, [x12, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 25b
	add x4, x3, #0
	add x10, x30, #0
	add x14, x16, #0
	bl {vg_cast5_batch_decrypt}
	add x30, x10, #0
	add x11, x3, #0
	add x12, x1, #0
	add x13, x2, #0
26:
	ldr x10, [x11, #0]
	str x10, [x12, #0]
	add x11, x11, #8
	add x12, x12, #8
	sub x13, x13, #1
	cbnz x13, 26b
	b 24f
23:
24:
	ldr q8, [x3, #128]
	ldr q9, [x3, #144]
	ldr q10, [x3, #160]
	ldr q11, [x3, #176]
	ldr q12, [x3, #192]
	ldr q13, [x3, #208]
	ldr q14, [x3, #224]
	ldr q15, [x3, #240]
	movz x6, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x13, #0, lsl #0
	movz x15, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
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
	tst x6, x6
	mov v8.d[1], x6
	mov v9.d[1], x6
	mov v10.d[1], x6
	mov v11.d[1], x6
	mov v12.d[1], x6
	mov v13.d[1], x6
	mov v14.d[1], x6
	mov v15.d[1], x6
	ret
	.p2align 6
