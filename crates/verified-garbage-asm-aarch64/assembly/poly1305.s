// The functions of `src/poly1305.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init:
	ldr x2, [x1, #0]
	ldr x3, [x1, #8]
	ldr x4, [x1, #16]
	ldr x5, [x1, #24]
	str x2, [x0, #24]
	str x3, [x0, #32]
	str x4, [x0, #40]
	str x5, [x0, #48]
	movz x2, #0, lsl #0
	str x2, [x0, #0]
	str x2, [x0, #8]
	str x2, [x0, #16]
	ret
	.p2align 6

vg_poly1305_blocks:
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	cbz x2, 20f
22:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x2, x2, #1
	cbnz x2, 22b
	b 21f
20:
21:
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	ret
	.p2align 6

vg_poly1305_update:
	sub sp, sp, #128
	add x4, sp, #0
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	movz x9, #15, lsl #0
	and x9, x1, x9
	cbz x9, 20f
	movz x10, #16, lsl #0
	sub x10, x10, x9
	lsr x11, x3, #4
	cbz x11, 22f
	b 23f
22:
	sub x12, x3, x10
	lsr x12, x12, #63
	cbz x12, 24f
	add x10, x3, #0
	b 25f
24:
25:
23:
	sub x3, x3, x10
	add x11, x0, x9
	add x9, x9, x10
	add x1, x2, #0
	cbz x10, 26f
28:
	ldrb w12, [x1, #0]
	strb w12, [x11, #56]
	add x1, x1, #1
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 28b
	b 27f
26:
27:
	add x2, x1, #0
	sub x12, x9, #16
	cbz x12, 29f
	b 210f
29:
	add x1, x0, #56
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
210:
	b 21f
20:
21:
	add x1, x2, #0
	lsr x2, x3, #4
	cbz x2, 211f
213:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x3, x3, #16
	lsr x2, x3, #4
	cbnz x2, 213b
	b 212f
211:
212:
	cbz x3, 214f
	add x10, x3, #0
	add x11, x0, #0
216:
	ldrb w12, [x1, #0]
	strb w12, [x11, #56]
	add x1, x1, #1
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 216b
	b 215f
214:
215:
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	add sp, sp, #128
	ret
	.p2align 6

vg_poly1305_update_neon:
	sub sp, sp, #128
	add x4, sp, #0
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	movz x9, #15, lsl #0
	and x9, x1, x9
	cbz x9, 20f
	movz x10, #16, lsl #0
	sub x10, x10, x9
	lsr x11, x3, #4
	cbz x11, 22f
	b 23f
22:
	sub x12, x3, x10
	lsr x12, x12, #63
	cbz x12, 24f
	add x10, x3, #0
	b 25f
24:
25:
23:
	sub x3, x3, x10
	add x11, x0, x9
	add x9, x9, x10
	add x1, x2, #0
	cbz x10, 26f
28:
	ldrb w12, [x1, #0]
	strb w12, [x11, #56]
	add x1, x1, #1
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 28b
	b 27f
26:
27:
	add x2, x1, #0
	sub x12, x9, #16
	cbz x12, 29f
	b 210f
29:
	add x1, x0, #56
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
210:
	b 21f
20:
21:
	lsr x9, x3, #7
	cbz x9, 211f
	movz x16, #65535, lsl #0
	movk x16, #1023, lsl #16
	umov x9, v8.d[0]
	str x9, [x0, #72]
	umov x9, v9.d[0]
	str x9, [x0, #80]
	umov x9, v10.d[0]
	str x9, [x0, #88]
	umov x9, v11.d[0]
	str x9, [x0, #96]
	umov x9, v12.d[0]
	str x9, [x0, #104]
	umov x9, v13.d[0]
	str x9, [x0, #112]
	umov x9, v14.d[0]
	str x9, [x0, #120]
	and x9, x4, x16
	lsr x10, x4, #26
	and x10, x10, x16
	lsr x11, x4, #52
	lsl x12, x5, #12
	orr x11, x11, x12
	and x11, x11, x16
	lsr x12, x5, #14
	and x12, x12, x16
	lsr x13, x5, #40
	lsl x14, x6, #24
	orr x13, x13, x14
	movi v0.2d, #0
	mov v0.d[0], x9
	movi v1.2d, #0
	mov v1.d[0], x10
	movi v2.2d, #0
	mov v2.d[0], x11
	movi v3.2d, #0
	mov v3.d[0], x12
	movi v4.2d, #0
	mov v4.d[0], x13
	add x4, x7, #0
	add x5, x8, #0
	movz x6, #0, lsl #0
	and x9, x4, x16
	lsr x10, x4, #26
	and x10, x10, x16
	lsr x11, x4, #52
	lsl x12, x5, #12
	orr x11, x11, x12
	and x11, x11, x16
	lsr x12, x5, #14
	and x12, x12, x16
	lsr x13, x5, #40
	lsl x14, x6, #24
	orr x13, x13, x14
	mov v28.s[3], w9
	mov v29.s[3], w10
	mov v30.s[3], w11
	mov v31.s[3], w12
	mov v7.s[3], w13
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	and x9, x4, x16
	lsr x10, x4, #26
	and x10, x10, x16
	lsr x11, x4, #52
	lsl x12, x5, #12
	orr x11, x11, x12
	and x11, x11, x16
	lsr x12, x5, #14
	and x12, x12, x16
	lsr x13, x5, #40
	lsl x14, x6, #24
	orr x13, x13, x14
	mov v8.s[2], w9
	mov v9.s[2], w10
	mov v10.s[2], w11
	mov v11.s[2], w12
	mov v12.s[2], w13
	mov v8.s[3], w9
	mov v9.s[3], w10
	mov v10.s[3], w11
	mov v11.s[3], w12
	mov v12.s[3], w13
	mov v28.s[2], w9
	mov v29.s[2], w10
	mov v30.s[2], w11
	mov v31.s[2], w12
	mov v7.s[2], w13
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	and x9, x4, x16
	lsr x10, x4, #26
	and x10, x10, x16
	lsr x11, x4, #52
	lsl x12, x5, #12
	orr x11, x11, x12
	and x11, x11, x16
	lsr x12, x5, #14
	and x12, x12, x16
	lsr x13, x5, #40
	lsl x14, x6, #24
	orr x13, x13, x14
	mov v28.s[1], w9
	mov v29.s[1], w10
	mov v30.s[1], w11
	mov v31.s[1], w12
	mov v7.s[1], w13
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	and x9, x4, x16
	lsr x10, x4, #26
	and x10, x10, x16
	lsr x11, x4, #52
	lsl x12, x5, #12
	orr x11, x11, x12
	and x11, x11, x16
	lsr x12, x5, #14
	and x12, x12, x16
	lsr x13, x5, #40
	lsl x14, x6, #24
	orr x13, x13, x14
	mov v8.s[0], w9
	mov v9.s[0], w10
	mov v10.s[0], w11
	mov v11.s[0], w12
	mov v12.s[0], w13
	mov v8.s[1], w9
	mov v9.s[1], w10
	mov v10.s[1], w11
	mov v11.s[1], w12
	mov v12.s[1], w13
	mov v28.s[0], w9
	mov v29.s[0], w10
	mov v30.s[0], w11
	mov v31.s[0], w12
	mov v7.s[0], w13
	shl v13.4s, v9.4s, #2
	add v13.4s, v13.4s, v9.4s
	shl v14.4s, v10.4s, #2
	add v14.4s, v14.4s, v10.4s
	shl v5.4s, v11.4s, #2
	add v5.4s, v5.4s, v11.4s
	shl v6.4s, v12.4s, #2
	add v6.4s, v6.4s, v12.4s
	dup v26.2d, x16
	movz x9, #256, lsl #16
	dup v27.2d, x9
	lsr x9, x3, #6
	sub x9, x9, #1
213:
	ldr q23, [x2, #32]
	ldr q24, [x2, #48]
	zip1 v21.2d, v23.2d, v24.2d
	zip2 v25.2d, v23.2d, v24.2d
	ushr v22.2d, v21.2d, #26
	ushr v23.2d, v21.2d, #52
	and v21.16b, v21.16b, v26.16b
	and v22.16b, v22.16b, v26.16b
	sli v23.2d, v25.2d, #12
	and v23.16b, v23.16b, v26.16b
	ushr v24.2d, v25.2d, #14
	and v24.16b, v24.16b, v26.16b
	ushr v25.2d, v25.2d, #40
	orr v25.16b, v25.16b, v27.16b
	uzp1 v21.4s, v21.4s, v21.4s
	uzp1 v22.4s, v22.4s, v22.4s
	uzp1 v23.4s, v23.4s, v23.4s
	uzp1 v24.4s, v24.4s, v24.4s
	uzp1 v25.4s, v25.4s, v25.4s
	umull2 v16.2d, v21.4s, v8.4s
	umull2 v17.2d, v21.4s, v9.4s
	umull2 v18.2d, v21.4s, v10.4s
	umull2 v19.2d, v21.4s, v11.4s
	umull2 v20.2d, v21.4s, v12.4s
	umlal2 v16.2d, v22.4s, v6.4s
	umlal2 v17.2d, v22.4s, v8.4s
	umlal2 v18.2d, v22.4s, v9.4s
	umlal2 v19.2d, v22.4s, v10.4s
	umlal2 v20.2d, v22.4s, v11.4s
	umlal2 v16.2d, v23.4s, v5.4s
	umlal2 v17.2d, v23.4s, v6.4s
	umlal2 v18.2d, v23.4s, v8.4s
	umlal2 v19.2d, v23.4s, v9.4s
	umlal2 v20.2d, v23.4s, v10.4s
	umlal2 v16.2d, v24.4s, v14.4s
	umlal2 v17.2d, v24.4s, v5.4s
	umlal2 v18.2d, v24.4s, v6.4s
	umlal2 v19.2d, v24.4s, v8.4s
	umlal2 v20.2d, v24.4s, v9.4s
	umlal2 v16.2d, v25.4s, v13.4s
	umlal2 v17.2d, v25.4s, v14.4s
	umlal2 v18.2d, v25.4s, v5.4s
	umlal2 v19.2d, v25.4s, v6.4s
	umlal2 v20.2d, v25.4s, v8.4s
	ldr q23, [x2, #0]
	ldr q24, [x2, #16]
	zip1 v21.2d, v23.2d, v24.2d
	zip2 v25.2d, v23.2d, v24.2d
	ushr v22.2d, v21.2d, #26
	ushr v23.2d, v21.2d, #52
	and v21.16b, v21.16b, v26.16b
	and v22.16b, v22.16b, v26.16b
	sli v23.2d, v25.2d, #12
	and v23.16b, v23.16b, v26.16b
	ushr v24.2d, v25.2d, #14
	and v24.16b, v24.16b, v26.16b
	ushr v25.2d, v25.2d, #40
	orr v25.16b, v25.16b, v27.16b
	add v21.2d, v21.2d, v0.2d
	add v22.2d, v22.2d, v1.2d
	add v23.2d, v23.2d, v2.2d
	add v24.2d, v24.2d, v3.2d
	add v25.2d, v25.2d, v4.2d
	uzp1 v21.4s, v21.4s, v21.4s
	uzp1 v22.4s, v22.4s, v22.4s
	uzp1 v23.4s, v23.4s, v23.4s
	uzp1 v24.4s, v24.4s, v24.4s
	uzp1 v25.4s, v25.4s, v25.4s
	umlal v16.2d, v21.2s, v8.2s
	umlal v17.2d, v21.2s, v9.2s
	umlal v18.2d, v21.2s, v10.2s
	umlal v19.2d, v21.2s, v11.2s
	umlal v20.2d, v21.2s, v12.2s
	umlal v16.2d, v22.2s, v6.2s
	umlal v17.2d, v22.2s, v8.2s
	umlal v18.2d, v22.2s, v9.2s
	umlal v19.2d, v22.2s, v10.2s
	umlal v20.2d, v22.2s, v11.2s
	umlal v16.2d, v23.2s, v5.2s
	umlal v17.2d, v23.2s, v6.2s
	umlal v18.2d, v23.2s, v8.2s
	umlal v19.2d, v23.2s, v9.2s
	umlal v20.2d, v23.2s, v10.2s
	umlal v16.2d, v24.2s, v14.2s
	umlal v17.2d, v24.2s, v5.2s
	umlal v18.2d, v24.2s, v6.2s
	umlal v19.2d, v24.2s, v8.2s
	umlal v20.2d, v24.2s, v9.2s
	umlal v16.2d, v25.2s, v13.2s
	umlal v17.2d, v25.2s, v14.2s
	umlal v18.2d, v25.2s, v5.2s
	umlal v19.2d, v25.2s, v6.2s
	umlal v20.2d, v25.2s, v8.2s
	ushr v21.2d, v16.2d, #26
	and v0.16b, v16.16b, v26.16b
	add v17.2d, v17.2d, v21.2d
	ushr v21.2d, v19.2d, #26
	and v3.16b, v19.16b, v26.16b
	add v20.2d, v20.2d, v21.2d
	ushr v21.2d, v17.2d, #26
	and v1.16b, v17.16b, v26.16b
	add v18.2d, v18.2d, v21.2d
	ushr v21.2d, v20.2d, #26
	and v4.16b, v20.16b, v26.16b
	add v0.2d, v0.2d, v21.2d
	shl v21.2d, v21.2d, #2
	add v0.2d, v0.2d, v21.2d
	ushr v21.2d, v18.2d, #26
	and v2.16b, v18.16b, v26.16b
	add v3.2d, v3.2d, v21.2d
	ushr v21.2d, v0.2d, #26
	and v0.16b, v0.16b, v26.16b
	add v1.2d, v1.2d, v21.2d
	ushr v21.2d, v3.2d, #26
	and v3.16b, v3.16b, v26.16b
	add v4.2d, v4.2d, v21.2d
	add x2, x2, #64
	sub x9, x9, #1
	cbnz x9, 213b
	shl v13.4s, v29.4s, #2
	add v13.4s, v13.4s, v29.4s
	shl v14.4s, v30.4s, #2
	add v14.4s, v14.4s, v30.4s
	shl v5.4s, v31.4s, #2
	add v5.4s, v5.4s, v31.4s
	shl v6.4s, v7.4s, #2
	add v6.4s, v6.4s, v7.4s
	ldr q23, [x2, #32]
	ldr q24, [x2, #48]
	zip1 v21.2d, v23.2d, v24.2d
	zip2 v25.2d, v23.2d, v24.2d
	ushr v22.2d, v21.2d, #26
	ushr v23.2d, v21.2d, #52
	and v21.16b, v21.16b, v26.16b
	and v22.16b, v22.16b, v26.16b
	sli v23.2d, v25.2d, #12
	and v23.16b, v23.16b, v26.16b
	ushr v24.2d, v25.2d, #14
	and v24.16b, v24.16b, v26.16b
	ushr v25.2d, v25.2d, #40
	orr v25.16b, v25.16b, v27.16b
	uzp1 v21.4s, v21.4s, v21.4s
	uzp1 v22.4s, v22.4s, v22.4s
	uzp1 v23.4s, v23.4s, v23.4s
	uzp1 v24.4s, v24.4s, v24.4s
	uzp1 v25.4s, v25.4s, v25.4s
	umull2 v16.2d, v21.4s, v28.4s
	umull2 v17.2d, v21.4s, v29.4s
	umull2 v18.2d, v21.4s, v30.4s
	umull2 v19.2d, v21.4s, v31.4s
	umull2 v20.2d, v21.4s, v7.4s
	umlal2 v16.2d, v22.4s, v6.4s
	umlal2 v17.2d, v22.4s, v28.4s
	umlal2 v18.2d, v22.4s, v29.4s
	umlal2 v19.2d, v22.4s, v30.4s
	umlal2 v20.2d, v22.4s, v31.4s
	umlal2 v16.2d, v23.4s, v5.4s
	umlal2 v17.2d, v23.4s, v6.4s
	umlal2 v18.2d, v23.4s, v28.4s
	umlal2 v19.2d, v23.4s, v29.4s
	umlal2 v20.2d, v23.4s, v30.4s
	umlal2 v16.2d, v24.4s, v14.4s
	umlal2 v17.2d, v24.4s, v5.4s
	umlal2 v18.2d, v24.4s, v6.4s
	umlal2 v19.2d, v24.4s, v28.4s
	umlal2 v20.2d, v24.4s, v29.4s
	umlal2 v16.2d, v25.4s, v13.4s
	umlal2 v17.2d, v25.4s, v14.4s
	umlal2 v18.2d, v25.4s, v5.4s
	umlal2 v19.2d, v25.4s, v6.4s
	umlal2 v20.2d, v25.4s, v28.4s
	ldr q23, [x2, #0]
	ldr q24, [x2, #16]
	zip1 v21.2d, v23.2d, v24.2d
	zip2 v25.2d, v23.2d, v24.2d
	ushr v22.2d, v21.2d, #26
	ushr v23.2d, v21.2d, #52
	and v21.16b, v21.16b, v26.16b
	and v22.16b, v22.16b, v26.16b
	sli v23.2d, v25.2d, #12
	and v23.16b, v23.16b, v26.16b
	ushr v24.2d, v25.2d, #14
	and v24.16b, v24.16b, v26.16b
	ushr v25.2d, v25.2d, #40
	orr v25.16b, v25.16b, v27.16b
	add v21.2d, v21.2d, v0.2d
	add v22.2d, v22.2d, v1.2d
	add v23.2d, v23.2d, v2.2d
	add v24.2d, v24.2d, v3.2d
	add v25.2d, v25.2d, v4.2d
	uzp1 v21.4s, v21.4s, v21.4s
	uzp1 v22.4s, v22.4s, v22.4s
	uzp1 v23.4s, v23.4s, v23.4s
	uzp1 v24.4s, v24.4s, v24.4s
	uzp1 v25.4s, v25.4s, v25.4s
	umlal v16.2d, v21.2s, v28.2s
	umlal v17.2d, v21.2s, v29.2s
	umlal v18.2d, v21.2s, v30.2s
	umlal v19.2d, v21.2s, v31.2s
	umlal v20.2d, v21.2s, v7.2s
	umlal v16.2d, v22.2s, v6.2s
	umlal v17.2d, v22.2s, v28.2s
	umlal v18.2d, v22.2s, v29.2s
	umlal v19.2d, v22.2s, v30.2s
	umlal v20.2d, v22.2s, v31.2s
	umlal v16.2d, v23.2s, v5.2s
	umlal v17.2d, v23.2s, v6.2s
	umlal v18.2d, v23.2s, v28.2s
	umlal v19.2d, v23.2s, v29.2s
	umlal v20.2d, v23.2s, v30.2s
	umlal v16.2d, v24.2s, v14.2s
	umlal v17.2d, v24.2s, v5.2s
	umlal v18.2d, v24.2s, v6.2s
	umlal v19.2d, v24.2s, v28.2s
	umlal v20.2d, v24.2s, v29.2s
	umlal v16.2d, v25.2s, v13.2s
	umlal v17.2d, v25.2s, v14.2s
	umlal v18.2d, v25.2s, v5.2s
	umlal v19.2d, v25.2s, v6.2s
	umlal v20.2d, v25.2s, v28.2s
	ushr v21.2d, v16.2d, #26
	and v0.16b, v16.16b, v26.16b
	add v17.2d, v17.2d, v21.2d
	ushr v21.2d, v19.2d, #26
	and v3.16b, v19.16b, v26.16b
	add v20.2d, v20.2d, v21.2d
	ushr v21.2d, v17.2d, #26
	and v1.16b, v17.16b, v26.16b
	add v18.2d, v18.2d, v21.2d
	ushr v21.2d, v20.2d, #26
	and v4.16b, v20.16b, v26.16b
	add v0.2d, v0.2d, v21.2d
	shl v21.2d, v21.2d, #2
	add v0.2d, v0.2d, v21.2d
	ushr v21.2d, v18.2d, #26
	and v2.16b, v18.16b, v26.16b
	add v3.2d, v3.2d, v21.2d
	ushr v21.2d, v0.2d, #26
	and v0.16b, v0.16b, v26.16b
	add v1.2d, v1.2d, v21.2d
	ushr v21.2d, v3.2d, #26
	and v3.16b, v3.16b, v26.16b
	add v4.2d, v4.2d, v21.2d
	add x2, x2, #64
	movz x9, #63, lsl #0
	and x3, x3, x9
	umov x9, v0.d[0]
	umov x14, v0.d[1]
	add x9, x9, x14
	umov x10, v1.d[0]
	umov x14, v1.d[1]
	add x10, x10, x14
	umov x11, v2.d[0]
	umov x14, v2.d[1]
	add x11, x11, x14
	umov x12, v3.d[0]
	umov x14, v3.d[1]
	add x12, x12, x14
	umov x13, v4.d[0]
	umov x14, v4.d[1]
	add x13, x13, x14
	lsl x14, x10, #26
	add x4, x9, x14
	lsl x14, x11, #52
	adds x4, x4, x14
	lsr x15, x11, #12
	lsl x14, x12, #14
	add x5, x15, x14
	lsl x14, x13, #40
	adcs x5, x5, x14
	lsr x15, x13, #24
	movz x14, #0, lsl #0
	adc x6, x15, x14
	lsr x14, x6, #2
	movz x15, #3, lsl #0
	and x6, x6, x15
	lsl x15, x14, #2
	add x14, x14, x15
	adds x4, x4, x14
	movz x15, #0, lsl #0
	adcs x5, x5, x15
	adc x6, x6, x15
	ldr x9, [x0, #72]
	mov v8.d[0], x9
	ldr x9, [x0, #80]
	mov v9.d[0], x9
	ldr x9, [x0, #88]
	mov v10.d[0], x9
	ldr x9, [x0, #96]
	mov v11.d[0], x9
	ldr x9, [x0, #104]
	mov v12.d[0], x9
	ldr x9, [x0, #112]
	mov v13.d[0], x9
	ldr x9, [x0, #120]
	mov v14.d[0], x9
	b 212f
211:
212:
	add x1, x2, #0
	lsr x2, x3, #4
	cbz x2, 214f
216:
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #1, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	add x1, x1, #16
	sub x3, x3, #16
	lsr x2, x3, #4
	cbnz x2, 216b
	b 215f
214:
215:
	cbz x3, 217f
	add x10, x3, #0
	add x11, x0, #0
219:
	ldrb w12, [x1, #0]
	strb w12, [x11, #56]
	add x1, x1, #1
	add x11, x11, #1
	sub x10, x10, #1
	cbnz x10, 219b
	b 218f
217:
218:
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	add sp, sp, #128
	ret
	.p2align 6

vg_poly1305_finalize:
	sub sp, sp, #128
	add x3, sp, #0
	add x3, x2, #0
	movz x2, #15, lsl #0
	and x2, x1, x2
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	cbz x2, 20f
	movz x11, #0, lsl #0
	add x9, x0, x2
	movz x10, #16, lsl #0
	sub x10, x10, x2
22:
	strb w11, [x9, #56]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 22b
	movz x11, #1, lsl #0
	add x9, x0, x2
	strb w11, [x9, #56]
	add x1, x0, #56
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 21f
20:
21:
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	ldr x13, [x0, #40]
	ldr x14, [x0, #48]
	adds x4, x4, x13
	adc x5, x5, x14
	str x4, [x3, #0]
	str x5, [x3, #8]
	add sp, sp, #128
	ret
	.p2align 6

vg_poly1305_finalize_scratch:
	add x3, x2, #0
	movz x2, #15, lsl #0
	and x2, x1, x2
	movz x16, #65535, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x7, [x0, #24]
	and x7, x7, x16
	movz x16, #65532, lsl #0
	movk x16, #4095, lsl #16
	movk x16, #65532, lsl #32
	movk x16, #4095, lsl #48
	ldr x8, [x0, #32]
	and x8, x8, x16
	lsr x17, x8, #2
	add x17, x17, x8
	ldr x4, [x0, #0]
	ldr x5, [x0, #8]
	ldr x6, [x0, #16]
	cbz x2, 20f
	movz x11, #0, lsl #0
	add x9, x0, x2
	movz x10, #16, lsl #0
	sub x10, x10, x2
22:
	strb w11, [x9, #56]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 22b
	movz x11, #1, lsl #0
	add x9, x0, x2
	strb w11, [x9, #56]
	add x1, x0, #56
	ldr x13, [x1, #0]
	ldr x14, [x1, #8]
	movz x15, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x15
	mul x9, x4, x7
	umulh x10, x4, x7
	mul x13, x5, x17
	umulh x14, x5, x17
	adds x9, x9, x13
	adc x10, x10, x14
	mul x11, x4, x8
	umulh x12, x4, x8
	mul x13, x5, x7
	umulh x14, x5, x7
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x17
	movz x14, #0, lsl #0
	adds x11, x11, x13
	adc x12, x12, x14
	mul x13, x6, x7
	adds x11, x11, x10
	adc x12, x12, x13
	add x4, x9, #0
	add x5, x11, #0
	movz x14, #3, lsl #0
	bic x13, x12, x14, ror #0
	and x6, x12, x14
	lsr x12, x12, #2
	add x13, x13, x12
	movz x14, #0, lsl #0
	adds x4, x4, x13
	adcs x5, x5, x14
	adc x6, x6, x14
	b 21f
20:
21:
	movz x13, #5, lsl #0
	movz x14, #0, lsl #0
	adds x9, x4, x13
	adcs x10, x5, x14
	adc x11, x6, x14
	lsr x12, x11, #2
	movz x14, #0, lsl #0
	sub x12, x14, x12
	movz x14, #3, lsl #0
	and x11, x11, x14
	eor x13, x9, x4
	and x13, x13, x12
	eor x4, x4, x13
	eor x13, x10, x5
	and x13, x13, x12
	eor x5, x5, x13
	eor x13, x11, x6
	and x13, x13, x12
	eor x6, x6, x13
	ldr x13, [x0, #40]
	ldr x14, [x0, #48]
	adds x4, x4, x13
	adc x5, x5, x14
	str x4, [x3, #0]
	str x5, [x3, #8]
	ret
	.p2align 6
