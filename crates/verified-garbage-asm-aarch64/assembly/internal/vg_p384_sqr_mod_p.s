// The functions of `src/internal/vg_p384_sqr_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p384_sqr_mod_p:
	add w1, w1, #0
	add w2, w2, #0
	add w3, w3, #0
	mov v16.d[0], x21
	mov v16.d[1], x22
	mov v17.d[0], x23
	mov v17.d[1], x24
	mov v18.d[0], x25
	mov v18.d[1], x26
	mov v19.d[0], x27
	mov v19.d[1], x28
	add x28, x0, x1
	add x27, x0, x2
	add x3, x0, x3
	ldr x4, [x27, #0]
	ldr x5, [x27, #8]
	ldr x16, [x27, #16]
	ldr x17, [x27, #24]
	ldr x21, [x27, #32]
	ldr x22, [x27, #40]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x6, #0, lsl #0
	movz x23, #0, lsl #0
	movz x24, #0, lsl #0
	movz x25, #0, lsl #0
	mul x2, x4, x5
	adds x9, x9, x2
	mul x2, x4, x16
	adcs x10, x10, x2
	mul x2, x4, x17
	adcs x11, x11, x2
	mul x2, x4, x21
	adcs x12, x12, x2
	mul x2, x4, x22
	adcs x13, x13, x2
	umulh x2, x4, x22
	adcs x14, x14, x2
	umulh x2, x4, x5
	adds x10, x10, x2
	umulh x2, x4, x16
	adcs x11, x11, x2
	umulh x2, x4, x17
	adcs x12, x12, x2
	umulh x2, x4, x21
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x2, x5, x16
	adds x11, x11, x2
	mul x2, x5, x17
	adcs x12, x12, x2
	mul x2, x5, x21
	adcs x13, x13, x2
	mul x2, x5, x22
	adcs x14, x14, x2
	umulh x2, x5, x22
	adcs x15, x15, x2
	umulh x2, x5, x16
	adds x12, x12, x2
	umulh x2, x5, x17
	adcs x13, x13, x2
	umulh x2, x5, x21
	adcs x14, x14, x2
	adcs x15, x15, x7
	mul x2, x16, x17
	adds x13, x13, x2
	mul x2, x16, x21
	adcs x14, x14, x2
	mul x2, x16, x22
	adcs x15, x15, x2
	umulh x2, x16, x22
	adcs x6, x6, x2
	umulh x2, x16, x17
	adds x14, x14, x2
	umulh x2, x16, x21
	adcs x15, x15, x2
	adcs x6, x6, x7
	mul x2, x17, x21
	adds x15, x15, x2
	mul x2, x17, x22
	adcs x6, x6, x2
	umulh x2, x17, x22
	adcs x23, x23, x2
	umulh x2, x17, x21
	adds x6, x6, x2
	adcs x23, x23, x7
	mul x2, x21, x22
	adds x23, x23, x2
	umulh x2, x21, x22
	adcs x24, x24, x2
	adds x8, x8, x8
	adcs x9, x9, x9
	adcs x10, x10, x10
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x6, x6, x6
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	mul x2, x4, x4
	adds x8, x8, x2
	umulh x2, x4, x4
	adcs x9, x9, x2
	mul x2, x5, x5
	adcs x10, x10, x2
	umulh x2, x5, x5
	adcs x11, x11, x2
	mul x2, x16, x16
	adcs x12, x12, x2
	umulh x2, x16, x16
	adcs x13, x13, x2
	mul x2, x17, x17
	adcs x14, x14, x2
	umulh x2, x17, x17
	adcs x15, x15, x2
	mul x2, x21, x21
	adcs x6, x6, x2
	umulh x2, x21, x21
	adcs x23, x23, x2
	mul x2, x22, x22
	adcs x24, x24, x2
	umulh x2, x22, x22
	adcs x25, x25, x2
	sub x17, x7, #1
	lsl x16, x17, #32
	lsr x17, x17, #32
	add x16, x16, #1
	lsl x1, x8, #32
	add x8, x1, x8
	umulh x1, x16, x8
	mul x3, x17, x8
	umulh x2, x17, x8
	adds x1, x1, x3
	adcs x2, x2, x8
	adc x3, x7, x7
	subs x9, x9, x1
	sbcs x10, x10, x2
	sbcs x11, x11, x3
	sbcs x12, x12, x7
	sbcs x13, x13, x7
	sbc x8, x8, x7
	lsl x1, x9, #32
	add x9, x1, x9
	umulh x1, x16, x9
	mul x3, x17, x9
	umulh x2, x17, x9
	adds x1, x1, x3
	adcs x2, x2, x9
	adc x3, x7, x7
	subs x10, x10, x1
	sbcs x11, x11, x2
	sbcs x12, x12, x3
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x1, x10, #32
	add x10, x1, x10
	umulh x1, x16, x10
	mul x3, x17, x10
	umulh x2, x17, x10
	adds x1, x1, x3
	adcs x2, x2, x10
	adc x3, x7, x7
	subs x11, x11, x1
	sbcs x12, x12, x2
	sbcs x13, x13, x3
	sbcs x8, x8, x7
	sbcs x9, x9, x7
	sbc x10, x10, x7
	lsl x1, x11, #32
	add x11, x1, x11
	umulh x1, x16, x11
	mul x3, x17, x11
	umulh x2, x17, x11
	adds x1, x1, x3
	adcs x2, x2, x11
	adc x3, x7, x7
	subs x12, x12, x1
	sbcs x13, x13, x2
	sbcs x8, x8, x3
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x11, x11, x7
	lsl x1, x12, #32
	add x12, x1, x12
	umulh x1, x16, x12
	mul x3, x17, x12
	umulh x2, x17, x12
	adds x1, x1, x3
	adcs x2, x2, x12
	adc x3, x7, x7
	subs x13, x13, x1
	sbcs x8, x8, x2
	sbcs x9, x9, x3
	sbcs x10, x10, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	lsl x1, x13, #32
	add x13, x1, x13
	umulh x1, x16, x13
	mul x3, x17, x13
	umulh x2, x17, x13
	adds x1, x1, x3
	adcs x2, x2, x13
	adc x3, x7, x7
	subs x8, x8, x1
	sbcs x9, x9, x2
	sbcs x10, x10, x3
	sbcs x11, x11, x7
	sbcs x12, x12, x7
	sbc x13, x13, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x6
	adcs x11, x11, x23
	adcs x12, x12, x24
	adcs x13, x13, x25
	adc x21, x7, x7
	sub x26, x7, #1
	lsr x23, x26, #32
	lsl x24, x26, #32
	sub x25, x26, #1
	subs x1, x8, x23
	sbcs x3, x9, x24
	sbcs x4, x10, x25
	sbcs x5, x11, x26
	sbcs x6, x12, x26
	sbcs x16, x13, x26
	sbcs x2, x21, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x11, x5, x11, hs
	csel x12, x6, x12, hs
	csel x13, x16, x13, hs
	str x8, [x28, #0]
	str x9, [x28, #8]
	str x10, [x28, #16]
	str x11, [x28, #24]
	str x12, [x28, #32]
	str x13, [x28, #40]
	umov x21, v16.d[0]
	umov x22, v16.d[1]
	umov x23, v17.d[0]
	umov x24, v17.d[1]
	umov x25, v18.d[0]
	umov x26, v18.d[1]
	umov x27, v19.d[0]
	umov x28, v19.d[1]
	ret
	.p2align 6
