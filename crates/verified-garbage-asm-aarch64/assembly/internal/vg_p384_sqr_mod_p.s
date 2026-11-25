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
	movz x7, #0, lsl #0
	ldr x8, [x27, #0]
	ldr x9, [x27, #8]
	ldr x10, [x27, #16]
	ldr x16, [x27, #24]
	ldr x24, [x27, #32]
	ldr x25, [x27, #40]
	mul x22, x8, x9
	mul x23, x8, x10
	mul x11, x8, x16
	mul x12, x8, x24
	mul x13, x8, x25
	umulh x2, x8, x9
	adds x23, x23, x2
	umulh x2, x8, x10
	adcs x11, x11, x2
	umulh x2, x8, x16
	adcs x12, x12, x2
	umulh x2, x8, x24
	adcs x13, x13, x2
	umulh x2, x8, x25
	adc x14, x2, x7
	mul x2, x9, x10
	adds x11, x11, x2
	mul x2, x9, x16
	adcs x12, x12, x2
	mul x2, x9, x24
	adcs x13, x13, x2
	mul x2, x9, x25
	adcs x14, x14, x2
	adc x15, x7, x7
	umulh x2, x9, x10
	adds x12, x12, x2
	umulh x2, x9, x16
	adcs x13, x13, x2
	umulh x2, x9, x24
	adcs x14, x14, x2
	umulh x2, x9, x25
	adc x15, x15, x2
	mul x2, x10, x16
	adds x13, x13, x2
	mul x2, x10, x24
	adcs x14, x14, x2
	mul x2, x10, x25
	adcs x15, x15, x2
	adc x21, x7, x7
	umulh x2, x10, x16
	adds x14, x14, x2
	umulh x2, x10, x24
	adcs x15, x15, x2
	umulh x2, x10, x25
	adc x21, x21, x2
	mul x2, x16, x24
	adds x15, x15, x2
	mul x2, x16, x25
	adcs x21, x21, x2
	adc x4, x7, x7
	umulh x2, x16, x24
	adds x21, x21, x2
	umulh x2, x16, x25
	adc x4, x4, x2
	mul x2, x24, x25
	adds x4, x4, x2
	umulh x2, x24, x25
	adc x5, x2, x7
	adds x22, x22, x22
	adcs x23, x23, x23
	adcs x11, x11, x11
	adcs x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x21, x21, x21
	adcs x4, x4, x4
	adcs x5, x5, x5
	adc x6, x7, x7
	mul x17, x8, x8
	umulh x2, x8, x8
	adds x22, x22, x2
	mul x2, x9, x9
	adcs x23, x23, x2
	umulh x2, x9, x9
	adcs x11, x11, x2
	mul x2, x10, x10
	adcs x12, x12, x2
	umulh x2, x10, x10
	adcs x13, x13, x2
	mul x2, x16, x16
	adcs x14, x14, x2
	umulh x2, x16, x16
	adcs x15, x15, x2
	mul x2, x24, x24
	adcs x21, x21, x2
	umulh x2, x24, x24
	adcs x4, x4, x2
	mul x2, x25, x25
	adcs x5, x5, x2
	umulh x2, x25, x25
	adc x6, x6, x2
	lsl x8, x17, #32
	extr x1, x22, x17, #32
	adds x8, x17, x8
	adc x1, x22, x1
	add x9, x1, x17
	lsl x17, x8, #32
	extr x1, x9, x8, #32
	lsr x2, x9, #32
	adds x3, x9, x17
	adcs x16, x8, x1
	adcs x24, x9, x2
	adc x25, x7, x7
	subs x17, x8, x17
	sbcs x3, x3, x1
	sbcs x16, x16, x2
	sbcs x24, x24, x7
	sbc x25, x25, x7
	subs x23, x23, x16
	sbcs x11, x11, x24
	sbcs x12, x12, x25
	sbcs x13, x13, x7
	sbcs x8, x8, x7
	sbc x9, x9, x7
	lsl x10, x23, #32
	extr x1, x11, x23, #32
	adds x10, x23, x10
	adc x1, x11, x1
	add x22, x1, x23
	lsl x23, x10, #32
	extr x1, x22, x10, #32
	lsr x2, x22, #32
	adds x3, x22, x23
	adcs x16, x10, x1
	adcs x24, x22, x2
	adc x25, x7, x7
	subs x23, x10, x23
	sbcs x3, x3, x1
	sbcs x16, x16, x2
	sbcs x24, x24, x7
	sbc x25, x25, x7
	subs x12, x12, x16
	sbcs x13, x13, x24
	sbcs x8, x8, x25
	sbcs x9, x9, x7
	sbcs x10, x10, x7
	sbc x22, x22, x7
	lsl x11, x12, #32
	extr x1, x13, x12, #32
	adds x11, x12, x11
	adc x1, x13, x1
	add x12, x1, x12
	lsl x13, x11, #32
	extr x1, x12, x11, #32
	lsr x2, x12, #32
	adds x3, x12, x13
	adcs x16, x11, x1
	adcs x24, x12, x2
	adc x25, x7, x7
	subs x13, x11, x13
	sbcs x3, x3, x1
	sbcs x16, x16, x2
	sbcs x24, x24, x7
	sbc x25, x25, x7
	subs x8, x8, x16
	sbcs x9, x9, x24
	sbcs x10, x10, x25
	sbcs x22, x22, x7
	sbcs x11, x11, x7
	sbc x12, x12, x7
	adds x8, x8, x14
	adcs x9, x9, x15
	adcs x10, x10, x21
	adcs x22, x22, x4
	adcs x11, x11, x5
	adcs x12, x12, x6
	adc x13, x7, x7
	sub x26, x7, #1
	lsr x23, x26, #32
	lsl x24, x26, #32
	sub x25, x26, #1
	subs x1, x8, x23
	sbcs x3, x9, x24
	sbcs x4, x10, x25
	sbcs x5, x22, x26
	sbcs x6, x11, x26
	sbcs x16, x12, x26
	sbcs x2, x13, x7
	csel x8, x1, x8, hs
	csel x9, x3, x9, hs
	csel x10, x4, x10, hs
	csel x22, x5, x22, hs
	csel x11, x6, x11, hs
	csel x12, x16, x12, hs
	str x8, [x28, #0]
	str x9, [x28, #8]
	str x10, [x28, #16]
	str x22, [x28, #24]
	str x11, [x28, #32]
	str x12, [x28, #40]
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
