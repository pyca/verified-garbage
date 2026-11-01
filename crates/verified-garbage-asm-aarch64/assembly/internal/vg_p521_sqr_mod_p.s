// The functions of `src/internal/vg_p521_sqr_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sqr_mod_p:
	add w1, w1, #0
	add w2, w2, #0
	add w3, w3, #0
	mov v16.d[0], x19
	mov v16.d[1], x20
	mov v17.d[0], x21
	mov v17.d[1], x22
	mov v18.d[0], x23
	mov v18.d[1], x24
	mov v19.d[0], x25
	mov v19.d[1], x26
	mov v20.d[0], x27
	mov v20.d[1], x28
	mov v21.d[0], x30
	add x30, x0, x1
	add x1, x0, x2
	ldr x2, [x1, #0]
	ldr x3, [x1, #8]
	ldr x4, [x1, #16]
	ldr x5, [x1, #24]
	ldr x6, [x1, #32]
	ldr x7, [x1, #40]
	ldr x8, [x1, #48]
	ldr x9, [x1, #56]
	ldr x28, [x1, #64]
	dup v22.2d, x30
	movz x30, #0, lsl #0
	mul x12, x2, x3
	umulh x13, x2, x3
	mul x10, x2, x4
	umulh x14, x2, x4
	adds x13, x13, x10
	mul x10, x2, x5
	umulh x15, x2, x5
	adcs x14, x14, x10
	mul x10, x2, x6
	umulh x16, x2, x6
	adcs x15, x15, x10
	mul x10, x2, x7
	umulh x17, x2, x7
	adcs x16, x16, x10
	mul x10, x2, x8
	umulh x19, x2, x8
	adcs x17, x17, x10
	mul x10, x2, x9
	umulh x20, x2, x9
	adcs x19, x19, x10
	adc x20, x20, x30
	mul x10, x3, x4
	adds x14, x14, x10
	mul x10, x3, x5
	adcs x15, x15, x10
	mul x10, x3, x6
	adcs x16, x16, x10
	mul x10, x3, x7
	adcs x17, x17, x10
	mul x10, x3, x8
	adcs x19, x19, x10
	mul x10, x3, x9
	adcs x20, x20, x10
	adc x21, x30, x30
	umulh x10, x3, x4
	adds x15, x15, x10
	umulh x10, x3, x5
	adcs x16, x16, x10
	umulh x10, x3, x6
	adcs x17, x17, x10
	umulh x10, x3, x7
	adcs x19, x19, x10
	umulh x10, x3, x8
	adcs x20, x20, x10
	umulh x10, x3, x9
	adc x21, x21, x10
	mul x10, x6, x7
	umulh x22, x6, x7
	adds x21, x21, x10
	adc x22, x22, x30
	mul x10, x4, x5
	adds x16, x16, x10
	mul x10, x4, x6
	adcs x17, x17, x10
	mul x10, x4, x7
	adcs x19, x19, x10
	mul x10, x4, x8
	adcs x20, x20, x10
	mul x10, x4, x9
	adcs x21, x21, x10
	mul x10, x6, x8
	adcs x22, x22, x10
	adc x23, x30, x30
	umulh x10, x4, x5
	adds x17, x17, x10
	umulh x10, x4, x6
	adcs x19, x19, x10
	umulh x10, x4, x7
	adcs x20, x20, x10
	umulh x10, x4, x8
	adcs x21, x21, x10
	umulh x10, x4, x9
	adcs x22, x22, x10
	umulh x10, x6, x8
	adc x23, x23, x10
	mul x10, x7, x8
	umulh x24, x7, x8
	adds x23, x23, x10
	adc x24, x24, x30
	mul x10, x5, x6
	adds x19, x19, x10
	mul x10, x5, x7
	adcs x20, x20, x10
	mul x10, x5, x8
	adcs x21, x21, x10
	mul x10, x5, x9
	adcs x22, x22, x10
	mul x10, x6, x9
	adcs x23, x23, x10
	mul x10, x7, x9
	adcs x24, x24, x10
	adc x25, x30, x30
	umulh x10, x5, x6
	adds x20, x20, x10
	umulh x10, x5, x7
	adcs x21, x21, x10
	umulh x10, x5, x8
	adcs x22, x22, x10
	umulh x10, x5, x9
	adcs x23, x23, x10
	umulh x10, x6, x9
	adcs x24, x24, x10
	umulh x10, x7, x9
	adc x25, x25, x10
	mul x10, x8, x9
	umulh x26, x8, x9
	adds x25, x25, x10
	adc x26, x26, x30
	adds x12, x12, x12
	adcs x13, x13, x13
	adcs x14, x14, x14
	adcs x15, x15, x15
	adcs x16, x16, x16
	adcs x17, x17, x17
	adcs x19, x19, x19
	adcs x20, x20, x20
	adcs x21, x21, x21
	adcs x22, x22, x22
	adcs x23, x23, x23
	adcs x24, x24, x24
	adcs x25, x25, x25
	adcs x26, x26, x26
	adc x27, x30, x30
	umulh x10, x2, x2
	mul x11, x2, x2
	adds x12, x12, x10
	mul x10, x3, x3
	adcs x13, x13, x10
	umulh x10, x3, x3
	adcs x14, x14, x10
	mul x10, x4, x4
	adcs x15, x15, x10
	umulh x10, x4, x4
	adcs x16, x16, x10
	mul x10, x5, x5
	adcs x17, x17, x10
	umulh x10, x5, x5
	adcs x19, x19, x10
	mul x10, x6, x6
	adcs x20, x20, x10
	umulh x10, x6, x6
	adcs x21, x21, x10
	mul x10, x7, x7
	adcs x22, x22, x10
	umulh x10, x7, x7
	adcs x23, x23, x10
	mul x10, x8, x8
	adcs x24, x24, x10
	umulh x10, x8, x8
	adcs x25, x25, x10
	mul x10, x9, x9
	adcs x26, x26, x10
	umulh x10, x9, x9
	adc x27, x27, x10
	mul x1, x28, x28
	add x28, x28, x28
	mul x10, x28, x2
	adds x20, x20, x10
	mul x10, x28, x3
	adcs x21, x21, x10
	mul x10, x28, x4
	adcs x22, x22, x10
	mul x10, x28, x5
	adcs x23, x23, x10
	mul x10, x28, x6
	adcs x24, x24, x10
	mul x10, x28, x7
	adcs x25, x25, x10
	mul x10, x28, x8
	adcs x26, x26, x10
	mul x10, x28, x9
	adcs x27, x27, x10
	adc x1, x1, x30
	umulh x10, x28, x2
	adds x21, x21, x10
	umulh x10, x28, x3
	adcs x22, x22, x10
	umulh x10, x28, x4
	adcs x23, x23, x10
	umulh x10, x28, x5
	adcs x24, x24, x10
	umulh x10, x28, x6
	adcs x25, x25, x10
	umulh x10, x28, x7
	adcs x26, x26, x10
	umulh x10, x28, x8
	adcs x27, x27, x10
	umulh x10, x28, x9
	adc x1, x1, x10
	subs x30, x30, x30
	extr x10, x21, x20, #9
	adcs x11, x11, x10
	extr x10, x22, x21, #9
	adcs x12, x12, x10
	extr x10, x23, x22, #9
	adcs x13, x13, x10
	extr x10, x24, x23, #9
	adcs x14, x14, x10
	extr x10, x25, x24, #9
	adcs x15, x15, x10
	extr x10, x26, x25, #9
	adcs x16, x16, x10
	extr x10, x27, x26, #9
	adcs x17, x17, x10
	extr x10, x1, x27, #9
	adcs x19, x19, x10
	sub x3, x30, #1
	lsl x3, x3, #9
	orr x20, x20, x3
	lsr x10, x1, #9
	adcs x20, x20, x10
	sbcs x11, x11, x30
	sbcs x12, x12, x30
	sbcs x13, x13, x30
	sbcs x14, x14, x30
	sbcs x15, x15, x30
	sbcs x16, x16, x30
	sbcs x17, x17, x30
	sbcs x19, x19, x30
	sbc x20, x20, x30
	movz x3, #511, lsl #0
	and x20, x20, x3
	lsl x10, x11, #9
	extr x11, x12, x11, #55
	extr x12, x13, x12, #55
	extr x13, x14, x13, #55
	extr x14, x15, x14, #55
	orr x20, x20, x10
	extr x15, x16, x15, #55
	extr x16, x17, x16, #55
	extr x17, x19, x17, #55
	extr x19, x20, x19, #55
	lsr x20, x20, #55
	umov x30, v22.d[0]
	str x11, [x30, #0]
	str x12, [x30, #8]
	str x13, [x30, #16]
	str x14, [x30, #24]
	str x15, [x30, #32]
	str x16, [x30, #40]
	str x17, [x30, #48]
	str x19, [x30, #56]
	str x20, [x30, #64]
	umov x19, v16.d[0]
	umov x20, v16.d[1]
	umov x21, v17.d[0]
	umov x22, v17.d[1]
	umov x23, v18.d[0]
	umov x24, v18.d[1]
	umov x25, v19.d[0]
	umov x26, v19.d[1]
	umov x27, v20.d[0]
	umov x28, v20.d[1]
	umov x30, v21.d[0]
	ret
	.p2align 6
