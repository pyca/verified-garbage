// The functions of `src/internal/vg_p521_sqr_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_sqr_mod_p:
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
	mov v20.d[0], x30
	add x30, x0, x1
	add x28, x0, x2
	add x3, x0, x3
	ldr x1, [x28, #8]
	ldr x3, [x28, #16]
	extr x4, x3, x1, #63
	ldr x1, [x28, #24]
	extr x5, x1, x3, #63
	ldr x3, [x28, #32]
	extr x6, x3, x1, #63
	ldr x1, [x28, #40]
	extr x16, x1, x3, #63
	ldr x3, [x28, #48]
	extr x17, x3, x1, #63
	ldr x1, [x28, #56]
	extr x24, x1, x3, #63
	ldr x3, [x28, #64]
	extr x25, x3, x1, #63
	movz x7, #0, lsl #0
	ldr x1, [x28, #0]
	ldr x3, [x28, #8]
	lsl x3, x3, #1
	mul x8, x1, x1
	mul x9, x1, x3
	mul x10, x1, x4
	mul x11, x1, x5
	mul x12, x1, x6
	mul x13, x1, x16
	mul x14, x1, x17
	mul x15, x1, x24
	mul x21, x1, x25
	umulh x2, x1, x1
	adds x9, x9, x2
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adcs x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x6
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x24
	adcs x21, x21, x2
	umulh x2, x1, x25
	adc x22, x2, x7
	ldr x1, [x28, #8]
	ldr x3, [x28, #16]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x10, x10, x2
	mul x2, x1, x3
	adcs x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x6
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x24
	adcs x21, x21, x2
	mul x2, x1, x25
	adcs x22, x22, x2
	umulh x2, x1, x25
	adc x4, x2, x7
	umulh x2, x1, x1
	adds x11, x11, x2
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x6
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	umulh x2, x1, x24
	adcs x22, x22, x2
	adc x4, x4, x7
	ldr x1, [x28, #16]
	ldr x3, [x28, #24]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x12, x12, x2
	mul x2, x1, x3
	adcs x13, x13, x2
	mul x2, x1, x6
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	mul x2, x1, x24
	adcs x22, x22, x2
	mul x2, x1, x25
	adcs x4, x4, x2
	umulh x2, x1, x25
	adc x5, x2, x7
	umulh x2, x1, x1
	adds x13, x13, x2
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x6
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	umulh x2, x1, x24
	adcs x4, x4, x2
	adc x5, x5, x7
	ldr x1, [x28, #24]
	ldr x3, [x28, #32]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x14, x14, x2
	mul x2, x1, x3
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	mul x2, x1, x24
	adcs x4, x4, x2
	mul x2, x1, x25
	adcs x5, x5, x2
	umulh x2, x1, x25
	adc x6, x2, x7
	umulh x2, x1, x1
	adds x15, x15, x2
	umulh x2, x1, x3
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x4, x4, x2
	umulh x2, x1, x24
	adcs x5, x5, x2
	adc x6, x6, x7
	ldr x1, [x28, #32]
	ldr x3, [x28, #40]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x21, x21, x2
	mul x2, x1, x3
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x4, x4, x2
	mul x2, x1, x24
	adcs x5, x5, x2
	mul x2, x1, x25
	adcs x6, x6, x2
	umulh x2, x1, x25
	adc x16, x2, x7
	umulh x2, x1, x1
	adds x22, x22, x2
	umulh x2, x1, x3
	adcs x4, x4, x2
	umulh x2, x1, x17
	adcs x5, x5, x2
	umulh x2, x1, x24
	adcs x6, x6, x2
	adc x16, x16, x7
	ldr x1, [x28, #40]
	ldr x3, [x28, #48]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x4, x4, x2
	mul x2, x1, x3
	adcs x5, x5, x2
	mul x2, x1, x24
	adcs x6, x6, x2
	mul x2, x1, x25
	adcs x16, x16, x2
	umulh x2, x1, x25
	adc x17, x2, x7
	umulh x2, x1, x1
	adds x5, x5, x2
	umulh x2, x1, x3
	adcs x6, x6, x2
	umulh x2, x1, x24
	adcs x16, x16, x2
	adc x17, x17, x7
	ldr x1, [x28, #48]
	ldr x3, [x28, #56]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x6, x6, x2
	mul x2, x1, x3
	adcs x16, x16, x2
	mul x2, x1, x25
	adcs x17, x17, x2
	umulh x2, x1, x25
	adc x24, x2, x7
	umulh x2, x1, x1
	adds x16, x16, x2
	umulh x2, x1, x3
	adcs x17, x17, x2
	adc x24, x24, x7
	ldr x1, [x28, #56]
	ldr x3, [x28, #64]
	lsl x3, x3, #1
	mul x2, x1, x1
	adds x17, x17, x2
	mul x2, x1, x3
	adcs x24, x24, x2
	umulh x2, x1, x3
	adc x25, x2, x7
	umulh x2, x1, x1
	adds x24, x24, x2
	adc x25, x25, x7
	ldr x1, [x28, #64]
	mul x2, x1, x1
	add x25, x25, x2
	lsl x2, x8, #9
	adds x21, x21, x2
	extr x8, x9, x8, #55
	extr x9, x10, x9, #55
	extr x10, x11, x10, #55
	extr x11, x12, x11, #55
	extr x12, x13, x12, #55
	extr x13, x14, x13, #55
	extr x14, x15, x14, #55
	extr x15, x21, x15, #55
	lsr x21, x21, #55
	adcs x8, x22, x8
	adcs x9, x4, x9
	adcs x10, x5, x10
	adcs x11, x6, x11
	adcs x12, x16, x12
	adcs x13, x17, x13
	adcs x14, x24, x14
	adcs x15, x25, x15
	adc x21, x21, x7
	lsr x1, x21, #9
	movz x2, #511, lsl #0
	and x21, x21, x2
	adds x8, x8, x1
	adcs x9, x9, x7
	adcs x10, x10, x7
	adcs x11, x11, x7
	adcs x12, x12, x7
	adcs x13, x13, x7
	adcs x14, x14, x7
	adcs x15, x15, x7
	adc x21, x21, x7
	str x8, [x30, #0]
	str x9, [x30, #8]
	str x10, [x30, #16]
	str x11, [x30, #24]
	str x12, [x30, #32]
	str x13, [x30, #40]
	str x14, [x30, #48]
	str x15, [x30, #56]
	str x21, [x30, #64]
	umov x21, v16.d[0]
	umov x22, v16.d[1]
	umov x23, v17.d[0]
	umov x24, v17.d[1]
	umov x25, v18.d[0]
	umov x26, v18.d[1]
	umov x27, v19.d[0]
	umov x28, v19.d[1]
	umov x30, v20.d[0]
	ret
	.p2align 6
