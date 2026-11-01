// The functions of `src/p521_mont.rs` of `verified-garbage-asm-aarch64`, as text: generated from
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

vg_p521_mul_mod_p:
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
	ldr x4, [x3, #0]
	ldr x5, [x3, #8]
	ldr x16, [x3, #16]
	ldr x17, [x3, #24]
	ldr x6, [x3, #32]
	ldr x24, [x3, #40]
	ldr x25, [x3, #48]
	ldr x26, [x3, #56]
	ldr x27, [x3, #64]
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x21, #0, lsl #0
	movz x22, #0, lsl #0
	movz x23, #0, lsl #0
	ldr x1, [x28, #0]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	mul x2, x1, x6
	adcs x12, x12, x2
	mul x2, x1, x24
	adcs x13, x13, x2
	mul x2, x1, x25
	adcs x14, x14, x2
	mul x2, x1, x26
	adcs x15, x15, x2
	mul x2, x1, x27
	adcs x21, x21, x2
	umulh x2, x1, x27
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	umulh x2, x1, x6
	adcs x13, x13, x2
	umulh x2, x1, x24
	adcs x14, x14, x2
	umulh x2, x1, x25
	adcs x15, x15, x2
	umulh x2, x1, x26
	adcs x21, x21, x2
	adcs x22, x22, x7
	lsl x2, x8, #9
	adds x21, x21, x2
	lsr x2, x8, #55
	adcs x22, x22, x2
	adcs x23, x23, x7
	movz x8, #0, lsl #0
	ldr x1, [x28, #8]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	mul x2, x1, x6
	adcs x13, x13, x2
	mul x2, x1, x24
	adcs x14, x14, x2
	mul x2, x1, x25
	adcs x15, x15, x2
	mul x2, x1, x26
	adcs x21, x21, x2
	mul x2, x1, x27
	adcs x22, x22, x2
	umulh x2, x1, x27
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	umulh x2, x1, x6
	adcs x14, x14, x2
	umulh x2, x1, x24
	adcs x15, x15, x2
	umulh x2, x1, x25
	adcs x21, x21, x2
	umulh x2, x1, x26
	adcs x22, x22, x2
	adcs x23, x23, x7
	lsl x2, x9, #9
	adds x22, x22, x2
	lsr x2, x9, #55
	adcs x23, x23, x2
	adcs x8, x8, x7
	movz x9, #0, lsl #0
	ldr x1, [x28, #16]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	mul x2, x1, x6
	adcs x14, x14, x2
	mul x2, x1, x24
	adcs x15, x15, x2
	mul x2, x1, x25
	adcs x21, x21, x2
	mul x2, x1, x26
	adcs x22, x22, x2
	mul x2, x1, x27
	adcs x23, x23, x2
	umulh x2, x1, x27
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	umulh x2, x1, x6
	adcs x15, x15, x2
	umulh x2, x1, x24
	adcs x21, x21, x2
	umulh x2, x1, x25
	adcs x22, x22, x2
	umulh x2, x1, x26
	adcs x23, x23, x2
	adcs x8, x8, x7
	lsl x2, x10, #9
	adds x23, x23, x2
	lsr x2, x10, #55
	adcs x8, x8, x2
	adcs x9, x9, x7
	movz x10, #0, lsl #0
	ldr x1, [x28, #24]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	mul x2, x1, x6
	adcs x15, x15, x2
	mul x2, x1, x24
	adcs x21, x21, x2
	mul x2, x1, x25
	adcs x22, x22, x2
	mul x2, x1, x26
	adcs x23, x23, x2
	mul x2, x1, x27
	adcs x8, x8, x2
	umulh x2, x1, x27
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	umulh x2, x1, x6
	adcs x21, x21, x2
	umulh x2, x1, x24
	adcs x22, x22, x2
	umulh x2, x1, x25
	adcs x23, x23, x2
	umulh x2, x1, x26
	adcs x8, x8, x2
	adcs x9, x9, x7
	lsl x2, x11, #9
	adds x8, x8, x2
	lsr x2, x11, #55
	adcs x9, x9, x2
	adcs x10, x10, x7
	movz x11, #0, lsl #0
	ldr x1, [x28, #32]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	mul x2, x1, x6
	adcs x21, x21, x2
	mul x2, x1, x24
	adcs x22, x22, x2
	mul x2, x1, x25
	adcs x23, x23, x2
	mul x2, x1, x26
	adcs x8, x8, x2
	mul x2, x1, x27
	adcs x9, x9, x2
	umulh x2, x1, x27
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	umulh x2, x1, x6
	adcs x22, x22, x2
	umulh x2, x1, x24
	adcs x23, x23, x2
	umulh x2, x1, x25
	adcs x8, x8, x2
	umulh x2, x1, x26
	adcs x9, x9, x2
	adcs x10, x10, x7
	lsl x2, x12, #9
	adds x9, x9, x2
	lsr x2, x12, #55
	adcs x10, x10, x2
	adcs x11, x11, x7
	movz x12, #0, lsl #0
	ldr x1, [x28, #40]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	mul x2, x1, x6
	adcs x22, x22, x2
	mul x2, x1, x24
	adcs x23, x23, x2
	mul x2, x1, x25
	adcs x8, x8, x2
	mul x2, x1, x26
	adcs x9, x9, x2
	mul x2, x1, x27
	adcs x10, x10, x2
	umulh x2, x1, x27
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	umulh x2, x1, x6
	adcs x23, x23, x2
	umulh x2, x1, x24
	adcs x8, x8, x2
	umulh x2, x1, x25
	adcs x9, x9, x2
	umulh x2, x1, x26
	adcs x10, x10, x2
	adcs x11, x11, x7
	lsl x2, x13, #9
	adds x10, x10, x2
	lsr x2, x13, #55
	adcs x11, x11, x2
	adcs x12, x12, x7
	movz x13, #0, lsl #0
	ldr x1, [x28, #48]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	mul x2, x1, x6
	adcs x23, x23, x2
	mul x2, x1, x24
	adcs x8, x8, x2
	mul x2, x1, x25
	adcs x9, x9, x2
	mul x2, x1, x26
	adcs x10, x10, x2
	mul x2, x1, x27
	adcs x11, x11, x2
	umulh x2, x1, x27
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	umulh x2, x1, x6
	adcs x8, x8, x2
	umulh x2, x1, x24
	adcs x9, x9, x2
	umulh x2, x1, x25
	adcs x10, x10, x2
	umulh x2, x1, x26
	adcs x11, x11, x2
	adcs x12, x12, x7
	lsl x2, x14, #9
	adds x11, x11, x2
	lsr x2, x14, #55
	adcs x12, x12, x2
	adcs x13, x13, x7
	movz x14, #0, lsl #0
	ldr x1, [x28, #56]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x23, x23, x2
	mul x2, x1, x6
	adcs x8, x8, x2
	mul x2, x1, x24
	adcs x9, x9, x2
	mul x2, x1, x25
	adcs x10, x10, x2
	mul x2, x1, x26
	adcs x11, x11, x2
	mul x2, x1, x27
	adcs x12, x12, x2
	umulh x2, x1, x27
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x23, x23, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	umulh x2, x1, x6
	adcs x9, x9, x2
	umulh x2, x1, x24
	adcs x10, x10, x2
	umulh x2, x1, x25
	adcs x11, x11, x2
	umulh x2, x1, x26
	adcs x12, x12, x2
	adcs x13, x13, x7
	lsl x2, x15, #9
	adds x12, x12, x2
	lsr x2, x15, #55
	adcs x13, x13, x2
	adcs x14, x14, x7
	movz x15, #0, lsl #0
	ldr x1, [x28, #64]
	mul x2, x1, x4
	adds x21, x21, x2
	mul x2, x1, x5
	adcs x22, x22, x2
	mul x2, x1, x16
	adcs x23, x23, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	mul x2, x1, x6
	adcs x9, x9, x2
	mul x2, x1, x24
	adcs x10, x10, x2
	mul x2, x1, x25
	adcs x11, x11, x2
	mul x2, x1, x26
	adcs x12, x12, x2
	mul x2, x1, x27
	adcs x13, x13, x2
	umulh x2, x1, x27
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x22, x22, x2
	umulh x2, x1, x5
	adcs x23, x23, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	umulh x2, x1, x6
	adcs x10, x10, x2
	umulh x2, x1, x24
	adcs x11, x11, x2
	umulh x2, x1, x25
	adcs x12, x12, x2
	umulh x2, x1, x26
	adcs x13, x13, x2
	adcs x14, x14, x7
	lsl x2, x21, #9
	adds x13, x13, x2
	lsr x2, x21, #55
	adcs x14, x14, x2
	adcs x15, x15, x7
	movz x21, #0, lsl #0
	movz x26, #65535, lsl #0
	movk x26, #65535, lsl #16
	movk x26, #65535, lsl #32
	movk x26, #65535, lsl #48
	movz x27, #511, lsl #0
	movk x27, #0, lsl #16
	movk x27, #0, lsl #32
	movk x27, #0, lsl #48
	subs x1, x22, x26
	sbcs x3, x23, x26
	sbcs x4, x8, x26
	sbcs x5, x9, x26
	sbcs x6, x10, x26
	sbcs x16, x11, x26
	sbcs x17, x12, x26
	sbcs x24, x13, x26
	sbcs x25, x14, x27
	sbcs x2, x15, x7
	csel x22, x1, x22, hs
	csel x23, x3, x23, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	csel x14, x25, x14, hs
	str x22, [x30, #0]
	str x23, [x30, #8]
	str x8, [x30, #16]
	str x9, [x30, #24]
	str x10, [x30, #32]
	str x11, [x30, #40]
	str x12, [x30, #48]
	str x13, [x30, #56]
	str x14, [x30, #64]
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

vg_p521_mul_mod_n:
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
	add x26, x0, x2
	add x27, x0, x3
	movz x1, #25609, lsl #0
	movk x1, #37176, lsl #16
	movk x1, #46878, lsl #32
	movk x1, #47983, lsl #48
	str x1, [x0, #3952]
	movz x1, #18350, lsl #0
	movk x1, #35228, lsl #16
	movk x1, #51640, lsl #32
	movk x1, #15285, lsl #48
	str x1, [x0, #3960]
	movz x1, #42448, lsl #0
	movk x1, #63241, lsl #16
	movk x1, #328, lsl #32
	movk x1, #32716, lsl #48
	str x1, [x0, #3968]
	movz x1, #38507, lsl #0
	movk x1, #48943, lsl #16
	movk x1, #34691, lsl #32
	movk x1, #20870, lsl #48
	str x1, [x0, #3976]
	movz x1, #65530, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #3984]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #3992]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #4000]
	movz x1, #65535, lsl #0
	movk x1, #65535, lsl #16
	movk x1, #65535, lsl #32
	movk x1, #65535, lsl #48
	str x1, [x0, #4008]
	movz x1, #511, lsl #0
	movk x1, #0, lsl #16
	movk x1, #0, lsl #32
	movk x1, #0, lsl #48
	str x1, [x0, #4016]
	movz x7, #0, lsl #0
	ldr x4, [x27, #0]
	ldr x5, [x27, #8]
	ldr x16, [x27, #16]
	ldr x17, [x27, #24]
	movz x6, #38343, lsl #0
	movk x6, #31145, lsl #16
	movk x6, #23757, lsl #32
	movk x6, #7471, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x21, #0, lsl #0
	movz x22, #0, lsl #0
	movz x23, #0, lsl #0
	ldr x1, [x26, #0]
	mul x2, x1, x4
	adds x8, x8, x2
	mul x2, x1, x5
	adcs x9, x9, x2
	mul x2, x1, x16
	adcs x10, x10, x2
	mul x2, x1, x17
	adcs x11, x11, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x22, x22, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	mul x1, x8, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x21, x21, x2
	adcs x22, x22, x7
	adcs x23, x23, x7
	ldr x1, [x26, #8]
	mul x2, x1, x4
	adds x9, x9, x2
	mul x2, x1, x5
	adcs x10, x10, x2
	mul x2, x1, x16
	adcs x11, x11, x2
	mul x2, x1, x17
	adcs x12, x12, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x23, x23, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	mul x1, x9, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x22, x22, x2
	adcs x23, x23, x7
	adcs x8, x8, x7
	ldr x1, [x26, #16]
	mul x2, x1, x4
	adds x10, x10, x2
	mul x2, x1, x5
	adcs x11, x11, x2
	mul x2, x1, x16
	adcs x12, x12, x2
	mul x2, x1, x17
	adcs x13, x13, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x8, x8, x2
	umulh x2, x1, x4
	adds x11, x11, x2
	umulh x2, x1, x5
	adcs x12, x12, x2
	umulh x2, x1, x16
	adcs x13, x13, x2
	umulh x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x23, x23, x2
	adcs x8, x8, x7
	adcs x9, x9, x7
	ldr x1, [x26, #24]
	mul x2, x1, x4
	adds x11, x11, x2
	mul x2, x1, x5
	adcs x12, x12, x2
	mul x2, x1, x16
	adcs x13, x13, x2
	mul x2, x1, x17
	adcs x14, x14, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	adcs x10, x10, x7
	ldr x1, [x26, #32]
	mul x2, x1, x4
	adds x12, x12, x2
	mul x2, x1, x5
	adcs x13, x13, x2
	mul x2, x1, x16
	adcs x14, x14, x2
	mul x2, x1, x17
	adcs x15, x15, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x15, x15, x2
	umulh x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x1, [x26, #40]
	mul x2, x1, x4
	adds x13, x13, x2
	mul x2, x1, x5
	adcs x14, x14, x2
	mul x2, x1, x16
	adcs x15, x15, x2
	mul x2, x1, x17
	adcs x21, x21, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x11, x11, x2
	umulh x2, x1, x4
	adds x14, x14, x2
	umulh x2, x1, x5
	adcs x15, x15, x2
	umulh x2, x1, x16
	adcs x21, x21, x2
	umulh x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	mul x1, x13, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	adcs x12, x12, x7
	ldr x1, [x26, #48]
	mul x2, x1, x4
	adds x14, x14, x2
	mul x2, x1, x5
	adcs x15, x15, x2
	mul x2, x1, x16
	adcs x21, x21, x2
	mul x2, x1, x17
	adcs x22, x22, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x12, x12, x2
	umulh x2, x1, x4
	adds x15, x15, x2
	umulh x2, x1, x5
	adcs x21, x21, x2
	umulh x2, x1, x16
	adcs x22, x22, x2
	umulh x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	mul x1, x14, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x14, x14, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x15, x15, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x11, x11, x2
	adcs x12, x12, x7
	adcs x13, x13, x7
	ldr x1, [x26, #56]
	mul x2, x1, x4
	adds x15, x15, x2
	mul x2, x1, x5
	adcs x21, x21, x2
	mul x2, x1, x16
	adcs x22, x22, x2
	mul x2, x1, x17
	adcs x23, x23, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x21, x21, x2
	umulh x2, x1, x5
	adcs x22, x22, x2
	umulh x2, x1, x16
	adcs x23, x23, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x15, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x15, x15, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x21, x21, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
	ldr x1, [x26, #64]
	mul x2, x1, x4
	adds x21, x21, x2
	mul x2, x1, x5
	adcs x22, x22, x2
	mul x2, x1, x16
	adcs x23, x23, x2
	mul x2, x1, x17
	adcs x8, x8, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #40]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #48]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x27, #56]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x27, #64]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x27, #64]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x22, x22, x2
	umulh x2, x1, x5
	adcs x23, x23, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x27, #40]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x27, #48]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x27, #56]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x1, x21, x6
	ldr x3, [x0, #3952]
	mul x2, x1, x3
	adds x21, x21, x2
	ldr x3, [x0, #3960]
	mul x2, x1, x3
	adcs x22, x22, x2
	ldr x3, [x0, #3968]
	mul x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3976]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3984]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3992]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4000]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4008]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x15, x15, x7
	ldr x3, [x0, #3952]
	umulh x2, x1, x3
	adds x22, x22, x2
	ldr x3, [x0, #3960]
	umulh x2, x1, x3
	adcs x23, x23, x2
	ldr x3, [x0, #3968]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #3976]
	umulh x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #3984]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #3992]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4000]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4008]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	adcs x15, x15, x7
	ldr x2, [x0, #3952]
	subs x1, x22, x2
	ldr x2, [x0, #3960]
	sbcs x3, x23, x2
	ldr x2, [x0, #3968]
	sbcs x4, x8, x2
	ldr x2, [x0, #3976]
	sbcs x5, x9, x2
	ldr x2, [x0, #3984]
	sbcs x6, x10, x2
	ldr x2, [x0, #3992]
	sbcs x16, x11, x2
	ldr x2, [x0, #4000]
	sbcs x17, x12, x2
	ldr x2, [x0, #4008]
	sbcs x24, x13, x2
	ldr x2, [x0, #4016]
	sbcs x25, x14, x2
	sbcs x2, x15, x7
	csel x22, x1, x22, hs
	csel x23, x3, x23, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	csel x11, x16, x11, hs
	csel x12, x17, x12, hs
	csel x13, x24, x13, hs
	csel x14, x25, x14, hs
	str x22, [x28, #0]
	str x23, [x28, #8]
	str x8, [x28, #16]
	str x9, [x28, #24]
	str x10, [x28, #32]
	str x11, [x28, #40]
	str x12, [x28, #48]
	str x13, [x28, #56]
	str x14, [x28, #64]
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
