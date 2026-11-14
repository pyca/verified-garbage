// The functions of `src/internal/vg_p521_normal_mul.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_p521_normal_mul:
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
	add x28, x0, #0
	add x27, x0, #3952
	add x4, x0, x1
	add x1, x0, x2
	add x2, x0, x3
	add x0, x4, #0
	ldr x3, [x1, #0]
	ldr x4, [x1, #8]
	ldr x5, [x2, #0]
	ldr x6, [x2, #8]
	mul x15, x3, x5
	umulh x16, x3, x5
	mul x14, x3, x6
	umulh x17, x3, x6
	adds x16, x16, x14
	ldr x7, [x2, #16]
	ldr x8, [x2, #24]
	mul x14, x3, x7
	umulh x19, x3, x7
	adcs x17, x17, x14
	mul x14, x3, x8
	umulh x20, x3, x8
	adcs x19, x19, x14
	ldr x9, [x2, #32]
	ldr x10, [x2, #40]
	mul x14, x3, x9
	umulh x21, x3, x9
	adcs x20, x20, x14
	mul x14, x3, x10
	umulh x22, x3, x10
	adcs x21, x21, x14
	ldr x11, [x2, #48]
	ldr x12, [x2, #56]
	mul x14, x3, x11
	umulh x23, x3, x11
	adcs x22, x22, x14
	ldr x13, [x2, #64]
	mul x14, x3, x12
	umulh x24, x3, x12
	adcs x23, x23, x14
	mul x14, x3, x13
	umulh x25, x3, x13
	adcs x24, x24, x14
	movz x2, #0, lsl #0
	adc x25, x25, x2
	mul x14, x4, x5
	adds x16, x16, x14
	mul x14, x4, x6
	adcs x17, x17, x14
	mul x14, x4, x7
	adcs x19, x19, x14
	mul x14, x4, x8
	adcs x20, x20, x14
	mul x14, x4, x9
	adcs x21, x21, x14
	mul x14, x4, x10
	adcs x22, x22, x14
	mul x14, x4, x11
	adcs x23, x23, x14
	mul x14, x4, x12
	adcs x24, x24, x14
	mul x14, x4, x13
	adcs x25, x25, x14
	movz x26, #1, lsl #0
	csel x26, x26, x2, hs
	umulh x14, x4, x5
	adds x17, x17, x14
	umulh x14, x4, x6
	adcs x19, x19, x14
	umulh x14, x4, x7
	adcs x20, x20, x14
	umulh x14, x4, x8
	adcs x21, x21, x14
	umulh x14, x4, x9
	adcs x22, x22, x14
	umulh x14, x4, x10
	adcs x23, x23, x14
	umulh x14, x4, x11
	adcs x24, x24, x14
	umulh x14, x4, x12
	adcs x25, x25, x14
	umulh x14, x4, x13
	adc x26, x26, x14
	str x15, [x27, #0]
	str x16, [x27, #8]
	ldr x3, [x1, #16]
	ldr x4, [x1, #24]
	mul x14, x3, x5
	adds x17, x17, x14
	mul x14, x3, x6
	adcs x19, x19, x14
	mul x14, x3, x7
	adcs x20, x20, x14
	mul x14, x3, x8
	adcs x21, x21, x14
	mul x14, x3, x9
	adcs x22, x22, x14
	mul x14, x3, x10
	adcs x23, x23, x14
	mul x14, x3, x11
	adcs x24, x24, x14
	mul x14, x3, x12
	adcs x25, x25, x14
	mul x14, x3, x13
	adcs x26, x26, x14
	movz x15, #1, lsl #0
	csel x15, x15, x2, hs
	umulh x14, x3, x5
	adds x19, x19, x14
	umulh x14, x3, x6
	adcs x20, x20, x14
	umulh x14, x3, x7
	adcs x21, x21, x14
	umulh x14, x3, x8
	adcs x22, x22, x14
	umulh x14, x3, x9
	adcs x23, x23, x14
	umulh x14, x3, x10
	adcs x24, x24, x14
	umulh x14, x3, x11
	adcs x25, x25, x14
	umulh x14, x3, x12
	adcs x26, x26, x14
	umulh x14, x3, x13
	adc x15, x15, x14
	mul x14, x4, x5
	adds x19, x19, x14
	mul x14, x4, x6
	adcs x20, x20, x14
	mul x14, x4, x7
	adcs x21, x21, x14
	mul x14, x4, x8
	adcs x22, x22, x14
	mul x14, x4, x9
	adcs x23, x23, x14
	mul x14, x4, x10
	adcs x24, x24, x14
	mul x14, x4, x11
	adcs x25, x25, x14
	mul x14, x4, x12
	adcs x26, x26, x14
	mul x14, x4, x13
	adcs x15, x15, x14
	movz x16, #1, lsl #0
	csel x16, x16, x2, hs
	umulh x14, x4, x5
	adds x20, x20, x14
	umulh x14, x4, x6
	adcs x21, x21, x14
	umulh x14, x4, x7
	adcs x22, x22, x14
	umulh x14, x4, x8
	adcs x23, x23, x14
	umulh x14, x4, x9
	adcs x24, x24, x14
	umulh x14, x4, x10
	adcs x25, x25, x14
	umulh x14, x4, x11
	adcs x26, x26, x14
	umulh x14, x4, x12
	adcs x15, x15, x14
	umulh x14, x4, x13
	adc x16, x16, x14
	str x17, [x27, #16]
	str x19, [x27, #24]
	ldr x3, [x1, #32]
	ldr x4, [x1, #40]
	mul x14, x3, x5
	adds x20, x20, x14
	mul x14, x3, x6
	adcs x21, x21, x14
	mul x14, x3, x7
	adcs x22, x22, x14
	mul x14, x3, x8
	adcs x23, x23, x14
	mul x14, x3, x9
	adcs x24, x24, x14
	mul x14, x3, x10
	adcs x25, x25, x14
	mul x14, x3, x11
	adcs x26, x26, x14
	mul x14, x3, x12
	adcs x15, x15, x14
	mul x14, x3, x13
	adcs x16, x16, x14
	movz x17, #1, lsl #0
	csel x17, x17, x2, hs
	umulh x14, x3, x5
	adds x21, x21, x14
	umulh x14, x3, x6
	adcs x22, x22, x14
	umulh x14, x3, x7
	adcs x23, x23, x14
	umulh x14, x3, x8
	adcs x24, x24, x14
	umulh x14, x3, x9
	adcs x25, x25, x14
	umulh x14, x3, x10
	adcs x26, x26, x14
	umulh x14, x3, x11
	adcs x15, x15, x14
	umulh x14, x3, x12
	adcs x16, x16, x14
	umulh x14, x3, x13
	adc x17, x17, x14
	mul x14, x4, x5
	adds x21, x21, x14
	mul x14, x4, x6
	adcs x22, x22, x14
	mul x14, x4, x7
	adcs x23, x23, x14
	mul x14, x4, x8
	adcs x24, x24, x14
	mul x14, x4, x9
	adcs x25, x25, x14
	mul x14, x4, x10
	adcs x26, x26, x14
	mul x14, x4, x11
	adcs x15, x15, x14
	mul x14, x4, x12
	adcs x16, x16, x14
	mul x14, x4, x13
	adcs x17, x17, x14
	movz x19, #1, lsl #0
	csel x19, x19, x2, hs
	umulh x14, x4, x5
	adds x22, x22, x14
	umulh x14, x4, x6
	adcs x23, x23, x14
	umulh x14, x4, x7
	adcs x24, x24, x14
	umulh x14, x4, x8
	adcs x25, x25, x14
	umulh x14, x4, x9
	adcs x26, x26, x14
	umulh x14, x4, x10
	adcs x15, x15, x14
	umulh x14, x4, x11
	adcs x16, x16, x14
	umulh x14, x4, x12
	adcs x17, x17, x14
	umulh x14, x4, x13
	adc x19, x19, x14
	str x20, [x27, #32]
	str x21, [x27, #40]
	ldr x3, [x1, #48]
	ldr x4, [x1, #56]
	mul x14, x3, x5
	adds x22, x22, x14
	mul x14, x3, x6
	adcs x23, x23, x14
	mul x14, x3, x7
	adcs x24, x24, x14
	mul x14, x3, x8
	adcs x25, x25, x14
	mul x14, x3, x9
	adcs x26, x26, x14
	mul x14, x3, x10
	adcs x15, x15, x14
	mul x14, x3, x11
	adcs x16, x16, x14
	mul x14, x3, x12
	adcs x17, x17, x14
	mul x14, x3, x13
	adcs x19, x19, x14
	movz x20, #1, lsl #0
	csel x20, x20, x2, hs
	umulh x14, x3, x5
	adds x23, x23, x14
	umulh x14, x3, x6
	adcs x24, x24, x14
	umulh x14, x3, x7
	adcs x25, x25, x14
	umulh x14, x3, x8
	adcs x26, x26, x14
	umulh x14, x3, x9
	adcs x15, x15, x14
	umulh x14, x3, x10
	adcs x16, x16, x14
	umulh x14, x3, x11
	adcs x17, x17, x14
	umulh x14, x3, x12
	adcs x19, x19, x14
	umulh x14, x3, x13
	adc x20, x20, x14
	mul x14, x4, x5
	adds x23, x23, x14
	mul x14, x4, x6
	adcs x24, x24, x14
	mul x14, x4, x7
	adcs x25, x25, x14
	mul x14, x4, x8
	adcs x26, x26, x14
	mul x14, x4, x9
	adcs x15, x15, x14
	mul x14, x4, x10
	adcs x16, x16, x14
	mul x14, x4, x11
	adcs x17, x17, x14
	mul x14, x4, x12
	adcs x19, x19, x14
	mul x14, x4, x13
	adcs x20, x20, x14
	movz x21, #1, lsl #0
	csel x21, x21, x2, hs
	umulh x14, x4, x5
	adds x24, x24, x14
	umulh x14, x4, x6
	adcs x25, x25, x14
	umulh x14, x4, x7
	adcs x26, x26, x14
	umulh x14, x4, x8
	adcs x15, x15, x14
	umulh x14, x4, x9
	adcs x16, x16, x14
	umulh x14, x4, x10
	adcs x17, x17, x14
	umulh x14, x4, x11
	adcs x19, x19, x14
	umulh x14, x4, x12
	adcs x20, x20, x14
	umulh x14, x4, x13
	adc x21, x21, x14
	str x22, [x27, #48]
	str x23, [x27, #56]
	ldr x3, [x1, #64]
	mul x14, x3, x5
	adds x24, x24, x14
	mul x14, x3, x6
	adcs x25, x25, x14
	mul x14, x3, x7
	adcs x26, x26, x14
	mul x14, x3, x8
	adcs x15, x15, x14
	mul x14, x3, x9
	adcs x16, x16, x14
	mul x14, x3, x10
	adcs x17, x17, x14
	mul x14, x3, x11
	adcs x19, x19, x14
	mul x14, x3, x12
	adcs x20, x20, x14
	mul x14, x3, x13
	adc x21, x21, x14
	umulh x14, x3, x5
	adds x25, x25, x14
	umulh x14, x3, x6
	adcs x26, x26, x14
	umulh x14, x3, x7
	adcs x15, x15, x14
	umulh x14, x3, x8
	adcs x16, x16, x14
	umulh x14, x3, x9
	adcs x17, x17, x14
	umulh x14, x3, x10
	adcs x19, x19, x14
	umulh x14, x3, x11
	adcs x20, x20, x14
	umulh x14, x3, x12
	adc x21, x21, x14
	subs x1, x1, x1
	ldr x5, [x27, #0]
	ldr x6, [x27, #8]
	extr x14, x25, x24, #9
	adcs x5, x5, x14
	extr x14, x26, x25, #9
	adcs x6, x6, x14
	ldr x7, [x27, #16]
	ldr x8, [x27, #24]
	extr x14, x15, x26, #9
	adcs x7, x7, x14
	extr x14, x16, x15, #9
	adcs x8, x8, x14
	ldr x9, [x27, #32]
	ldr x10, [x27, #40]
	extr x14, x17, x16, #9
	adcs x9, x9, x14
	extr x14, x19, x17, #9
	adcs x10, x10, x14
	ldr x11, [x27, #48]
	ldr x12, [x27, #56]
	extr x14, x20, x19, #9
	adcs x11, x11, x14
	extr x14, x21, x20, #9
	adcs x12, x12, x14
	sub x1, x2, #512
	orr x13, x24, x1
	lsr x14, x21, #9
	adcs x13, x13, x14
	sbcs x5, x5, x2
	sbcs x6, x6, x2
	sbcs x7, x7, x2
	sbcs x8, x8, x2
	sbcs x9, x9, x2
	sbcs x10, x10, x2
	sbcs x11, x11, x2
	sbcs x12, x12, x2
	sbc x13, x13, x2
	movz x1, #511, lsl #0
	and x13, x13, x1
	str x5, [x0, #0]
	str x6, [x0, #8]
	str x7, [x0, #16]
	str x8, [x0, #24]
	str x9, [x0, #32]
	str x10, [x0, #40]
	str x11, [x0, #48]
	str x12, [x0, #56]
	str x13, [x0, #64]
	add x0, x28, #0
	umov x27, v20.d[0]
	umov x28, v20.d[1]
	umov x25, v19.d[0]
	umov x26, v19.d[1]
	umov x23, v18.d[0]
	umov x24, v18.d[1]
	umov x21, v17.d[0]
	umov x22, v17.d[1]
	umov x19, v16.d[0]
	umov x20, v16.d[1]
	ret
	.p2align 6
