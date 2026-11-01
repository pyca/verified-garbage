// The functions of `src/internal/vg_poly1305_finalize_scratch.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
