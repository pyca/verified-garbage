// The functions of `src/internal/vg_ed25519_scalar_reduce.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_reduce:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	movz w4, #0, lsl #0
	movz w5, #0, lsl #0
	movz w6, #0, lsl #0
	movz w7, #0, lsl #0
	movz w10, #0, lsl #0
	movz w19, #64, lsl #0
20:
	sub x19, x19, #8
	add x9, x1, x19
	ldr x3, [x9, #0]
	lsr x12, x6, #60
	lsl x13, x7, #4
	orr x12, x12, x13
	lsr x13, x7, #60
	lsl x7, x6, #4
	lsr x7, x7, #4
	add x6, x5, #0
	add x5, x4, #0
	add x4, x3, #0
	movz x8, #54253, lsl #0
	movk x8, #23797, lsl #16
	movk x8, #25370, lsl #32
	movk x8, #22546, lsl #48
	movz x17, #40150, lsl #0
	movk x17, #41719, lsl #16
	movk x17, #63966, lsl #32
	movk x17, #5342, lsl #48
	mul x14, x12, x8
	umulh x15, x12, x8
	mul x9, x12, x17
	umulh x16, x12, x17
	adds x15, x15, x9
	adcs x16, x16, x10
	mul x9, x13, x8
	mul x13, x13, x17
	adds x15, x15, x9
	adcs x16, x16, x13
	subs x14, x8, x14
	sbcs x15, x17, x15
	sbcs x16, x10, x16
	movz x9, #4096, lsl #48
	sbcs x9, x9, x10
	adds x4, x4, x14
	adcs x5, x5, x15
	adcs x6, x6, x16
	adcs x7, x7, x9
	add x21, x4, #0
	add x22, x5, #0
	add x23, x6, #0
	add x24, x7, #0
	movz x3, #54253, lsl #0
	movk x3, #23797, lsl #16
	movk x3, #25370, lsl #32
	movk x3, #22546, lsl #48
	subs x4, x4, x3
	movz x3, #40150, lsl #0
	movk x3, #41719, lsl #16
	movk x3, #63966, lsl #32
	movk x3, #5342, lsl #48
	sbcs x5, x5, x3
	sbcs x6, x6, x10
	movz x3, #0, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #4096, lsl #48
	sbcs x7, x7, x3
	sbcs x8, x10, x10
	eor x21, x21, x4
	and x21, x21, x8
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x8
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x8
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x8
	eor x7, x7, x24
	cbnz x19, 20b
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	ret
	.p2align 6
