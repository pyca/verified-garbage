// The functions of `src/internal/vg_ed25519_scalar_mul_add.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed25519_scalar_mul_add:
	str x19, [x4, #0]
	str x20, [x4, #8]
	str x21, [x4, #16]
	str x22, [x4, #24]
	str x23, [x4, #32]
	str x24, [x4, #40]
	add x19, x0, #0
	add x0, x4, #0
	ldr x4, [x2, #0]
	ldr x5, [x2, #8]
	ldr x6, [x2, #16]
	ldr x7, [x2, #24]
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	ldr x4, [x3, #0]
	ldr x5, [x3, #8]
	ldr x6, [x3, #16]
	ldr x7, [x3, #24]
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	ldr x4, [x1, #0]
	ldr x5, [x1, #8]
	ldr x6, [x1, #16]
	ldr x7, [x1, #24]
	movz w10, #0, lsl #0
	ldr x3, [x0, #64]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x4, x4, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x5, x5, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x21, x20, #0
	ldr x3, [x0, #72]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x5, x5, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x22, x20, #0
	ldr x3, [x0, #80]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x6, x6, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x22, x22, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x23, x20, #0
	ldr x3, [x0, #88]
	movz w20, #0, lsl #0
	ldr x9, [x0, #96]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x7, x7, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #104]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x21, x21, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #112]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x22, x22, x8
	adcs x2, x2, x10
	add x20, x2, #0
	ldr x9, [x0, #120]
	mul x8, x3, x9
	umulh x2, x3, x9
	adds x8, x8, x20
	adcs x2, x2, x10
	adds x23, x23, x8
	adcs x2, x2, x10
	add x20, x2, #0
	add x24, x20, #0
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	str x21, [x0, #160]
	str x22, [x0, #168]
	str x23, [x0, #176]
	str x24, [x0, #184]
	add x1, x0, #128
	add x2, x0, #0
	add x0, x19, #0
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
