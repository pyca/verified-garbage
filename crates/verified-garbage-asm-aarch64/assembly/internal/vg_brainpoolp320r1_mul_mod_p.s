// The functions of `src/internal/vg_brainpoolp320r1_mul_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_brainpoolp320r1_mul_mod_p:
	add w1, w1, #0
	add w2, w2, #0
	add w3, w3, #0
	mov v16.d[0], x26
	mov v16.d[1], x27
	mov v17.d[0], x28
	add x28, x0, x1
	add x26, x0, x2
	add x27, x0, x3
	movz x1, #11815, lsl #0
	movk x1, #61875, lsl #16
	movk x1, #4785, lsl #32
	movk x1, #64724, lsl #48
	str x1, [x0, #4016]
	movz x1, #60456, lsl #0
	movk x1, #30867, lsl #16
	movk x1, #47596, lsl #32
	movk x1, #20370, lsl #48
	str x1, [x0, #4024]
	movz x1, #3567, lsl #0
	movk x1, #63220, lsl #16
	movk x1, #53158, lsl #32
	movk x1, #63887, lsl #48
	str x1, [x0, #4032]
	movz x1, #57445, lsl #0
	movk x1, #53761, lsl #16
	movk x1, #30814, lsl #32
	movk x1, #57660, lsl #48
	str x1, [x0, #4040]
	movz x1, #20407, lsl #0
	movk x1, #14012, lsl #16
	movk x1, #18208, lsl #32
	movk x1, #54110, lsl #48
	str x1, [x0, #4048]
	movz x7, #0, lsl #0
	ldr x4, [x27, #0]
	ldr x5, [x27, #8]
	ldr x16, [x27, #16]
	ldr x17, [x27, #24]
	movz x6, #40553, lsl #0
	movk x6, #10890, lsl #16
	movk x6, #39842, lsl #32
	movk x6, #15646, lsl #48
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
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
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x13, x13, x2
	umulh x2, x1, x4
	adds x9, x9, x2
	umulh x2, x1, x5
	adcs x10, x10, x2
	umulh x2, x1, x16
	adcs x11, x11, x2
	umulh x2, x1, x17
	adcs x12, x12, x2
	adcs x13, x13, x7
	mul x1, x8, x6
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adds x8, x8, x2
	ldr x3, [x0, #4024]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4032]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4040]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4048]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4048]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #4024]
	umulh x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4032]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4040]
	umulh x2, x1, x3
	adcs x12, x12, x2
	adcs x13, x13, x7
	adcs x14, x14, x7
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
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x14, x14, x2
	umulh x2, x1, x4
	adds x10, x10, x2
	umulh x2, x1, x5
	adcs x11, x11, x2
	umulh x2, x1, x16
	adcs x12, x12, x2
	umulh x2, x1, x17
	adcs x13, x13, x2
	adcs x14, x14, x7
	mul x1, x9, x6
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adds x9, x9, x2
	ldr x3, [x0, #4024]
	mul x2, x1, x3
	adcs x10, x10, x2
	ldr x3, [x0, #4032]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4040]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4048]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4048]
	umulh x2, x1, x3
	adcs x14, x14, x2
	adcs x8, x8, x7
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #4024]
	umulh x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4032]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4040]
	umulh x2, x1, x3
	adcs x13, x13, x2
	adcs x14, x14, x7
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
	ldr x3, [x27, #32]
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
	adcs x8, x8, x7
	mul x1, x10, x6
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adds x10, x10, x2
	ldr x3, [x0, #4024]
	mul x2, x1, x3
	adcs x11, x11, x2
	ldr x3, [x0, #4032]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4040]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4048]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4048]
	umulh x2, x1, x3
	adcs x8, x8, x2
	adcs x9, x9, x7
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #4024]
	umulh x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4032]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4040]
	umulh x2, x1, x3
	adcs x14, x14, x2
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
	adcs x8, x8, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x9, x9, x2
	umulh x2, x1, x4
	adds x12, x12, x2
	umulh x2, x1, x5
	adcs x13, x13, x2
	umulh x2, x1, x16
	adcs x14, x14, x2
	umulh x2, x1, x17
	adcs x8, x8, x2
	adcs x9, x9, x7
	mul x1, x11, x6
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adds x11, x11, x2
	ldr x3, [x0, #4024]
	mul x2, x1, x3
	adcs x12, x12, x2
	ldr x3, [x0, #4032]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4040]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4048]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4048]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #4024]
	umulh x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4032]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4040]
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
	adcs x8, x8, x2
	ldr x3, [x27, #32]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x27, #32]
	umulh x2, x1, x3
	adcs x10, x10, x2
	umulh x2, x1, x4
	adds x13, x13, x2
	umulh x2, x1, x5
	adcs x14, x14, x2
	umulh x2, x1, x16
	adcs x8, x8, x2
	umulh x2, x1, x17
	adcs x9, x9, x2
	adcs x10, x10, x7
	mul x1, x12, x6
	ldr x3, [x0, #4016]
	mul x2, x1, x3
	adds x12, x12, x2
	ldr x3, [x0, #4024]
	mul x2, x1, x3
	adcs x13, x13, x2
	ldr x3, [x0, #4032]
	mul x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4040]
	mul x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4048]
	mul x2, x1, x3
	adcs x9, x9, x2
	ldr x3, [x0, #4048]
	umulh x2, x1, x3
	adcs x10, x10, x2
	adcs x11, x11, x7
	ldr x3, [x0, #4016]
	umulh x2, x1, x3
	adds x13, x13, x2
	ldr x3, [x0, #4024]
	umulh x2, x1, x3
	adcs x14, x14, x2
	ldr x3, [x0, #4032]
	umulh x2, x1, x3
	adcs x8, x8, x2
	ldr x3, [x0, #4040]
	umulh x2, x1, x3
	adcs x9, x9, x2
	adcs x10, x10, x7
	adcs x11, x11, x7
	ldr x2, [x0, #4016]
	subs x1, x13, x2
	ldr x2, [x0, #4024]
	sbcs x3, x14, x2
	ldr x2, [x0, #4032]
	sbcs x4, x8, x2
	ldr x2, [x0, #4040]
	sbcs x5, x9, x2
	ldr x2, [x0, #4048]
	sbcs x6, x10, x2
	sbcs x2, x11, x7
	csel x13, x1, x13, hs
	csel x14, x3, x14, hs
	csel x8, x4, x8, hs
	csel x9, x5, x9, hs
	csel x10, x6, x10, hs
	str x13, [x28, #0]
	str x14, [x28, #8]
	str x8, [x28, #16]
	str x9, [x28, #24]
	str x10, [x28, #32]
	umov x26, v16.d[0]
	umov x27, v16.d[1]
	umov x28, v17.d[0]
	ret
	.p2align 6
