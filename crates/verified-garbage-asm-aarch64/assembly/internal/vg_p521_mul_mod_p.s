// The functions of `src/internal/vg_p521_mul_mod_p.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
