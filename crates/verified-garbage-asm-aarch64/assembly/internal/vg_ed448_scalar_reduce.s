// The functions of `src/internal/vg_ed448_scalar_reduce.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ed448_scalar_reduce:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	str x25, [x2, #48]
	str x26, [x2, #56]
	movz x21, #47885, lsl #0
	movk x21, #21671, lsl #16
	movk x21, #15725, lsl #32
	movk x21, #56455, lsl #48
	movz x22, #28842, lsl #0
	movk x22, #29242, lsl #16
	movk x22, #15757, lsl #32
	movk x22, #56979, lsl #48
	movz x23, #51567, lsl #0
	movk x23, #20777, lsl #16
	movk x23, #9398, lsl #32
	movk x23, #15281, lsl #48
	movz x24, #56342, lsl #0
	movk x24, #33589, lsl #16
	movk x24, #0, lsl #32
	movk x24, #0, lsl #48
	movz x25, #49152, lsl #48
	movz x26, #0, lsl #0
	ldrb w5, [x1, #112]
	ldrb w12, [x1, #113]
	lsl x12, x12, #8
	add x5, x5, x12
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x3, #112, lsl #0
20:
	sub x3, x3, #8
	add x4, x1, x3
	ldr x4, [x4, #0]
	extr x11, x11, x10, #62
	lsl x10, x10, #2
	lsr x10, x10, #2
	mul x12, x11, x21
	umulh x16, x11, x21
	mul x13, x11, x22
	umulh x17, x11, x22
	mul x14, x11, x23
	umulh x19, x11, x23
	mul x15, x11, x24
	umulh x20, x11, x24
	adds x13, x13, x16
	adcs x14, x14, x17
	adcs x15, x15, x19
	adcs x20, x20, x26
	adds x4, x4, x12
	adcs x5, x5, x13
	adcs x6, x6, x14
	adcs x7, x7, x15
	adcs x8, x8, x20
	adcs x9, x9, x26
	adcs x10, x10, x26
	adds x12, x4, x21
	adcs x13, x5, x22
	adcs x14, x6, x23
	adcs x15, x7, x24
	adcs x16, x8, x26
	adcs x17, x9, x26
	adcs x19, x10, x25
	sbcs x20, x26, x26
	eor x10, x10, x19
	and x10, x10, x20
	eor x11, x19, x10
	eor x9, x9, x17
	and x9, x9, x20
	eor x10, x17, x9
	eor x8, x8, x16
	and x8, x8, x20
	eor x9, x16, x8
	eor x7, x7, x15
	and x7, x7, x20
	eor x8, x15, x7
	eor x6, x6, x14
	and x6, x6, x20
	eor x7, x14, x6
	eor x5, x5, x13
	and x5, x5, x20
	eor x6, x13, x5
	eor x4, x4, x12
	and x4, x4, x20
	eor x5, x12, x4
	cbnz x3, 20b
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	ldr x25, [x2, #48]
	ldr x26, [x2, #56]
	str x5, [x0, #0]
	str x6, [x0, #8]
	str x7, [x0, #16]
	str x8, [x0, #24]
	str x9, [x0, #32]
	str x10, [x0, #40]
	str x11, [x0, #48]
	movz x12, #0, lsl #0
	strb w12, [x0, #56]
	ret
	.p2align 6
