// The functions of `src/internal/vg_mldsa_bit_unpack.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_unpack:
	movz x13, #57345, lsl #0
	movk x13, #127, lsl #16
	movk x13, #0, lsl #32
	movk x13, #0, lsl #48
	sub x9, x1, #96
	cbz x9, 20f
	sub x9, x1, #128
	cbz x9, 22f
	sub x9, x1, #416
	cbz x9, 24f
	sub x9, x1, #576
	cbz x9, 26f
	movz x12, #0, lsl #0
	movk x12, #8, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x15, #65535, lsl #0
	movk x15, #15, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #128, lsl #0
28:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	ldrb w10, [x0, #1]
	lsl x10, x10, #8
	add x9, x9, x10
	ldrb w10, [x0, #2]
	lsl x10, x10, #16
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #20
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #0]
	ldrb w10, [x0, #3]
	lsl x10, x10, #4
	add x9, x9, x10
	ldrb w10, [x0, #4]
	lsl x10, x10, #12
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #20
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #4]
	add x0, x0, #5
	add x4, x4, #8
	sub x11, x11, #1
	cbnz x11, 28b
	b 27f
26:
	movz x12, #0, lsl #0
	movk x12, #2, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x15, #65535, lsl #0
	movk x15, #3, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #64, lsl #0
29:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	ldrb w10, [x0, #1]
	lsl x10, x10, #8
	add x9, x9, x10
	ldrb w10, [x0, #2]
	lsl x10, x10, #16
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #18
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #0]
	ldrb w10, [x0, #3]
	lsl x10, x10, #6
	add x9, x9, x10
	ldrb w10, [x0, #4]
	lsl x10, x10, #14
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #18
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #4]
	ldrb w10, [x0, #5]
	lsl x10, x10, #4
	add x9, x9, x10
	ldrb w10, [x0, #6]
	lsl x10, x10, #12
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #18
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #8]
	ldrb w10, [x0, #7]
	lsl x10, x10, #2
	add x9, x9, x10
	ldrb w10, [x0, #8]
	lsl x10, x10, #10
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #18
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #12]
	add x0, x0, #9
	add x4, x4, #16
	sub x11, x11, #1
	cbnz x11, 29b
27:
	b 25f
24:
	movz x12, #4096, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x15, #8191, lsl #0
	movk x15, #0, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #32, lsl #0
210:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	ldrb w10, [x0, #1]
	lsl x10, x10, #8
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #0]
	ldrb w10, [x0, #2]
	lsl x10, x10, #3
	add x9, x9, x10
	ldrb w10, [x0, #3]
	lsl x10, x10, #11
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #4]
	ldrb w10, [x0, #4]
	lsl x10, x10, #6
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #8]
	ldrb w10, [x0, #5]
	lsl x10, x10, #1
	add x9, x9, x10
	ldrb w10, [x0, #6]
	lsl x10, x10, #9
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #12]
	ldrb w10, [x0, #7]
	lsl x10, x10, #4
	add x9, x9, x10
	ldrb w10, [x0, #8]
	lsl x10, x10, #12
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #16]
	ldrb w10, [x0, #9]
	lsl x10, x10, #7
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #20]
	ldrb w10, [x0, #10]
	lsl x10, x10, #2
	add x9, x9, x10
	ldrb w10, [x0, #11]
	lsl x10, x10, #10
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #24]
	ldrb w10, [x0, #12]
	lsl x10, x10, #5
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #13
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #28]
	add x0, x0, #13
	add x4, x4, #32
	sub x11, x11, #1
	cbnz x11, 210b
25:
	b 23f
22:
	movz x12, #4, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x15, #15, lsl #0
	movk x15, #0, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #128, lsl #0
211:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #4
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #0]
	and x10, x9, x15
	lsr x9, x9, #4
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #4]
	add x0, x0, #1
	add x4, x4, #8
	sub x11, x11, #1
	cbnz x11, 211b
23:
	b 21f
20:
	movz x12, #2, lsl #0
	movk x12, #0, lsl #16
	movk x12, #0, lsl #32
	movk x12, #0, lsl #48
	movz x15, #7, lsl #0
	movk x15, #0, lsl #16
	movk x15, #0, lsl #32
	movk x15, #0, lsl #48
	movz x11, #32, lsl #0
212:
	movz x9, #0, lsl #0
	ldrb w10, [x0, #0]
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #0]
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #4]
	ldrb w10, [x0, #1]
	lsl x10, x10, #2
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #8]
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #12]
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #16]
	ldrb w10, [x0, #2]
	lsl x10, x10, #1
	add x9, x9, x10
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #20]
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #24]
	and x10, x9, x15
	lsr x9, x9, #3
	sub x10, x12, x10
	lsr x14, x10, #63
	madd x10, x14, x13, x10
	str w10, [x4, #28]
	add x0, x0, #3
	add x4, x4, #32
	sub x11, x11, #1
	cbnz x11, 212b
21:
	ret
	.p2align 6
