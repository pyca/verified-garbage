// The functions of `src/internal/vg_mldsa_hint_bit_unpack.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_unpack:
	lsr x12, x4, #8
	sub x2, x1, x12
	movz x15, #0, lsl #0
	add x9, x0, #0
	add x10, x3, #0
	add x8, x4, #0
20:
	str w15, [x10, #0]
	add x10, x10, #4
	sub x8, x8, #1
	cbnz x8, 20b
	movz x5, #0, lsl #0
	movz x15, #1, lsl #0
	add x6, x9, x2
21:
	ldrb w7, [x6, #0]
	sub x10, x7, x5
	sub x11, x2, x7
	orr x10, x10, x11
	lsr x10, x10, #63
	cbnz x10, 22f
	movz x11, #0, lsl #0
	sub x10, x5, x7
	lsr x10, x10, #63
	cbnz x10, 24f
	b 25f
24:
26:
	add x13, x9, x5
	ldrb w10, [x13, #0]
	sub x14, x10, x11
	lsr x14, x14, #63
	cbnz x14, 27f
	lsl x14, x10, #2
	add x14, x3, x14
	str w15, [x14, #0]
	add x5, x5, #1
	add x11, x10, #1
	b 28f
27:
	movz x5, #256, lsl #0
28:
	sub x10, x5, x7
	lsr x10, x10, #63
	cbnz x10, 26b
25:
	b 23f
22:
	movz x5, #256, lsl #0
23:
	add x6, x6, #1
	add x3, x3, #1024
	sub x12, x12, #1
	cbnz x12, 21b
	sub x10, x5, x2
	lsr x10, x10, #63
	cbnz x10, 29f
	b 210f
29:
211:
	add x13, x9, x5
	ldrb w10, [x13, #0]
	cbnz x10, 212f
	add x5, x5, #1
	b 213f
212:
	movz x5, #256, lsl #0
213:
	sub x10, x5, x2
	lsr x10, x10, #63
	cbnz x10, 211b
210:
	sub x10, x2, x5
	lsr x10, x10, #63
	eor x0, x10, x15
	ret
	.p2align 6
