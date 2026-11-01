// The functions of `src/ct.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	movz x4, #0, lsl #0
	sub x9, x1, x3
	cbz x9, 20f
	movz w0, #0, lsl #0
	b 21f
20:
	movz x8, #0, lsl #0
	cbz x1, 22f
24:
	add x5, x0, x8
	ldrb w6, [x5, #0]
	add x5, x2, x8
	ldrb w7, [x5, #0]
	eor x6, x6, x7
	orr x4, x4, x6
	add x8, x8, #1
	sub x9, x8, x1
	cbnz x9, 24b
	b 23f
22:
23:
	sub x4, x4, #1
	lsr x0, x4, #63
21:
	ret
	.p2align 6
