// The functions of `src/internal/vg_ghash.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ghash:
	cbz x3, 20f
22:
	ldr x5, [x1, #0]
	rev x5, x5
	ldr x12, [x2, #0]
	rev x12, x12
	eor x5, x5, x12
	ldr x6, [x1, #8]
	rev x6, x6
	ldr x12, [x2, #8]
	rev x12, x12
	eor x6, x6, x12
	ldr x9, [x0, #0]
	rev x9, x9
	ldr x10, [x0, #8]
	rev x10, x10
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x13, #57600, lsl #48
	movz x15, #0, lsl #0
	movz x14, #16, lsl #0
23:
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	lsr x12, x5, #63
	sub x11, x15, x12
	lsl x5, x5, #1
	lsr x12, x6, #63
	orr x5, x5, x12
	lsl x6, x6, #1
	and x12, x9, x11
	eor x7, x7, x12
	and x12, x10, x11
	eor x8, x8, x12
	lsl x12, x10, #63
	lsr x12, x12, #63
	sub x11, x15, x12
	lsr x10, x10, #1
	lsl x12, x9, #63
	orr x10, x10, x12
	lsr x9, x9, #1
	and x11, x11, x13
	eor x9, x9, x11
	sub x14, x14, #1
	cbnz x14, 23b
	rev x7, x7
	str x7, [x1, #0]
	rev x8, x8
	str x8, [x1, #8]
	add x2, x2, #16
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	ret
	.p2align 6
