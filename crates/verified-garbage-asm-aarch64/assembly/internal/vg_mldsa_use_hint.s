// The functions of `src/internal/vg_mldsa_use_hint.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_use_hint:
	add w2, w2, #0
	movz w4, #65280, lsl #0
	movk w4, #3, lsl #16
	sub x4, x2, x4
	cbz x4, 20f
	movz x5, #11275, lsl #0
	movz x6, #128, lsl #16
	movz w7, #59392, lsl #0
	movk w7, #2, lsl #16
	movz x9, #0, lsl #0
	movz x10, #44, lsl #0
	movz x8, #256, lsl #0
22:
	ldr w11, [x1, #0]
	add x12, x11, #127
	lsr x12, x12, #7
	mul x12, x12, x5
	add x12, x12, x6
	lsr x12, x12, #24
	mul x13, x12, x7
	sub x13, x13, x11
	lsr x13, x13, #63
	lsl x13, x13, #1
	sub x13, x13, #1
	ldr w14, [x0, #0]
	sub x14, x9, x14
	lsr x14, x14, #63
	mul x13, x13, x14
	add x13, x13, x12
	add x13, x13, #44
	sub x13, x13, x10
	lsr x14, x13, #63
	madd x13, x14, x10, x13
	sub x13, x13, x10
	lsr x14, x13, #63
	madd x13, x14, x10, x13
	str w13, [x3, #0]
	add x0, x0, #4
	add x1, x1, #4
	add x3, x3, #4
	sub x8, x8, #1
	cbnz x8, 22b
	b 21f
20:
	movz x5, #1025, lsl #0
	movz x6, #32, lsl #16
	movz w7, #65024, lsl #0
	movk w7, #7, lsl #16
	movz x9, #0, lsl #0
	movz x10, #16, lsl #0
	movz x8, #256, lsl #0
23:
	ldr w11, [x1, #0]
	add x12, x11, #127
	lsr x12, x12, #7
	mul x12, x12, x5
	add x12, x12, x6
	lsr x12, x12, #22
	mul x13, x12, x7
	sub x13, x13, x11
	lsr x13, x13, #63
	lsl x13, x13, #1
	sub x13, x13, #1
	ldr w14, [x0, #0]
	sub x14, x9, x14
	lsr x14, x14, #63
	mul x13, x13, x14
	add x13, x13, x12
	add x13, x13, #16
	sub x13, x13, x10
	lsr x14, x13, #63
	madd x13, x14, x10, x13
	sub x13, x13, x10
	lsr x14, x13, #63
	madd x13, x14, x10, x13
	str w13, [x3, #0]
	add x0, x0, #4
	add x1, x1, #4
	add x3, x3, #4
	sub x8, x8, #1
	cbnz x8, 23b
21:
	ret
	.p2align 6
