// The functions of `src/zeroize.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	movz x2, #0, lsl #0
	lsr x3, x1, #7
	movz x4, #127, lsl #0
	and x1, x1, x4
	dup v0.2d, x2
	cbz x3, 20f
22:
	str q0, [x0, #0]
	str q0, [x0, #16]
	str q0, [x0, #32]
	str q0, [x0, #48]
	str q0, [x0, #64]
	str q0, [x0, #80]
	str q0, [x0, #96]
	str q0, [x0, #112]
	add x0, x0, #128
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	lsr x3, x1, #3
	movz x4, #7, lsl #0
	and x1, x1, x4
	cbz x3, 23f
25:
	str x2, [x0, #0]
	add x0, x0, #8
	sub x3, x3, #1
	cbnz x3, 25b
	b 24f
23:
24:
	add x3, x1, #0
	cbz x3, 26f
28:
	strb w2, [x0, #0]
	add x0, x0, #1
	sub x3, x3, #1
	cbnz x3, 28b
	b 27f
26:
27:
	ret
	.p2align 6
