// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	lsr x12, x1, #8
	sub x2, x4, x12
	movz x15, #0, lsl #0
	add x9, x3, #0
	add x10, x4, #0
20:
	strb w15, [x9, #0]
	add x9, x9, #1
	sub x10, x10, #1
	cbnz x10, 20b
	movz x5, #0, lsl #0
	add x6, x3, x2
21:
	movz x7, #0, lsl #0
	movz x8, #256, lsl #0
22:
	ldr w9, [x0, #0]
	cbnz x9, 23f
	b 24f
23:
	add x10, x3, x5
	strb w7, [x10, #0]
	add x5, x5, #1
24:
	add x0, x0, #4
	add x7, x7, #1
	sub x8, x8, #1
	cbnz x8, 22b
	strb w5, [x6, #0]
	add x6, x6, #1
	sub x12, x12, #1
	cbnz x12, 21b
	ret
	.p2align 6
