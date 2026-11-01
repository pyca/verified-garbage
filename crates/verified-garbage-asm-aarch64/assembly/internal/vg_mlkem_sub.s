// The functions of `src/internal/vg_mlkem_sub.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sub:
	movz x9, #3329, lsl #0
	dup v16.4s, w9
	movz x10, #64, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	sub v2.4s, v0.4s, v1.4s
	add v3.4s, v2.4s, v16.4s
	umin v2.4s, v2.4s, v3.4s
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6
