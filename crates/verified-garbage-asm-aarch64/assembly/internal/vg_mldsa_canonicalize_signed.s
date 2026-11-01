// The functions of `src/internal/vg_mldsa_canonicalize_signed.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_canonicalize_signed:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v16.4s, w9
	movz x10, #16, lsl #0
20:
	ldr q0, [x0, #0]
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q0, [x0, #0]
	ldr q0, [x0, #16]
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q0, [x0, #16]
	ldr q0, [x0, #32]
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q0, [x0, #32]
	ldr q0, [x0, #48]
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q0, [x0, #48]
	add x0, x0, #64
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6
