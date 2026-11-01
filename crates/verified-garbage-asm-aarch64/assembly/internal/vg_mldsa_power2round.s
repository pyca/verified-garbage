// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v16.4s, w9
	movz w9, #4095, lsl #0
	movk w9, #0, lsl #16
	dup v17.4s, w9
	movz x10, #16, lsl #0
20:
	ldr q0, [x0, #0]
	add v1.4s, v0.4s, v17.4s
	ushr v1.4s, v1.4s, #13
	shl v2.4s, v1.4s, #13
	sub v0.4s, v0.4s, v2.4s
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q1, [x1, #0]
	str q0, [x2, #0]
	ldr q0, [x0, #16]
	add v1.4s, v0.4s, v17.4s
	ushr v1.4s, v1.4s, #13
	shl v2.4s, v1.4s, #13
	sub v0.4s, v0.4s, v2.4s
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q1, [x1, #16]
	str q0, [x2, #16]
	ldr q0, [x0, #32]
	add v1.4s, v0.4s, v17.4s
	ushr v1.4s, v1.4s, #13
	shl v2.4s, v1.4s, #13
	sub v0.4s, v0.4s, v2.4s
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q1, [x1, #32]
	str q0, [x2, #32]
	ldr q0, [x0, #48]
	add v1.4s, v0.4s, v17.4s
	ushr v1.4s, v1.4s, #13
	shl v2.4s, v1.4s, #13
	sub v0.4s, v0.4s, v2.4s
	sshr v7.4s, v0.4s, #31
	and v7.16b, v7.16b, v16.16b
	add v0.4s, v0.4s, v7.4s
	str q1, [x1, #48]
	str q0, [x2, #48]
	add x0, x0, #64
	add x1, x1, #64
	add x2, x2, #64
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6
