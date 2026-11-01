// The functions of `src/internal/vg_mldsa_signed_add_norm.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_signed_add_norm:
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v16.4s, w9
	movz w9, #0, lsl #0
	movk w9, #64, lsl #16
	dup v25.4s, w9
	dup v24.4s, w2
	movi v31.2d, #0
	movz w9, #1, lsl #0
	movk w9, #0, lsl #16
	dup v27.4s, w9
	sub v27.4s, v24.4s, v27.4s
	add v24.4s, v24.4s, v27.4s
	movz x10, #16, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v0.4s, v0.4s, v1.4s
	add v6.4s, v0.4s, v25.4s
	sshr v6.4s, v6.4s, #23
	mls v0.4s, v6.4s, v16.4s
	str q0, [x0, #0]
	add v2.4s, v0.4s, v27.4s
	umin v2.4s, v2.4s, v24.4s
	cmeq v2.4s, v2.4s, v24.4s
	orr v31.16b, v31.16b, v2.16b
	ldr q0, [x0, #16]
	ldr q1, [x1, #16]
	add v0.4s, v0.4s, v1.4s
	add v6.4s, v0.4s, v25.4s
	sshr v6.4s, v6.4s, #23
	mls v0.4s, v6.4s, v16.4s
	str q0, [x0, #16]
	add v2.4s, v0.4s, v27.4s
	umin v2.4s, v2.4s, v24.4s
	cmeq v2.4s, v2.4s, v24.4s
	orr v31.16b, v31.16b, v2.16b
	ldr q0, [x0, #32]
	ldr q1, [x1, #32]
	add v0.4s, v0.4s, v1.4s
	add v6.4s, v0.4s, v25.4s
	sshr v6.4s, v6.4s, #23
	mls v0.4s, v6.4s, v16.4s
	str q0, [x0, #32]
	add v2.4s, v0.4s, v27.4s
	umin v2.4s, v2.4s, v24.4s
	cmeq v2.4s, v2.4s, v24.4s
	orr v31.16b, v31.16b, v2.16b
	ldr q0, [x0, #48]
	ldr q1, [x1, #48]
	add v0.4s, v0.4s, v1.4s
	add v6.4s, v0.4s, v25.4s
	sshr v6.4s, v6.4s, #23
	mls v0.4s, v6.4s, v16.4s
	str q0, [x0, #48]
	add v2.4s, v0.4s, v27.4s
	umin v2.4s, v2.4s, v24.4s
	cmeq v2.4s, v2.4s, v24.4s
	orr v31.16b, v31.16b, v2.16b
	add x0, x0, #64
	add x1, x1, #64
	sub x10, x10, #1
	cbnz x10, 20b
	umov w0, v31.s[0]
	umov w9, v31.s[1]
	orr w0, w0, w9
	umov w9, v31.s[2]
	orr w0, w0, w9
	umov w9, v31.s[3]
	orr w0, w0, w9
	add w0, w0, #1
	ret
	.p2align 6
