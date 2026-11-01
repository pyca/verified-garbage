// The functions of `src/internal/vg_mlkem16_cbd2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem16_cbd2:
	movz x9, #255, lsl #0
	movk x9, #256, lsl #16
	movk x9, #2, lsl #32
	dup v16.2d, x9
	movz x9, #3340, lsl #0
	dup v17.2d, x9
	movz x9, #85, lsl #0
	dup v18.16b, w9
	movz x9, #51, lsl #0
	dup v19.16b, w9
	movz x9, #34, lsl #0
	dup v20.16b, w9
	movz x9, #15, lsl #0
	dup v21.16b, w9
	movz x10, #8, lsl #0
20:
	ldr q0, [x0, #0]
	ushr v1.16b, v0.16b, #1
	and v0.16b, v0.16b, v18.16b
	and v1.16b, v1.16b, v18.16b
	add v0.16b, v0.16b, v1.16b
	ushr v1.16b, v0.16b, #2
	and v0.16b, v0.16b, v19.16b
	and v1.16b, v1.16b, v19.16b
	add v0.16b, v0.16b, v20.16b
	sub v0.16b, v0.16b, v1.16b
	and v2.16b, v0.16b, v21.16b
	ushr v3.16b, v0.16b, #4
	zip1 v4.16b, v2.16b, v3.16b
	tbl v5.16b, {v16.16b}, v4.16b
	tbl v6.16b, {v17.16b}, v4.16b
	zip1 v7.16b, v5.16b, v6.16b
	zip2 v5.16b, v5.16b, v6.16b
	str q7, [x1, #0]
	str q5, [x1, #16]
	zip2 v4.16b, v2.16b, v3.16b
	tbl v5.16b, {v16.16b}, v4.16b
	tbl v6.16b, {v17.16b}, v4.16b
	zip1 v7.16b, v5.16b, v6.16b
	zip2 v5.16b, v5.16b, v6.16b
	str q7, [x1, #32]
	str q5, [x1, #48]
	add x0, x0, #16
	add x1, x1, #64
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6
