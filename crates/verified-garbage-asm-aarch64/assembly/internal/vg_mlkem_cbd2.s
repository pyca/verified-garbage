// The functions of `src/internal/vg_mlkem_cbd2.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_cbd2:
	movz x9, #3329, lsl #0
	dup v16.4s, w9
	movz x9, #3327, lsl #0
	dup v17.4s, w9
	movz x9, #85, lsl #0
	dup v18.16b, w9
	movz x9, #51, lsl #0
	dup v19.16b, w9
	movz x9, #34, lsl #0
	dup v20.16b, w9
	movz x9, #15, lsl #0
	dup v21.16b, w9
	movi v22.2d, #0
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
	zip1 v5.16b, v4.16b, v22.16b
	zip1 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #0]
	zip2 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #16]
	zip2 v5.16b, v4.16b, v22.16b
	zip1 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #32]
	zip2 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #48]
	zip2 v4.16b, v2.16b, v3.16b
	zip1 v5.16b, v4.16b, v22.16b
	zip1 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #64]
	zip2 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #80]
	zip2 v5.16b, v4.16b, v22.16b
	zip1 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #96]
	zip2 v6.8h, v5.8h, v22.8h
	add v6.4s, v6.4s, v17.4s
	sub v7.4s, v6.4s, v16.4s
	umin v6.4s, v6.4s, v7.4s
	str q6, [x1, #112]
	add x0, x0, #16
	add x1, x1, #128
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6
