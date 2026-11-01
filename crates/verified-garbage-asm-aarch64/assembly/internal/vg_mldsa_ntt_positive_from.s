// The functions of `src/internal/vg_mldsa_ntt_positive_from.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_ntt_positive_from:
	add x11, x1, #0
	adrp x1, {VG_MLDSA_NTT_EXPANDED}
	add x1, x1, {VG_MLDSA_NTT_EXPANDED}
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	movz w10, #57343, lsl #0
	movk w10, #64639, lsl #16
	dup v16.4s, w9
	dup v17.4s, w10
	movz w9, #1793, lsl #0
	movk w9, #32800, lsl #16
	dup v20.4s, w9
	add x2, x0, #0
	movz x5, #8, lsl #0
	ldr q25, [x1, #3840]
	ldr q26, [x1, #3856]
	ldr q27, [x1, #3872]
	ldr q28, [x1, #3888]
20:
	ldr q0, [x11, #0]
	ldr q1, [x11, #128]
	ldr q5, [x11, #256]
	ldr q6, [x11, #384]
	ldr q7, [x11, #512]
	ldr q21, [x11, #640]
	ldr q22, [x11, #768]
	ldr q23, [x11, #896]
	dup v18.4s, v25.s[0]
	dup v19.4s, v25.s[1]
	sqdmulh v4.4s, v7.4s, v19.4s
	sqdmulh v29.4s, v21.4s, v19.4s
	sqdmulh v30.4s, v22.4s, v19.4s
	sqdmulh v31.4s, v23.4s, v19.4s
	mul v7.4s, v7.4s, v18.4s
	mul v21.4s, v21.4s, v18.4s
	mul v22.4s, v22.4s, v18.4s
	mul v23.4s, v23.4s, v18.4s
	mls v7.4s, v4.4s, v16.4s
	mls v21.4s, v29.4s, v16.4s
	mls v22.4s, v30.4s, v16.4s
	mls v23.4s, v31.4s, v16.4s
	sub v24.4s, v0.4s, v7.4s
	add v0.4s, v0.4s, v7.4s
	sub v7.4s, v1.4s, v21.4s
	add v1.4s, v1.4s, v21.4s
	sub v21.4s, v5.4s, v22.4s
	add v5.4s, v5.4s, v22.4s
	sub v22.4s, v6.4s, v23.4s
	add v6.4s, v6.4s, v23.4s
	dup v18.4s, v25.s[2]
	dup v19.4s, v25.s[3]
	sqdmulh v4.4s, v5.4s, v19.4s
	sqdmulh v29.4s, v6.4s, v19.4s
	mul v5.4s, v5.4s, v18.4s
	mul v6.4s, v6.4s, v18.4s
	mls v5.4s, v4.4s, v16.4s
	mls v6.4s, v29.4s, v16.4s
	sub v23.4s, v0.4s, v5.4s
	add v0.4s, v0.4s, v5.4s
	sub v5.4s, v1.4s, v6.4s
	add v1.4s, v1.4s, v6.4s
	dup v18.4s, v26.s[0]
	dup v19.4s, v26.s[1]
	sqdmulh v4.4s, v21.4s, v19.4s
	sqdmulh v29.4s, v22.4s, v19.4s
	mul v21.4s, v21.4s, v18.4s
	mul v22.4s, v22.4s, v18.4s
	mls v21.4s, v4.4s, v16.4s
	mls v22.4s, v29.4s, v16.4s
	sub v6.4s, v24.4s, v21.4s
	add v24.4s, v24.4s, v21.4s
	sub v21.4s, v7.4s, v22.4s
	add v7.4s, v7.4s, v22.4s
	dup v18.4s, v26.s[2]
	dup v19.4s, v26.s[3]
	sqdmulh v4.4s, v1.4s, v19.4s
	mul v1.4s, v1.4s, v18.4s
	mls v1.4s, v4.4s, v16.4s
	sub v22.4s, v0.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	dup v18.4s, v27.s[0]
	dup v19.4s, v27.s[1]
	sqdmulh v4.4s, v5.4s, v19.4s
	mul v5.4s, v5.4s, v18.4s
	mls v5.4s, v4.4s, v16.4s
	sub v1.4s, v23.4s, v5.4s
	add v23.4s, v23.4s, v5.4s
	dup v18.4s, v27.s[2]
	dup v19.4s, v27.s[3]
	sqdmulh v4.4s, v7.4s, v19.4s
	mul v7.4s, v7.4s, v18.4s
	mls v7.4s, v4.4s, v16.4s
	sub v5.4s, v24.4s, v7.4s
	add v24.4s, v24.4s, v7.4s
	dup v18.4s, v28.s[0]
	dup v19.4s, v28.s[1]
	sqdmulh v4.4s, v21.4s, v19.4s
	mul v21.4s, v21.4s, v18.4s
	mls v21.4s, v4.4s, v16.4s
	sub v7.4s, v6.4s, v21.4s
	add v6.4s, v6.4s, v21.4s
	str q0, [x2, #0]
	str q22, [x2, #128]
	str q23, [x2, #256]
	str q1, [x2, #384]
	str q24, [x2, #512]
	str q5, [x2, #640]
	str q6, [x2, #768]
	str q7, [x2, #896]
	add x2, x2, #16
	add x11, x11, #16
	sub x5, x5, #1
	cbnz x5, 20b
	add x2, x0, #0
	add x3, x1, #0
	add x4, x1, #32
	add x5, x1, #96
	add x7, x1, #224
	add x8, x1, #352
	movz x10, #8, lsl #0
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q5, [x2, #32]
	ldr q6, [x2, #48]
	ldr q7, [x2, #64]
	ldr q21, [x2, #80]
	ldr q22, [x2, #96]
	ldr q23, [x2, #112]
	ldr q18, [x3, #0]
	ldr q19, [x3, #16]
	sqdmulh v4.4s, v7.4s, v19.4s
	sqdmulh v29.4s, v21.4s, v19.4s
	sqdmulh v30.4s, v22.4s, v19.4s
	sqdmulh v31.4s, v23.4s, v19.4s
	mul v7.4s, v7.4s, v18.4s
	mul v21.4s, v21.4s, v18.4s
	mul v22.4s, v22.4s, v18.4s
	mul v23.4s, v23.4s, v18.4s
	mls v7.4s, v4.4s, v16.4s
	mls v21.4s, v29.4s, v16.4s
	mls v22.4s, v30.4s, v16.4s
	mls v23.4s, v31.4s, v16.4s
	sub v24.4s, v0.4s, v7.4s
	add v0.4s, v0.4s, v7.4s
	sub v7.4s, v1.4s, v21.4s
	add v1.4s, v1.4s, v21.4s
	sub v21.4s, v5.4s, v22.4s
	add v5.4s, v5.4s, v22.4s
	sub v22.4s, v6.4s, v23.4s
	add v6.4s, v6.4s, v23.4s
	ldr q18, [x4, #0]
	ldr q19, [x4, #16]
	sqdmulh v4.4s, v5.4s, v19.4s
	sqdmulh v29.4s, v6.4s, v19.4s
	mul v5.4s, v5.4s, v18.4s
	mul v6.4s, v6.4s, v18.4s
	mls v5.4s, v4.4s, v16.4s
	mls v6.4s, v29.4s, v16.4s
	sub v23.4s, v0.4s, v5.4s
	add v0.4s, v0.4s, v5.4s
	sub v5.4s, v1.4s, v6.4s
	add v1.4s, v1.4s, v6.4s
	ldr q18, [x4, #32]
	ldr q19, [x4, #48]
	sqdmulh v4.4s, v21.4s, v19.4s
	sqdmulh v29.4s, v22.4s, v19.4s
	mul v21.4s, v21.4s, v18.4s
	mul v22.4s, v22.4s, v18.4s
	mls v21.4s, v4.4s, v16.4s
	mls v22.4s, v29.4s, v16.4s
	sub v6.4s, v24.4s, v21.4s
	add v24.4s, v24.4s, v21.4s
	sub v21.4s, v7.4s, v22.4s
	add v7.4s, v7.4s, v22.4s
	ldr q18, [x5, #0]
	ldr q19, [x5, #16]
	sqdmulh v4.4s, v1.4s, v19.4s
	mul v1.4s, v1.4s, v18.4s
	mls v1.4s, v4.4s, v16.4s
	sub v22.4s, v0.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	ldr q18, [x5, #32]
	ldr q19, [x5, #48]
	sqdmulh v4.4s, v5.4s, v19.4s
	mul v5.4s, v5.4s, v18.4s
	mls v5.4s, v4.4s, v16.4s
	sub v1.4s, v23.4s, v5.4s
	add v23.4s, v23.4s, v5.4s
	ldr q18, [x5, #64]
	ldr q19, [x5, #80]
	sqdmulh v4.4s, v7.4s, v19.4s
	mul v7.4s, v7.4s, v18.4s
	mls v7.4s, v4.4s, v16.4s
	sub v5.4s, v24.4s, v7.4s
	add v24.4s, v24.4s, v7.4s
	ldr q18, [x5, #96]
	ldr q19, [x5, #112]
	sqdmulh v4.4s, v21.4s, v19.4s
	mul v21.4s, v21.4s, v18.4s
	mls v21.4s, v4.4s, v16.4s
	sub v7.4s, v6.4s, v21.4s
	add v6.4s, v6.4s, v21.4s
	ldr q18, [x7, #0]
	ldr q19, [x7, #16]
	trn1 v25.2d, v0.2d, v22.2d
	trn2 v26.2d, v0.2d, v22.2d
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	trn1 v0.2d, v25.2d, v21.2d
	trn2 v22.2d, v25.2d, v21.2d
	ldr q18, [x8, #0]
	ldr q19, [x8, #16]
	uzp1 v25.4s, v0.4s, v22.4s
	uzp2 v26.4s, v0.4s, v22.4s
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	zip1 v0.4s, v25.4s, v21.4s
	zip2 v22.4s, v25.4s, v21.4s
	ldr q18, [x7, #32]
	ldr q19, [x7, #48]
	trn1 v25.2d, v23.2d, v1.2d
	trn2 v26.2d, v23.2d, v1.2d
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	trn1 v23.2d, v25.2d, v21.2d
	trn2 v1.2d, v25.2d, v21.2d
	ldr q18, [x8, #32]
	ldr q19, [x8, #48]
	uzp1 v25.4s, v23.4s, v1.4s
	uzp2 v26.4s, v23.4s, v1.4s
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	zip1 v23.4s, v25.4s, v21.4s
	zip2 v1.4s, v25.4s, v21.4s
	ldr q18, [x7, #64]
	ldr q19, [x7, #80]
	trn1 v25.2d, v24.2d, v5.2d
	trn2 v26.2d, v24.2d, v5.2d
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	trn1 v24.2d, v25.2d, v21.2d
	trn2 v5.2d, v25.2d, v21.2d
	ldr q18, [x8, #64]
	ldr q19, [x8, #80]
	uzp1 v25.4s, v24.4s, v5.4s
	uzp2 v26.4s, v24.4s, v5.4s
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	zip1 v24.4s, v25.4s, v21.4s
	zip2 v5.4s, v25.4s, v21.4s
	ldr q18, [x7, #96]
	ldr q19, [x7, #112]
	trn1 v25.2d, v6.2d, v7.2d
	trn2 v26.2d, v6.2d, v7.2d
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	trn1 v6.2d, v25.2d, v21.2d
	trn2 v7.2d, v25.2d, v21.2d
	ldr q18, [x8, #96]
	ldr q19, [x8, #112]
	uzp1 v25.4s, v6.4s, v7.4s
	uzp2 v26.4s, v6.4s, v7.4s
	sqdmulh v4.4s, v26.4s, v19.4s
	mul v26.4s, v26.4s, v18.4s
	mls v26.4s, v4.4s, v16.4s
	sub v21.4s, v25.4s, v26.4s
	add v25.4s, v25.4s, v26.4s
	zip1 v6.4s, v25.4s, v21.4s
	zip2 v7.4s, v25.4s, v21.4s
	sshr v4.4s, v0.4s, #23
	mls v0.4s, v4.4s, v16.4s
	add v0.4s, v0.4s, v16.4s
	sshr v4.4s, v22.4s, #23
	mls v22.4s, v4.4s, v16.4s
	add v22.4s, v22.4s, v16.4s
	sshr v4.4s, v23.4s, #23
	mls v23.4s, v4.4s, v16.4s
	add v23.4s, v23.4s, v16.4s
	sshr v4.4s, v1.4s, #23
	mls v1.4s, v4.4s, v16.4s
	add v1.4s, v1.4s, v16.4s
	sshr v4.4s, v24.4s, #23
	mls v24.4s, v4.4s, v16.4s
	add v24.4s, v24.4s, v16.4s
	sshr v4.4s, v5.4s, #23
	mls v5.4s, v4.4s, v16.4s
	add v5.4s, v5.4s, v16.4s
	sshr v4.4s, v6.4s, #23
	mls v6.4s, v4.4s, v16.4s
	add v6.4s, v6.4s, v16.4s
	sshr v4.4s, v7.4s, #23
	mls v7.4s, v4.4s, v16.4s
	add v7.4s, v7.4s, v16.4s
	str q0, [x2, #0]
	str q22, [x2, #16]
	str q23, [x2, #32]
	str q1, [x2, #48]
	str q24, [x2, #64]
	str q5, [x2, #80]
	str q6, [x2, #96]
	str q7, [x2, #112]
	add x2, x2, #128
	add x3, x3, #480
	add x4, x4, #480
	add x5, x5, #480
	add x7, x7, #480
	add x8, x8, #480
	sub x10, x10, #1
	cbnz x10, 21b
	ret
	.p2align 6
