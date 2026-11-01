// The functions of `src/internal/vg_mldsa_multiply_inverse_raw.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_inverse_raw:
	add x13, x1, #0
	add x14, x2, #0
	adrp x1, {VG_MLDSA_INV_FOLDED}
	add x1, x1, {VG_MLDSA_INV_FOLDED}
	movz w10, #57343, lsl #0
	movk w10, #64639, lsl #16
	dup v30.4s, w10
	movz w9, #57345, lsl #0
	movk w9, #127, lsl #16
	dup v31.4s, w9
	add x3, x1, #0
	add x4, x1, #512
	add x5, x1, #768
	add x6, x1, #896
	add x7, x1, #960
	movz x11, #8, lsl #0
20:
	ldr q16, [x13, #0]
	ldr q17, [x14, #0]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v0.4s, v18.4s, v19.4s
	sub v0.4s, v0.4s, v31.4s
	ldr q16, [x13, #16]
	ldr q17, [x14, #16]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v1.4s, v18.4s, v19.4s
	sub v1.4s, v1.4s, v31.4s
	ldr q16, [x13, #32]
	ldr q17, [x14, #32]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v2.4s, v18.4s, v19.4s
	sub v2.4s, v2.4s, v31.4s
	ldr q16, [x13, #48]
	ldr q17, [x14, #48]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v3.4s, v18.4s, v19.4s
	sub v3.4s, v3.4s, v31.4s
	ldr q16, [x13, #64]
	ldr q17, [x14, #64]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v4.4s, v18.4s, v19.4s
	sub v4.4s, v4.4s, v31.4s
	ldr q16, [x13, #80]
	ldr q17, [x14, #80]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v5.4s, v18.4s, v19.4s
	sub v5.4s, v5.4s, v31.4s
	ldr q16, [x13, #96]
	ldr q17, [x14, #96]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v6.4s, v18.4s, v19.4s
	sub v6.4s, v6.4s, v31.4s
	ldr q16, [x13, #112]
	ldr q17, [x14, #112]
	umull v18.2d, v16.2s, v17.2s
	umull2 v19.2d, v16.4s, v17.4s
	uzp1 v20.4s, v18.4s, v19.4s
	mul v20.4s, v20.4s, v30.4s
	umlal v18.2d, v20.2s, v31.2s
	umlal2 v19.2d, v20.4s, v31.4s
	uzp2 v7.4s, v18.4s, v19.4s
	sub v7.4s, v7.4s, v31.4s
	ldr q20, [x1, #0]
	ldr q21, [x1, #16]
	uzp1 v16.4s, v0.4s, v1.4s
	uzp2 v17.4s, v0.4s, v1.4s
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	zip1 v0.4s, v16.4s, v18.4s
	zip2 v1.4s, v16.4s, v18.4s
	ldr q20, [x1, #32]
	ldr q21, [x1, #48]
	uzp1 v16.4s, v2.4s, v3.4s
	uzp2 v17.4s, v2.4s, v3.4s
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	zip1 v2.4s, v16.4s, v18.4s
	zip2 v3.4s, v16.4s, v18.4s
	ldr q20, [x1, #64]
	ldr q21, [x1, #80]
	uzp1 v16.4s, v4.4s, v5.4s
	uzp2 v17.4s, v4.4s, v5.4s
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	zip1 v4.4s, v16.4s, v18.4s
	zip2 v5.4s, v16.4s, v18.4s
	ldr q20, [x1, #96]
	ldr q21, [x1, #112]
	uzp1 v16.4s, v6.4s, v7.4s
	uzp2 v17.4s, v6.4s, v7.4s
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	zip1 v6.4s, v16.4s, v18.4s
	zip2 v7.4s, v16.4s, v18.4s
	ldr q20, [x1, #128]
	ldr q21, [x1, #144]
	trn1 v16.2d, v0.2d, v1.2d
	trn2 v17.2d, v0.2d, v1.2d
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	trn1 v0.2d, v16.2d, v18.2d
	trn2 v1.2d, v16.2d, v18.2d
	ldr q20, [x1, #160]
	ldr q21, [x1, #176]
	trn1 v16.2d, v2.2d, v3.2d
	trn2 v17.2d, v2.2d, v3.2d
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	trn1 v2.2d, v16.2d, v18.2d
	trn2 v3.2d, v16.2d, v18.2d
	ldr q20, [x1, #192]
	ldr q21, [x1, #208]
	trn1 v16.2d, v4.2d, v5.2d
	trn2 v17.2d, v4.2d, v5.2d
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	trn1 v4.2d, v16.2d, v18.2d
	trn2 v5.2d, v16.2d, v18.2d
	ldr q20, [x1, #224]
	ldr q21, [x1, #240]
	trn1 v16.2d, v6.2d, v7.2d
	trn2 v17.2d, v6.2d, v7.2d
	sub v18.4s, v16.4s, v17.4s
	add v16.4s, v16.4s, v17.4s
	sqdmulh v19.4s, v18.4s, v21.4s
	mul v18.4s, v18.4s, v20.4s
	mls v18.4s, v19.4s, v31.4s
	trn1 v6.2d, v16.2d, v18.2d
	trn2 v7.2d, v16.2d, v18.2d
	ldr q20, [x1, #256]
	ldr q21, [x1, #272]
	sub v24.4s, v0.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sqdmulh v16.4s, v24.4s, v21.4s
	mul v24.4s, v24.4s, v20.4s
	mls v24.4s, v16.4s, v31.4s
	ldr q20, [x1, #288]
	ldr q21, [x1, #304]
	sub v1.4s, v2.4s, v3.4s
	add v2.4s, v2.4s, v3.4s
	sqdmulh v16.4s, v1.4s, v21.4s
	mul v1.4s, v1.4s, v20.4s
	mls v1.4s, v16.4s, v31.4s
	ldr q20, [x1, #320]
	ldr q21, [x1, #336]
	sub v3.4s, v4.4s, v5.4s
	add v4.4s, v4.4s, v5.4s
	sqdmulh v16.4s, v3.4s, v21.4s
	mul v3.4s, v3.4s, v20.4s
	mls v3.4s, v16.4s, v31.4s
	ldr q20, [x1, #352]
	ldr q21, [x1, #368]
	sub v5.4s, v6.4s, v7.4s
	add v6.4s, v6.4s, v7.4s
	sqdmulh v16.4s, v5.4s, v21.4s
	mul v5.4s, v5.4s, v20.4s
	mls v5.4s, v16.4s, v31.4s
	ldr q20, [x1, #384]
	ldr q21, [x1, #400]
	sub v7.4s, v0.4s, v2.4s
	add v0.4s, v0.4s, v2.4s
	sub v25.4s, v24.4s, v1.4s
	add v24.4s, v24.4s, v1.4s
	sqdmulh v16.4s, v7.4s, v21.4s
	sqdmulh v17.4s, v25.4s, v21.4s
	mul v7.4s, v7.4s, v20.4s
	mul v25.4s, v25.4s, v20.4s
	mls v7.4s, v16.4s, v31.4s
	mls v25.4s, v17.4s, v31.4s
	ldr q20, [x1, #416]
	ldr q21, [x1, #432]
	sub v2.4s, v4.4s, v6.4s
	add v4.4s, v4.4s, v6.4s
	sub v1.4s, v3.4s, v5.4s
	add v3.4s, v3.4s, v5.4s
	sqdmulh v16.4s, v2.4s, v21.4s
	sqdmulh v17.4s, v1.4s, v21.4s
	mul v2.4s, v2.4s, v20.4s
	mul v1.4s, v1.4s, v20.4s
	mls v2.4s, v16.4s, v31.4s
	mls v1.4s, v17.4s, v31.4s
	ldr q20, [x1, #448]
	ldr q21, [x1, #464]
	sub v6.4s, v0.4s, v4.4s
	add v0.4s, v0.4s, v4.4s
	sub v5.4s, v24.4s, v3.4s
	add v24.4s, v24.4s, v3.4s
	sub v26.4s, v7.4s, v2.4s
	add v7.4s, v7.4s, v2.4s
	sub v27.4s, v25.4s, v1.4s
	add v25.4s, v25.4s, v1.4s
	sqdmulh v16.4s, v6.4s, v21.4s
	sqdmulh v17.4s, v5.4s, v21.4s
	sqdmulh v18.4s, v26.4s, v21.4s
	sqdmulh v19.4s, v27.4s, v21.4s
	mul v6.4s, v6.4s, v20.4s
	mul v5.4s, v5.4s, v20.4s
	mul v26.4s, v26.4s, v20.4s
	mul v27.4s, v27.4s, v20.4s
	mls v6.4s, v16.4s, v31.4s
	mls v5.4s, v17.4s, v31.4s
	mls v26.4s, v18.4s, v31.4s
	mls v27.4s, v19.4s, v31.4s
	str q0, [x0, #0]
	str q24, [x0, #16]
	str q7, [x0, #32]
	str q25, [x0, #48]
	str q6, [x0, #64]
	str q5, [x0, #80]
	str q26, [x0, #96]
	str q27, [x0, #112]
	add x13, x13, #128
	add x14, x14, #128
	add x0, x0, #128
	add x1, x1, #480
	sub x11, x11, #1
	cbnz x11, 20b
	sub x0, x0, #1024
	add x2, x0, #0
	movz x12, #8, lsl #0
	ldr q22, [x1, #0]
	ldr q23, [x1, #16]
	ldr q28, [x1, #32]
	ldr q29, [x1, #48]
	movz w9, #16382, lsl #0
	movk w9, #0, lsl #16
	dup v30.4s, w9
	movz w9, #3587, lsl #0
	movk w9, #64, lsl #16
	mov v30.s[1], w9
	movz w9, #24764, lsl #0
	movk w9, #123, lsl #16
	mov v30.s[2], w9
	movz w9, #39663, lsl #0
	movk w9, #31615, lsl #16
	mov v30.s[3], w9
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #128]
	ldr q2, [x2, #256]
	ldr q3, [x2, #384]
	ldr q4, [x2, #512]
	ldr q5, [x2, #640]
	ldr q6, [x2, #768]
	ldr q7, [x2, #896]
	dup v20.4s, v22.s[0]
	dup v21.4s, v28.s[0]
	sub v24.4s, v0.4s, v1.4s
	add v0.4s, v0.4s, v1.4s
	sqdmulh v16.4s, v24.4s, v21.4s
	mul v24.4s, v24.4s, v20.4s
	mls v24.4s, v16.4s, v31.4s
	dup v20.4s, v22.s[1]
	dup v21.4s, v28.s[1]
	sub v1.4s, v2.4s, v3.4s
	add v2.4s, v2.4s, v3.4s
	sqdmulh v16.4s, v1.4s, v21.4s
	mul v1.4s, v1.4s, v20.4s
	mls v1.4s, v16.4s, v31.4s
	dup v20.4s, v22.s[2]
	dup v21.4s, v28.s[2]
	sub v3.4s, v4.4s, v5.4s
	add v4.4s, v4.4s, v5.4s
	sqdmulh v16.4s, v3.4s, v21.4s
	mul v3.4s, v3.4s, v20.4s
	mls v3.4s, v16.4s, v31.4s
	dup v20.4s, v22.s[3]
	dup v21.4s, v28.s[3]
	sub v5.4s, v6.4s, v7.4s
	add v6.4s, v6.4s, v7.4s
	sqdmulh v16.4s, v5.4s, v21.4s
	mul v5.4s, v5.4s, v20.4s
	mls v5.4s, v16.4s, v31.4s
	dup v20.4s, v23.s[0]
	dup v21.4s, v29.s[0]
	sub v7.4s, v0.4s, v2.4s
	add v0.4s, v0.4s, v2.4s
	sub v25.4s, v24.4s, v1.4s
	add v24.4s, v24.4s, v1.4s
	sqdmulh v16.4s, v7.4s, v21.4s
	sqdmulh v17.4s, v25.4s, v21.4s
	mul v7.4s, v7.4s, v20.4s
	mul v25.4s, v25.4s, v20.4s
	mls v7.4s, v16.4s, v31.4s
	mls v25.4s, v17.4s, v31.4s
	dup v20.4s, v23.s[1]
	dup v21.4s, v29.s[1]
	sub v2.4s, v4.4s, v6.4s
	add v4.4s, v4.4s, v6.4s
	sub v1.4s, v3.4s, v5.4s
	add v3.4s, v3.4s, v5.4s
	sqdmulh v16.4s, v2.4s, v21.4s
	sqdmulh v17.4s, v1.4s, v21.4s
	mul v2.4s, v2.4s, v20.4s
	mul v1.4s, v1.4s, v20.4s
	mls v2.4s, v16.4s, v31.4s
	mls v1.4s, v17.4s, v31.4s
	dup v20.4s, v30.s[2]
	dup v21.4s, v30.s[3]
	sub v6.4s, v0.4s, v4.4s
	add v0.4s, v0.4s, v4.4s
	sub v5.4s, v24.4s, v3.4s
	add v24.4s, v24.4s, v3.4s
	sub v26.4s, v7.4s, v2.4s
	add v7.4s, v7.4s, v2.4s
	sub v27.4s, v25.4s, v1.4s
	add v25.4s, v25.4s, v1.4s
	sqdmulh v16.4s, v6.4s, v21.4s
	sqdmulh v17.4s, v5.4s, v21.4s
	sqdmulh v18.4s, v26.4s, v21.4s
	sqdmulh v19.4s, v27.4s, v21.4s
	mul v6.4s, v6.4s, v20.4s
	mul v5.4s, v5.4s, v20.4s
	mul v26.4s, v26.4s, v20.4s
	mul v27.4s, v27.4s, v20.4s
	mls v6.4s, v16.4s, v31.4s
	mls v5.4s, v17.4s, v31.4s
	mls v26.4s, v18.4s, v31.4s
	mls v27.4s, v19.4s, v31.4s
	dup v20.4s, v30.s[0]
	dup v21.4s, v30.s[1]
	sqdmulh v16.4s, v0.4s, v21.4s
	sqdmulh v17.4s, v24.4s, v21.4s
	sqdmulh v18.4s, v7.4s, v21.4s
	sqdmulh v19.4s, v25.4s, v21.4s
	mul v0.4s, v0.4s, v20.4s
	mul v24.4s, v24.4s, v20.4s
	mul v7.4s, v7.4s, v20.4s
	mul v25.4s, v25.4s, v20.4s
	mls v0.4s, v16.4s, v31.4s
	mls v24.4s, v17.4s, v31.4s
	mls v7.4s, v18.4s, v31.4s
	mls v25.4s, v19.4s, v31.4s
	str q0, [x2, #0]
	str q24, [x2, #128]
	str q7, [x2, #256]
	str q25, [x2, #384]
	str q6, [x2, #512]
	str q5, [x2, #640]
	str q26, [x2, #768]
	str q27, [x2, #896]
	add x2, x2, #16
	sub x12, x12, #1
	cbnz x12, 21b
	ret
	.p2align 6
