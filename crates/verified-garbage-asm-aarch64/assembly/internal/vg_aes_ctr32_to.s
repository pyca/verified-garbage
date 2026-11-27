// The functions of `src/internal/vg_aes_ctr32_to.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_to:
	cbz x4, 20f
	add x8, x6, #0
	add x9, x0, #0
	add x10, x1, #0
22:
	ldr q0, [x2, #0]
	ldr w6, [x2, #12]
	rev w6, w6
	add w6, w6, #1
	rev w6, w6
	str w6, [x2, #12]
	adrp x6, {VG_AES_VPERM}
	add x6, x6, {VG_AES_VPERM}
	ldr q16, [x6, #0]
	ldr q17, [x6, #16]
	ldr q18, [x6, #32]
	ldr q19, [x6, #48]
	ldr q20, [x6, #64]
	ldr q21, [x6, #80]
	ldr q22, [x6, #96]
	ldr q23, [x6, #112]
	ldr q24, [x6, #128]
	ldr q25, [x6, #144]
	ldr q26, [x6, #160]
	ldr q27, [x6, #176]
	ldr q28, [x6, #192]
	ldr q29, [x6, #208]
	ldr q30, [x6, #224]
	ldr q31, [x6, #240]
	ldr q5, [x0, #0]
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v1.16b, {v27.16b}, v1.16b
	tbl v0.16b, {v28.16b}, v0.16b
	eor v0.16b, v0.16b, v1.16b
	and v6.16b, v5.16b, v16.16b
	ushr v5.16b, v5.16b, #4
	tbl v6.16b, {v27.16b}, v6.16b
	tbl v5.16b, {v28.16b}, v5.16b
	eor v5.16b, v5.16b, v6.16b
	eor v0.16b, v0.16b, v5.16b
	sub x1, x1, #1
23:
	add x0, x0, #16
	ldr q5, [x0, #0]
	and v6.16b, v5.16b, v16.16b
	ushr v5.16b, v5.16b, #4
	tbl v6.16b, {v27.16b}, v6.16b
	tbl v5.16b, {v28.16b}, v5.16b
	eor v5.16b, v5.16b, v6.16b
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v2.16b, {v18.16b}, v1.16b
	eor v1.16b, v1.16b, v0.16b
	tbl v3.16b, {v17.16b}, v0.16b
	tbl v4.16b, {v17.16b}, v1.16b
	eor v3.16b, v3.16b, v2.16b
	eor v4.16b, v4.16b, v2.16b
	tbl v2.16b, {v17.16b}, v3.16b
	tbl v3.16b, {v17.16b}, v4.16b
	eor v2.16b, v2.16b, v1.16b
	eor v3.16b, v3.16b, v0.16b
	tbl v0.16b, {v19.16b}, v2.16b
	tbl v1.16b, {v20.16b}, v3.16b
	tbl v2.16b, {v21.16b}, v2.16b
	tbl v3.16b, {v22.16b}, v3.16b
	eor v0.16b, v0.16b, v1.16b
	eor v2.16b, v2.16b, v3.16b
	tbl v1.16b, {v2.16b}, v23.16b
	tbl v3.16b, {v0.16b}, v24.16b
	tbl v0.16b, {v0.16b}, v25.16b
	eor v1.16b, v1.16b, v3.16b
	eor v0.16b, v0.16b, v5.16b
	tbl v3.16b, {v1.16b}, v26.16b
	eor v0.16b, v0.16b, v1.16b
	eor v0.16b, v0.16b, v3.16b
	sub x1, x1, #1
	cbnz x1, 23b
	ldr q5, [x0, #16]
	and v1.16b, v0.16b, v16.16b
	ushr v0.16b, v0.16b, #4
	tbl v2.16b, {v18.16b}, v1.16b
	eor v1.16b, v1.16b, v0.16b
	tbl v3.16b, {v17.16b}, v0.16b
	tbl v4.16b, {v17.16b}, v1.16b
	eor v3.16b, v3.16b, v2.16b
	eor v4.16b, v4.16b, v2.16b
	tbl v2.16b, {v17.16b}, v3.16b
	tbl v3.16b, {v17.16b}, v4.16b
	eor v2.16b, v2.16b, v1.16b
	eor v3.16b, v3.16b, v0.16b
	tbl v0.16b, {v29.16b}, v2.16b
	tbl v1.16b, {v30.16b}, v3.16b
	eor v0.16b, v0.16b, v1.16b
	tbl v0.16b, {v0.16b}, v23.16b
	eor v5.16b, v5.16b, v31.16b
	eor v0.16b, v0.16b, v5.16b
	ldr q1, [x3, #0]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x8, #0]
	add x3, x3, #16
	add x8, x8, #16
	sub x4, x4, #1
	add x0, x9, #0
	add x1, x10, #0
	cbnz x4, 22b
	b 21f
20:
21:
	ret
	.p2align 6
