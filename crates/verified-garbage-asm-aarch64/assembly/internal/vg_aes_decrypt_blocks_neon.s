// The functions of `src/internal/vg_aes_decrypt_blocks_neon.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_decrypt_blocks_neon:
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	cbz x4, 20f
	movz w6, #1, lsl #0
	dup v16.16b, w6
	movz w6, #2, lsl #0
	dup v17.16b, w6
	movz w6, #4, lsl #0
	dup v18.16b, w6
	movz w6, #8, lsl #0
	dup v19.16b, w6
	movz w6, #16, lsl #0
	dup v20.16b, w6
	movz w6, #32, lsl #0
	dup v21.16b, w6
	movz w6, #64, lsl #0
	dup v22.16b, w6
	movz w6, #128, lsl #0
	dup v23.16b, w6
	add x7, x5, #128
	add x8, x1, #1
22:
	ldr q0, [x0, #0]
	and v1.16b, v0.16b, v16.16b
	cmeq v1.16b, v1.16b, v16.16b
	str q1, [x7, #0]
	and v1.16b, v0.16b, v17.16b
	cmeq v1.16b, v1.16b, v17.16b
	str q1, [x7, #16]
	and v1.16b, v0.16b, v18.16b
	cmeq v1.16b, v1.16b, v18.16b
	str q1, [x7, #32]
	and v1.16b, v0.16b, v19.16b
	cmeq v1.16b, v1.16b, v19.16b
	str q1, [x7, #48]
	and v1.16b, v0.16b, v20.16b
	cmeq v1.16b, v1.16b, v20.16b
	str q1, [x7, #64]
	and v1.16b, v0.16b, v21.16b
	cmeq v1.16b, v1.16b, v21.16b
	str q1, [x7, #80]
	and v1.16b, v0.16b, v22.16b
	cmeq v1.16b, v1.16b, v22.16b
	str q1, [x7, #96]
	and v1.16b, v0.16b, v23.16b
	cmeq v1.16b, v1.16b, v23.16b
	str q1, [x7, #112]
	add x0, x0, #16
	add x7, x7, #128
	sub x8, x8, #1
	cbnz x8, 22b
23:
	ldr q0, [x3, #0]
	sub x6, x4, #1
	cbnz x6, 24f
	b 25f
24:
	ldr q1, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 26f
	b 27f
26:
	ldr q2, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 28f
	b 29f
28:
	ldr q3, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 210f
	b 211f
210:
	ldr q4, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 212f
	b 213f
212:
	ldr q5, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 214f
	b 215f
214:
	ldr q6, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 216f
	b 217f
216:
	ldr q7, [x3, #112]
217:
215:
213:
211:
29:
27:
25:
	movz x6, #21845, lsl #0
	movk x6, #21845, lsl #16
	movk x6, #21845, lsl #32
	movk x6, #21845, lsl #48
	dup v29.2d, x6
	movz x6, #13107, lsl #0
	movk x6, #13107, lsl #16
	movk x6, #13107, lsl #32
	movk x6, #13107, lsl #48
	dup v30.2d, x6
	movz x6, #3855, lsl #0
	movk x6, #3855, lsl #16
	movk x6, #3855, lsl #32
	movk x6, #3855, lsl #48
	dup v31.2d, x6
	ushr v24.2d, v0.2d, #1
	eor v24.16b, v24.16b, v1.16b
	and v24.16b, v24.16b, v29.16b
	eor v1.16b, v1.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v2.2d, #1
	eor v24.16b, v24.16b, v3.16b
	and v24.16b, v24.16b, v29.16b
	eor v3.16b, v3.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v2.16b, v2.16b, v24.16b
	ushr v24.2d, v4.2d, #1
	eor v24.16b, v24.16b, v5.16b
	and v24.16b, v24.16b, v29.16b
	eor v5.16b, v5.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v4.16b, v4.16b, v24.16b
	ushr v24.2d, v6.2d, #1
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v29.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v6.16b, v6.16b, v24.16b
	ushr v24.2d, v0.2d, #2
	eor v24.16b, v24.16b, v2.16b
	and v24.16b, v24.16b, v30.16b
	eor v2.16b, v2.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v1.2d, #2
	eor v24.16b, v24.16b, v3.16b
	and v24.16b, v24.16b, v30.16b
	eor v3.16b, v3.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v1.16b, v1.16b, v24.16b
	ushr v24.2d, v4.2d, #2
	eor v24.16b, v24.16b, v6.16b
	and v24.16b, v24.16b, v30.16b
	eor v6.16b, v6.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v4.16b, v4.16b, v24.16b
	ushr v24.2d, v5.2d, #2
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v30.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v5.16b, v5.16b, v24.16b
	ushr v24.2d, v0.2d, #4
	eor v24.16b, v24.16b, v4.16b
	and v24.16b, v24.16b, v31.16b
	eor v4.16b, v4.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v0.16b, v0.16b, v24.16b
	ushr v24.2d, v1.2d, #4
	eor v24.16b, v24.16b, v5.16b
	and v24.16b, v24.16b, v31.16b
	eor v5.16b, v5.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v1.16b, v1.16b, v24.16b
	ushr v24.2d, v2.2d, #4
	eor v24.16b, v24.16b, v6.16b
	and v24.16b, v24.16b, v31.16b
	eor v6.16b, v6.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v2.16b, v2.16b, v24.16b
	ushr v24.2d, v3.2d, #4
	eor v24.16b, v24.16b, v7.16b
	and v24.16b, v24.16b, v31.16b
	eor v7.16b, v7.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v3.16b, v3.16b, v24.16b
	lsl x8, x1, #7
	add x8, x8, x5
	add x8, x8, #128
	sub x9, x1, #1
	ldr q24, [x8, #0]
	eor v0.16b, v0.16b, v24.16b
	ldr q24, [x8, #16]
	eor v1.16b, v1.16b, v24.16b
	ldr q24, [x8, #32]
	eor v2.16b, v2.16b, v24.16b
	ldr q24, [x8, #48]
	eor v3.16b, v3.16b, v24.16b
	ldr q24, [x8, #64]
	eor v4.16b, v4.16b, v24.16b
	ldr q24, [x8, #80]
	eor v5.16b, v5.16b, v24.16b
	ldr q24, [x8, #96]
	eor v6.16b, v6.16b, v24.16b
	ldr q24, [x8, #112]
	eor v7.16b, v7.16b, v24.16b
218:
	sub x8, x8, #128
	movz x6, #3328, lsl #0
	movk x6, #1802, lsl #16
	movk x6, #260, lsl #32
	movk x6, #2830, lsl #48
	movz x7, #1288, lsl #0
	movk x7, #3842, lsl #16
	movk x7, #2316, lsl #32
	movk x7, #774, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v0.16b, {v0.16b}, v25.16b
	tbl v1.16b, {v1.16b}, v25.16b
	tbl v2.16b, {v2.16b}, v25.16b
	tbl v3.16b, {v3.16b}, v25.16b
	tbl v4.16b, {v4.16b}, v25.16b
	tbl v5.16b, {v5.16b}, v25.16b
	tbl v6.16b, {v6.16b}, v25.16b
	tbl v7.16b, {v7.16b}, v25.16b
	eor v0.16b, v3.16b, v0.16b
	not v0.16b, v0.16b
	eor v2.16b, v7.16b, v2.16b
	eor v7.16b, v7.16b, v4.16b
	eor v6.16b, v6.16b, v7.16b
	not v6.16b, v6.16b
	eor v24.16b, v3.16b, v6.16b
	eor v3.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v3.16b
	not v5.16b, v5.16b
	eor v25.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v4.16b
	not v1.16b, v1.16b
	and v26.16b, v7.16b, v6.16b
	eor v27.16b, v7.16b, v25.16b
	and v28.16b, v27.16b, v4.16b
	eor v29.16b, v25.16b, v0.16b
	eor v30.16b, v24.16b, v1.16b
	eor v31.16b, v27.16b, v1.16b
	eor v16.16b, v7.16b, v30.16b
	eor v2.16b, v16.16b, v2.16b
	and v17.16b, v25.16b, v29.16b
	eor v18.16b, v29.16b, v2.16b
	eor v19.16b, v5.16b, v31.16b
	and v20.16b, v31.16b, v19.16b
	and v21.16b, v24.16b, v18.16b
	eor v22.16b, v4.16b, v19.16b
	eor v23.16b, v1.16b, v22.16b
	str q24, [x5, #0]
	and v24.16b, v1.16b, v22.16b
	eor v28.16b, v28.16b, v24.16b
	eor v20.16b, v20.16b, v24.16b
	and v24.16b, v3.16b, v2.16b
	eor v21.16b, v21.16b, v24.16b
	eor v17.16b, v17.16b, v24.16b
	eor v28.16b, v28.16b, v21.16b
	eor v28.16b, v28.16b, v23.16b
	eor v20.16b, v20.16b, v17.16b
	eor v20.16b, v20.16b, v5.16b
	eor v5.16b, v3.16b, v2.16b
	eor v23.16b, v22.16b, v18.16b
	and v24.16b, v30.16b, v23.16b
	eor v26.16b, v26.16b, v24.16b
	eor v26.16b, v26.16b, v21.16b
	eor v26.16b, v26.16b, v5.16b
	eor v5.16b, v19.16b, v2.16b
	and v21.16b, v16.16b, v5.16b
	eor v21.16b, v21.16b, v24.16b
	eor v21.16b, v21.16b, v17.16b
	eor v21.16b, v21.16b, v0.16b
	eor v0.16b, v28.16b, v20.16b
	eor v17.16b, v26.16b, v21.16b
	and v26.16b, v26.16b, v28.16b
	eor v24.16b, v20.16b, v26.16b
	eor v26.16b, v21.16b, v26.16b
	and v26.16b, v26.16b, v0.16b
	eor v26.16b, v26.16b, v20.16b
	and v16.16b, v26.16b, v16.16b
	and v5.16b, v26.16b, v5.16b
	eor v28.16b, v28.16b, v26.16b
	and v0.16b, v17.16b, v24.16b
	eor v0.16b, v0.16b, v21.16b
	and v19.16b, v0.16b, v19.16b
	and v31.16b, v0.16b, v31.16b
	eor v21.16b, v24.16b, v26.16b
	and v20.16b, v20.16b, v21.16b
	eor v28.16b, v20.16b, v28.16b
	eor v24.16b, v24.16b, v20.16b
	and v24.16b, v0.16b, v24.16b
	eor v17.16b, v17.16b, v24.16b
	and v6.16b, v28.16b, v6.16b
	and v7.16b, v28.16b, v7.16b
	and v4.16b, v17.16b, v4.16b
	and v27.16b, v17.16b, v27.16b
	eor v7.16b, v5.16b, v7.16b
	eor v24.16b, v17.16b, v28.16b
	and v29.16b, v24.16b, v29.16b
	eor v17.16b, v0.16b, v17.16b
	and v1.16b, v17.16b, v1.16b
	and v17.16b, v17.16b, v22.16b
	and v25.16b, v24.16b, v25.16b
	eor v28.16b, v26.16b, v28.16b
	eor v0.16b, v0.16b, v26.16b
	and v3.16b, v0.16b, v3.16b
	and v23.16b, v28.16b, v23.16b
	and v28.16b, v28.16b, v30.16b
	eor v24.16b, v0.16b, v24.16b
	and v0.16b, v0.16b, v2.16b
	eor v25.16b, v28.16b, v25.16b
	and v18.16b, v24.16b, v18.16b
	ldr q2, [x5, #0]
	and v24.16b, v24.16b, v2.16b
	eor v25.16b, v16.16b, v25.16b
	eor v0.16b, v0.16b, v3.16b
	eor v0.16b, v1.16b, v0.16b
	eor v0.16b, v27.16b, v0.16b
	eor v0.16b, v24.16b, v0.16b
	eor v0.16b, v29.16b, v0.16b
	eor v28.16b, v28.16b, v7.16b
	eor v17.16b, v17.16b, v0.16b
	eor v23.16b, v23.16b, v0.16b
	eor v19.16b, v19.16b, v17.16b
	eor v4.16b, v4.16b, v17.16b
	eor v20.16b, v5.16b, v23.16b
	eor v18.16b, v18.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v17.16b, v29.16b, v18.16b
	eor v23.16b, v19.16b, v23.16b
	eor v7.16b, v6.16b, v7.16b
	eor v31.16b, v31.16b, v7.16b
	eor v16.16b, v16.16b, v31.16b
	eor v18.16b, v6.16b, v23.16b
	eor v3.16b, v3.16b, v25.16b
	eor v24.16b, v24.16b, v25.16b
	eor v1.16b, v1.16b, v16.16b
	eor v21.16b, v27.16b, v16.16b
	eor v22.16b, v24.16b, v1.16b
	eor v24.16b, v17.16b, v24.16b
	eor v23.16b, v23.16b, v24.16b
	eor v28.16b, v28.16b, v23.16b
	mov v23.16b, v19.16b
	mov v19.16b, v28.16b
	mov v16.16b, v3.16b
	ldr q24, [x8, #0]
	eor v16.16b, v16.16b, v24.16b
	ldr q24, [x8, #16]
	eor v17.16b, v17.16b, v24.16b
	ldr q24, [x8, #32]
	eor v18.16b, v18.16b, v24.16b
	ldr q24, [x8, #48]
	eor v19.16b, v19.16b, v24.16b
	ldr q24, [x8, #64]
	eor v20.16b, v20.16b, v24.16b
	ldr q24, [x8, #80]
	eor v21.16b, v21.16b, v24.16b
	ldr q24, [x8, #96]
	eor v22.16b, v22.16b, v24.16b
	ldr q24, [x8, #112]
	eor v23.16b, v23.16b, v24.16b
	movz x6, #513, lsl #0
	movk x6, #3, lsl #16
	movk x6, #1541, lsl #32
	movk x6, #1031, lsl #48
	movz x7, #2569, lsl #0
	movk x7, #2059, lsl #16
	movk x7, #3597, lsl #32
	movk x7, #3087, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	rev32 v0.8h, v16.8h
	eor v0.16b, v0.16b, v16.16b
	rev32 v1.8h, v17.8h
	eor v1.16b, v1.16b, v17.16b
	rev32 v2.8h, v18.8h
	eor v2.16b, v2.16b, v18.16b
	rev32 v3.8h, v19.8h
	eor v3.16b, v3.16b, v19.16b
	rev32 v4.8h, v20.8h
	eor v4.16b, v4.16b, v20.16b
	rev32 v5.8h, v21.8h
	eor v5.16b, v5.16b, v21.16b
	rev32 v6.8h, v22.8h
	eor v6.16b, v6.16b, v22.16b
	rev32 v7.8h, v23.8h
	eor v7.16b, v7.16b, v23.16b
	eor v16.16b, v16.16b, v6.16b
	eor v17.16b, v17.16b, v6.16b
	eor v17.16b, v17.16b, v7.16b
	eor v18.16b, v18.16b, v0.16b
	eor v18.16b, v18.16b, v7.16b
	eor v19.16b, v19.16b, v1.16b
	eor v19.16b, v19.16b, v6.16b
	eor v20.16b, v20.16b, v2.16b
	eor v20.16b, v20.16b, v6.16b
	eor v20.16b, v20.16b, v7.16b
	eor v21.16b, v21.16b, v3.16b
	eor v21.16b, v21.16b, v7.16b
	eor v22.16b, v22.16b, v4.16b
	eor v23.16b, v23.16b, v5.16b
	tbl v0.16b, {v16.16b}, v25.16b
	eor v16.16b, v16.16b, v0.16b
	tbl v1.16b, {v17.16b}, v25.16b
	eor v17.16b, v17.16b, v1.16b
	tbl v2.16b, {v18.16b}, v25.16b
	eor v18.16b, v18.16b, v2.16b
	tbl v3.16b, {v19.16b}, v25.16b
	eor v19.16b, v19.16b, v3.16b
	tbl v4.16b, {v20.16b}, v25.16b
	eor v20.16b, v20.16b, v4.16b
	tbl v5.16b, {v21.16b}, v25.16b
	eor v21.16b, v21.16b, v5.16b
	tbl v6.16b, {v22.16b}, v25.16b
	eor v22.16b, v22.16b, v6.16b
	tbl v7.16b, {v23.16b}, v25.16b
	eor v23.16b, v23.16b, v7.16b
	eor v0.16b, v0.16b, v23.16b
	rev32 v24.8h, v16.8h
	eor v0.16b, v0.16b, v24.16b
	eor v1.16b, v1.16b, v16.16b
	eor v1.16b, v1.16b, v23.16b
	rev32 v24.8h, v17.8h
	eor v1.16b, v1.16b, v24.16b
	eor v2.16b, v2.16b, v17.16b
	rev32 v24.8h, v18.8h
	eor v2.16b, v2.16b, v24.16b
	eor v3.16b, v3.16b, v18.16b
	eor v3.16b, v3.16b, v23.16b
	rev32 v24.8h, v19.8h
	eor v3.16b, v3.16b, v24.16b
	eor v4.16b, v4.16b, v19.16b
	eor v4.16b, v4.16b, v23.16b
	rev32 v24.8h, v20.8h
	eor v4.16b, v4.16b, v24.16b
	eor v5.16b, v5.16b, v20.16b
	rev32 v24.8h, v21.8h
	eor v5.16b, v5.16b, v24.16b
	eor v6.16b, v6.16b, v21.16b
	rev32 v24.8h, v22.8h
	eor v6.16b, v6.16b, v24.16b
	eor v7.16b, v7.16b, v22.16b
	rev32 v24.8h, v23.8h
	eor v7.16b, v7.16b, v24.16b
	sub x9, x9, #1
	cbnz x9, 218b
	sub x8, x8, #128
	movz x6, #3328, lsl #0
	movk x6, #1802, lsl #16
	movk x6, #260, lsl #32
	movk x6, #2830, lsl #48
	movz x7, #1288, lsl #0
	movk x7, #3842, lsl #16
	movk x7, #2316, lsl #32
	movk x7, #774, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v0.16b, {v0.16b}, v25.16b
	tbl v1.16b, {v1.16b}, v25.16b
	tbl v2.16b, {v2.16b}, v25.16b
	tbl v3.16b, {v3.16b}, v25.16b
	tbl v4.16b, {v4.16b}, v25.16b
	tbl v5.16b, {v5.16b}, v25.16b
	tbl v6.16b, {v6.16b}, v25.16b
	tbl v7.16b, {v7.16b}, v25.16b
	eor v0.16b, v3.16b, v0.16b
	not v0.16b, v0.16b
	eor v2.16b, v7.16b, v2.16b
	eor v7.16b, v7.16b, v4.16b
	eor v6.16b, v6.16b, v7.16b
	not v6.16b, v6.16b
	eor v24.16b, v3.16b, v6.16b
	eor v3.16b, v4.16b, v3.16b
	eor v5.16b, v5.16b, v3.16b
	not v5.16b, v5.16b
	eor v25.16b, v4.16b, v6.16b
	eor v4.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v4.16b
	not v1.16b, v1.16b
	and v26.16b, v7.16b, v6.16b
	eor v27.16b, v7.16b, v25.16b
	and v28.16b, v27.16b, v4.16b
	eor v29.16b, v25.16b, v0.16b
	eor v30.16b, v24.16b, v1.16b
	eor v31.16b, v27.16b, v1.16b
	eor v16.16b, v7.16b, v30.16b
	eor v2.16b, v16.16b, v2.16b
	and v17.16b, v25.16b, v29.16b
	eor v18.16b, v29.16b, v2.16b
	eor v19.16b, v5.16b, v31.16b
	and v20.16b, v31.16b, v19.16b
	and v21.16b, v24.16b, v18.16b
	eor v22.16b, v4.16b, v19.16b
	eor v23.16b, v1.16b, v22.16b
	str q24, [x5, #0]
	and v24.16b, v1.16b, v22.16b
	eor v28.16b, v28.16b, v24.16b
	eor v20.16b, v20.16b, v24.16b
	and v24.16b, v3.16b, v2.16b
	eor v21.16b, v21.16b, v24.16b
	eor v17.16b, v17.16b, v24.16b
	eor v28.16b, v28.16b, v21.16b
	eor v28.16b, v28.16b, v23.16b
	eor v20.16b, v20.16b, v17.16b
	eor v20.16b, v20.16b, v5.16b
	eor v5.16b, v3.16b, v2.16b
	eor v23.16b, v22.16b, v18.16b
	and v24.16b, v30.16b, v23.16b
	eor v26.16b, v26.16b, v24.16b
	eor v26.16b, v26.16b, v21.16b
	eor v26.16b, v26.16b, v5.16b
	eor v5.16b, v19.16b, v2.16b
	and v21.16b, v16.16b, v5.16b
	eor v21.16b, v21.16b, v24.16b
	eor v21.16b, v21.16b, v17.16b
	eor v21.16b, v21.16b, v0.16b
	eor v0.16b, v28.16b, v20.16b
	eor v17.16b, v26.16b, v21.16b
	and v26.16b, v26.16b, v28.16b
	eor v24.16b, v20.16b, v26.16b
	eor v26.16b, v21.16b, v26.16b
	and v26.16b, v26.16b, v0.16b
	eor v26.16b, v26.16b, v20.16b
	and v16.16b, v26.16b, v16.16b
	and v5.16b, v26.16b, v5.16b
	eor v28.16b, v28.16b, v26.16b
	and v0.16b, v17.16b, v24.16b
	eor v0.16b, v0.16b, v21.16b
	and v19.16b, v0.16b, v19.16b
	and v31.16b, v0.16b, v31.16b
	eor v21.16b, v24.16b, v26.16b
	and v20.16b, v20.16b, v21.16b
	eor v28.16b, v20.16b, v28.16b
	eor v24.16b, v24.16b, v20.16b
	and v24.16b, v0.16b, v24.16b
	eor v17.16b, v17.16b, v24.16b
	and v6.16b, v28.16b, v6.16b
	and v7.16b, v28.16b, v7.16b
	and v4.16b, v17.16b, v4.16b
	and v27.16b, v17.16b, v27.16b
	eor v7.16b, v5.16b, v7.16b
	eor v24.16b, v17.16b, v28.16b
	and v29.16b, v24.16b, v29.16b
	eor v17.16b, v0.16b, v17.16b
	and v1.16b, v17.16b, v1.16b
	and v17.16b, v17.16b, v22.16b
	and v25.16b, v24.16b, v25.16b
	eor v28.16b, v26.16b, v28.16b
	eor v0.16b, v0.16b, v26.16b
	and v3.16b, v0.16b, v3.16b
	and v23.16b, v28.16b, v23.16b
	and v28.16b, v28.16b, v30.16b
	eor v24.16b, v0.16b, v24.16b
	and v0.16b, v0.16b, v2.16b
	eor v25.16b, v28.16b, v25.16b
	and v18.16b, v24.16b, v18.16b
	ldr q2, [x5, #0]
	and v24.16b, v24.16b, v2.16b
	eor v25.16b, v16.16b, v25.16b
	eor v0.16b, v0.16b, v3.16b
	eor v0.16b, v1.16b, v0.16b
	eor v0.16b, v27.16b, v0.16b
	eor v0.16b, v24.16b, v0.16b
	eor v0.16b, v29.16b, v0.16b
	eor v28.16b, v28.16b, v7.16b
	eor v17.16b, v17.16b, v0.16b
	eor v23.16b, v23.16b, v0.16b
	eor v19.16b, v19.16b, v17.16b
	eor v4.16b, v4.16b, v17.16b
	eor v20.16b, v5.16b, v23.16b
	eor v18.16b, v18.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v17.16b, v29.16b, v18.16b
	eor v23.16b, v19.16b, v23.16b
	eor v7.16b, v6.16b, v7.16b
	eor v31.16b, v31.16b, v7.16b
	eor v16.16b, v16.16b, v31.16b
	eor v18.16b, v6.16b, v23.16b
	eor v3.16b, v3.16b, v25.16b
	eor v24.16b, v24.16b, v25.16b
	eor v1.16b, v1.16b, v16.16b
	eor v21.16b, v27.16b, v16.16b
	eor v22.16b, v24.16b, v1.16b
	eor v24.16b, v17.16b, v24.16b
	eor v23.16b, v23.16b, v24.16b
	eor v28.16b, v28.16b, v23.16b
	mov v23.16b, v19.16b
	mov v19.16b, v28.16b
	mov v16.16b, v3.16b
	ldr q24, [x8, #0]
	eor v16.16b, v16.16b, v24.16b
	ldr q24, [x8, #16]
	eor v17.16b, v17.16b, v24.16b
	ldr q24, [x8, #32]
	eor v18.16b, v18.16b, v24.16b
	ldr q24, [x8, #48]
	eor v19.16b, v19.16b, v24.16b
	ldr q24, [x8, #64]
	eor v20.16b, v20.16b, v24.16b
	ldr q24, [x8, #80]
	eor v21.16b, v21.16b, v24.16b
	ldr q24, [x8, #96]
	eor v22.16b, v22.16b, v24.16b
	ldr q24, [x8, #112]
	eor v23.16b, v23.16b, v24.16b
	movz x6, #21845, lsl #0
	movk x6, #21845, lsl #16
	movk x6, #21845, lsl #32
	movk x6, #21845, lsl #48
	dup v29.2d, x6
	movz x6, #13107, lsl #0
	movk x6, #13107, lsl #16
	movk x6, #13107, lsl #32
	movk x6, #13107, lsl #48
	dup v30.2d, x6
	movz x6, #3855, lsl #0
	movk x6, #3855, lsl #16
	movk x6, #3855, lsl #32
	movk x6, #3855, lsl #48
	dup v31.2d, x6
	ushr v24.2d, v16.2d, #1
	eor v24.16b, v24.16b, v17.16b
	and v24.16b, v24.16b, v29.16b
	eor v17.16b, v17.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v18.2d, #1
	eor v24.16b, v24.16b, v19.16b
	and v24.16b, v24.16b, v29.16b
	eor v19.16b, v19.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v18.16b, v18.16b, v24.16b
	ushr v24.2d, v20.2d, #1
	eor v24.16b, v24.16b, v21.16b
	and v24.16b, v24.16b, v29.16b
	eor v21.16b, v21.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v20.16b, v20.16b, v24.16b
	ushr v24.2d, v22.2d, #1
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v29.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #1
	eor v22.16b, v22.16b, v24.16b
	ushr v24.2d, v16.2d, #2
	eor v24.16b, v24.16b, v18.16b
	and v24.16b, v24.16b, v30.16b
	eor v18.16b, v18.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v17.2d, #2
	eor v24.16b, v24.16b, v19.16b
	and v24.16b, v24.16b, v30.16b
	eor v19.16b, v19.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v17.16b, v17.16b, v24.16b
	ushr v24.2d, v20.2d, #2
	eor v24.16b, v24.16b, v22.16b
	and v24.16b, v24.16b, v30.16b
	eor v22.16b, v22.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v20.16b, v20.16b, v24.16b
	ushr v24.2d, v21.2d, #2
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v30.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #2
	eor v21.16b, v21.16b, v24.16b
	ushr v24.2d, v16.2d, #4
	eor v24.16b, v24.16b, v20.16b
	and v24.16b, v24.16b, v31.16b
	eor v20.16b, v20.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v16.16b, v16.16b, v24.16b
	ushr v24.2d, v17.2d, #4
	eor v24.16b, v24.16b, v21.16b
	and v24.16b, v24.16b, v31.16b
	eor v21.16b, v21.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v17.16b, v17.16b, v24.16b
	ushr v24.2d, v18.2d, #4
	eor v24.16b, v24.16b, v22.16b
	and v24.16b, v24.16b, v31.16b
	eor v22.16b, v22.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v18.16b, v18.16b, v24.16b
	ushr v24.2d, v19.2d, #4
	eor v24.16b, v24.16b, v23.16b
	and v24.16b, v24.16b, v31.16b
	eor v23.16b, v23.16b, v24.16b
	shl v24.2d, v24.2d, #4
	eor v19.16b, v19.16b, v24.16b
	str q16, [x3, #0]
	sub x6, x4, #1
	cbnz x6, 219f
	b 220f
219:
	str q17, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 221f
	b 222f
221:
	str q18, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 223f
	b 224f
223:
	str q19, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 225f
	b 226f
225:
	str q20, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 227f
	b 228f
227:
	str q21, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 229f
	b 230f
229:
	str q22, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 231f
	b 232f
231:
	str q23, [x3, #112]
232:
230:
228:
226:
224:
222:
220:
	sub x6, x4, #1
	lsr x6, x6, #3
	cbnz x6, 233f
	movz x4, #0, lsl #0
	b 234f
233:
	add x3, x3, #128
	sub x4, x4, #8
234:
	cbnz x4, 23b
	b 21f
20:
21:
	ret
	.p2align 6
