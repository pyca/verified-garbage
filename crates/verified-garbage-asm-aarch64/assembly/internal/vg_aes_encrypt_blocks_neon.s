// The functions of `src/internal/vg_aes_encrypt_blocks_neon.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_encrypt_blocks_neon:
	sub x6, x3, #1
	cbz x6, 20f
	add x5, x4, #0
	add x4, x3, #0
	add x3, x2, #0
	cbz x4, 22f
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
24:
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
	cbnz x8, 24b
25:
	ldr q0, [x3, #0]
	sub x6, x4, #1
	cbnz x6, 26f
	b 27f
26:
	ldr q1, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 28f
	b 29f
28:
	ldr q2, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 210f
	b 211f
210:
	ldr q3, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 212f
	b 213f
212:
	ldr q4, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 214f
	b 215f
214:
	ldr q5, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 216f
	b 217f
216:
	ldr q6, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 218f
	b 219f
218:
	ldr q7, [x3, #112]
219:
217:
215:
213:
211:
29:
27:
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
	add x8, x5, #128
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
220:
	add x8, x8, #128
	eor v5.16b, v6.16b, v5.16b
	eor v24.16b, v5.16b, v0.16b
	eor v25.16b, v4.16b, v2.16b
	eor v26.16b, v24.16b, v4.16b
	eor v4.16b, v7.16b, v4.16b
	eor v27.16b, v7.16b, v1.16b
	eor v1.16b, v24.16b, v1.16b
	eor v28.16b, v7.16b, v2.16b
	eor v29.16b, v27.16b, v25.16b
	eor v3.16b, v3.16b, v29.16b
	eor v2.16b, v3.16b, v2.16b
	eor v3.16b, v3.16b, v6.16b
	and v6.16b, v1.16b, v24.16b
	eor v30.16b, v2.16b, v0.16b
	eor v31.16b, v3.16b, v4.16b
	eor v16.16b, v24.16b, v7.16b
	eor v17.16b, v1.16b, v28.16b
	and v18.16b, v17.16b, v30.16b
	and v19.16b, v4.16b, v31.16b
	eor v20.16b, v2.16b, v5.16b
	eor v5.16b, v5.16b, v31.16b
	eor v7.16b, v7.16b, v5.16b
	eor v21.16b, v20.16b, v31.16b
	and v22.16b, v28.16b, v20.16b
	eor v22.16b, v22.16b, v19.16b
	eor v23.16b, v0.16b, v31.16b
	str q31, [x5, #0]
	and v31.16b, v25.16b, v21.16b
	eor v31.16b, v31.16b, v19.16b
	and v19.16b, v29.16b, v2.16b
	eor v18.16b, v18.16b, v19.16b
	eor v18.16b, v18.16b, v31.16b
	eor v18.16b, v18.16b, v3.16b
	and v3.16b, v26.16b, v0.16b
	eor v3.16b, v3.16b, v19.16b
	eor v3.16b, v3.16b, v22.16b
	and v19.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v19.16b
	eor v6.16b, v6.16b, v31.16b
	eor v31.16b, v20.16b, v28.16b
	eor v3.16b, v3.16b, v31.16b
	and v31.16b, v16.16b, v23.16b
	eor v31.16b, v31.16b, v19.16b
	eor v31.16b, v31.16b, v22.16b
	eor v31.16b, v31.16b, v7.16b
	eor v7.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v7.16b
	eor v7.16b, v18.16b, v3.16b
	and v18.16b, v18.16b, v6.16b
	eor v22.16b, v31.16b, v18.16b
	eor v18.16b, v3.16b, v18.16b
	and v19.16b, v7.16b, v22.16b
	eor v19.16b, v19.16b, v3.16b
	and v16.16b, v19.16b, v16.16b
	and v23.16b, v19.16b, v23.16b
	eor v3.16b, v6.16b, v31.16b
	and v18.16b, v18.16b, v3.16b
	eor v18.16b, v18.16b, v31.16b
	eor v6.16b, v6.16b, v18.16b
	and v0.16b, v18.16b, v0.16b
	and v26.16b, v18.16b, v26.16b
	eor v3.16b, v22.16b, v18.16b
	and v31.16b, v31.16b, v3.16b
	eor v6.16b, v31.16b, v6.16b
	eor v22.16b, v22.16b, v31.16b
	and v30.16b, v6.16b, v30.16b
	and v22.16b, v19.16b, v22.16b
	eor v7.16b, v7.16b, v22.16b
	and v24.16b, v7.16b, v24.16b
	and v1.16b, v7.16b, v1.16b
	eor v1.16b, v23.16b, v1.16b
	and v17.16b, v6.16b, v17.16b
	eor v23.16b, v0.16b, v23.16b
	eor v26.16b, v17.16b, v26.16b
	eor v22.16b, v7.16b, v6.16b
	eor v6.16b, v18.16b, v6.16b
	eor v18.16b, v19.16b, v18.16b
	eor v19.16b, v19.16b, v7.16b
	and v2.16b, v6.16b, v2.16b
	and v6.16b, v6.16b, v29.16b
	eor v6.16b, v6.16b, v17.16b
	and v28.16b, v22.16b, v28.16b
	and v5.16b, v19.16b, v5.16b
	and v19.16b, v19.16b, v27.16b
	eor v0.16b, v0.16b, v19.16b
	and v4.16b, v18.16b, v4.16b
	ldr q27, [x5, #0]
	and v27.16b, v18.16b, v27.16b
	eor v19.16b, v19.16b, v1.16b
	eor v18.16b, v18.16b, v22.16b
	and v22.16b, v22.16b, v20.16b
	eor v2.16b, v2.16b, v5.16b
	and v21.16b, v18.16b, v21.16b
	and v18.16b, v18.16b, v25.16b
	eor v28.16b, v18.16b, v28.16b
	eor v4.16b, v4.16b, v18.16b
	eor v22.16b, v21.16b, v22.16b
	eor v27.16b, v27.16b, v21.16b
	eor v5.16b, v5.16b, v27.16b
	eor v0.16b, v0.16b, v2.16b
	eor v16.16b, v16.16b, v0.16b
	eor v0.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v0.16b
	not v1.16b, v1.16b
	eor v4.16b, v24.16b, v4.16b
	eor v22.16b, v22.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v24.16b, v24.16b, v5.16b
	eor v16.16b, v16.16b, v22.16b
	eor v17.16b, v19.16b, v22.16b
	not v17.16b, v17.16b
	eor v30.16b, v30.16b, v6.16b
	eor v5.16b, v5.16b, v6.16b
	eor v20.16b, v2.16b, v30.16b
	eor v19.16b, v23.16b, v30.16b
	eor v18.16b, v26.16b, v16.16b
	eor v16.16b, v24.16b, v16.16b
	eor v21.16b, v28.16b, v16.16b
	not v21.16b, v21.16b
	eor v22.16b, v24.16b, v20.16b
	not v22.16b, v22.16b
	mov v23.16b, v5.16b
	mov v16.16b, v1.16b
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v16.16b, {v16.16b}, v25.16b
	tbl v17.16b, {v17.16b}, v25.16b
	tbl v18.16b, {v18.16b}, v25.16b
	tbl v19.16b, {v19.16b}, v25.16b
	tbl v20.16b, {v20.16b}, v25.16b
	tbl v21.16b, {v21.16b}, v25.16b
	tbl v22.16b, {v22.16b}, v25.16b
	tbl v23.16b, {v23.16b}, v25.16b
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
	sub x9, x9, #1
	cbnz x9, 220b
	add x8, x8, #128
	eor v5.16b, v6.16b, v5.16b
	eor v24.16b, v5.16b, v0.16b
	eor v25.16b, v4.16b, v2.16b
	eor v26.16b, v24.16b, v4.16b
	eor v4.16b, v7.16b, v4.16b
	eor v27.16b, v7.16b, v1.16b
	eor v1.16b, v24.16b, v1.16b
	eor v28.16b, v7.16b, v2.16b
	eor v29.16b, v27.16b, v25.16b
	eor v3.16b, v3.16b, v29.16b
	eor v2.16b, v3.16b, v2.16b
	eor v3.16b, v3.16b, v6.16b
	and v6.16b, v1.16b, v24.16b
	eor v30.16b, v2.16b, v0.16b
	eor v31.16b, v3.16b, v4.16b
	eor v16.16b, v24.16b, v7.16b
	eor v17.16b, v1.16b, v28.16b
	and v18.16b, v17.16b, v30.16b
	and v19.16b, v4.16b, v31.16b
	eor v20.16b, v2.16b, v5.16b
	eor v5.16b, v5.16b, v31.16b
	eor v7.16b, v7.16b, v5.16b
	eor v21.16b, v20.16b, v31.16b
	and v22.16b, v28.16b, v20.16b
	eor v22.16b, v22.16b, v19.16b
	eor v23.16b, v0.16b, v31.16b
	str q31, [x5, #0]
	and v31.16b, v25.16b, v21.16b
	eor v31.16b, v31.16b, v19.16b
	and v19.16b, v29.16b, v2.16b
	eor v18.16b, v18.16b, v19.16b
	eor v18.16b, v18.16b, v31.16b
	eor v18.16b, v18.16b, v3.16b
	and v3.16b, v26.16b, v0.16b
	eor v3.16b, v3.16b, v19.16b
	eor v3.16b, v3.16b, v22.16b
	and v19.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v19.16b
	eor v6.16b, v6.16b, v31.16b
	eor v31.16b, v20.16b, v28.16b
	eor v3.16b, v3.16b, v31.16b
	and v31.16b, v16.16b, v23.16b
	eor v31.16b, v31.16b, v19.16b
	eor v31.16b, v31.16b, v22.16b
	eor v31.16b, v31.16b, v7.16b
	eor v7.16b, v27.16b, v5.16b
	eor v6.16b, v6.16b, v7.16b
	eor v7.16b, v18.16b, v3.16b
	and v18.16b, v18.16b, v6.16b
	eor v22.16b, v31.16b, v18.16b
	eor v18.16b, v3.16b, v18.16b
	and v19.16b, v7.16b, v22.16b
	eor v19.16b, v19.16b, v3.16b
	and v16.16b, v19.16b, v16.16b
	and v23.16b, v19.16b, v23.16b
	eor v3.16b, v6.16b, v31.16b
	and v18.16b, v18.16b, v3.16b
	eor v18.16b, v18.16b, v31.16b
	eor v6.16b, v6.16b, v18.16b
	and v0.16b, v18.16b, v0.16b
	and v26.16b, v18.16b, v26.16b
	eor v3.16b, v22.16b, v18.16b
	and v31.16b, v31.16b, v3.16b
	eor v6.16b, v31.16b, v6.16b
	eor v22.16b, v22.16b, v31.16b
	and v30.16b, v6.16b, v30.16b
	and v22.16b, v19.16b, v22.16b
	eor v7.16b, v7.16b, v22.16b
	and v24.16b, v7.16b, v24.16b
	and v1.16b, v7.16b, v1.16b
	eor v1.16b, v23.16b, v1.16b
	and v17.16b, v6.16b, v17.16b
	eor v23.16b, v0.16b, v23.16b
	eor v26.16b, v17.16b, v26.16b
	eor v22.16b, v7.16b, v6.16b
	eor v6.16b, v18.16b, v6.16b
	eor v18.16b, v19.16b, v18.16b
	eor v19.16b, v19.16b, v7.16b
	and v2.16b, v6.16b, v2.16b
	and v6.16b, v6.16b, v29.16b
	eor v6.16b, v6.16b, v17.16b
	and v28.16b, v22.16b, v28.16b
	and v5.16b, v19.16b, v5.16b
	and v19.16b, v19.16b, v27.16b
	eor v0.16b, v0.16b, v19.16b
	and v4.16b, v18.16b, v4.16b
	ldr q27, [x5, #0]
	and v27.16b, v18.16b, v27.16b
	eor v19.16b, v19.16b, v1.16b
	eor v18.16b, v18.16b, v22.16b
	and v22.16b, v22.16b, v20.16b
	eor v2.16b, v2.16b, v5.16b
	and v21.16b, v18.16b, v21.16b
	and v18.16b, v18.16b, v25.16b
	eor v28.16b, v18.16b, v28.16b
	eor v4.16b, v4.16b, v18.16b
	eor v22.16b, v21.16b, v22.16b
	eor v27.16b, v27.16b, v21.16b
	eor v5.16b, v5.16b, v27.16b
	eor v0.16b, v0.16b, v2.16b
	eor v16.16b, v16.16b, v0.16b
	eor v0.16b, v4.16b, v0.16b
	eor v1.16b, v1.16b, v0.16b
	not v1.16b, v1.16b
	eor v4.16b, v24.16b, v4.16b
	eor v22.16b, v22.16b, v4.16b
	eor v6.16b, v6.16b, v4.16b
	eor v24.16b, v24.16b, v5.16b
	eor v16.16b, v16.16b, v22.16b
	eor v17.16b, v19.16b, v22.16b
	not v17.16b, v17.16b
	eor v30.16b, v30.16b, v6.16b
	eor v5.16b, v5.16b, v6.16b
	eor v20.16b, v2.16b, v30.16b
	eor v19.16b, v23.16b, v30.16b
	eor v18.16b, v26.16b, v16.16b
	eor v16.16b, v24.16b, v16.16b
	eor v21.16b, v28.16b, v16.16b
	not v21.16b, v21.16b
	eor v22.16b, v24.16b, v20.16b
	not v22.16b, v22.16b
	mov v23.16b, v5.16b
	mov v16.16b, v1.16b
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	tbl v16.16b, {v16.16b}, v25.16b
	tbl v17.16b, {v17.16b}, v25.16b
	tbl v18.16b, {v18.16b}, v25.16b
	tbl v19.16b, {v19.16b}, v25.16b
	tbl v20.16b, {v20.16b}, v25.16b
	tbl v21.16b, {v21.16b}, v25.16b
	tbl v22.16b, {v22.16b}, v25.16b
	tbl v23.16b, {v23.16b}, v25.16b
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
	cbnz x6, 221f
	b 222f
221:
	str q17, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 223f
	b 224f
223:
	str q18, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 225f
	b 226f
225:
	str q19, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 227f
	b 228f
227:
	str q20, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 229f
	b 230f
229:
	str q21, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 231f
	b 232f
231:
	str q22, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 233f
	b 234f
233:
	str q23, [x3, #112]
234:
232:
230:
228:
226:
224:
222:
	sub x6, x4, #1
	lsr x6, x6, #3
	cbnz x6, 235f
	movz x4, #0, lsl #0
	b 236f
235:
	add x3, x3, #128
	sub x4, x4, #8
236:
	cbnz x4, 25b
	b 23f
22:
23:
	b 21f
20:
	ldr q0, [x2, #0]
	movz x6, #31843, lsl #0
	movk x6, #31607, lsl #16
	movk x6, #27634, lsl #32
	movk x6, #50543, lsl #48
	movz x7, #304, lsl #0
	movk x7, #11111, lsl #16
	movk x7, #55294, lsl #32
	movk x7, #30379, lsl #48
	mov v16.d[0], x6
	mov v16.d[1], x7
	movz x6, #33482, lsl #0
	movk x6, #32201, lsl #16
	movk x6, #23034, lsl #32
	movk x6, #61511, lsl #48
	movz x7, #54445, lsl #0
	movk x7, #44962, lsl #16
	movk x7, #42140, lsl #32
	movk x7, #49266, lsl #48
	mov v17.d[0], x6
	mov v17.d[1], x7
	movz x6, #64951, lsl #0
	movk x6, #9875, lsl #16
	movk x6, #16182, lsl #32
	movk x6, #52471, lsl #48
	movz x7, #42292, lsl #0
	movk x7, #61925, lsl #16
	movk x7, #55409, lsl #32
	movk x7, #5425, lsl #48
	mov v18.d[0], x6
	mov v18.d[1], x7
	movz x6, #50948, lsl #0
	movk x6, #49955, lsl #16
	movk x6, #38424, lsl #32
	movk x6, #39429, lsl #48
	movz x7, #4615, lsl #0
	movk x7, #57984, lsl #16
	movk x7, #10219, lsl #32
	movk x7, #30130, lsl #48
	mov v19.d[0], x6
	mov v19.d[1], x7
	movz x6, #33545, lsl #0
	movk x6, #6700, lsl #16
	movk x6, #28187, lsl #32
	movk x6, #41050, lsl #48
	movz x7, #15186, lsl #0
	movk x7, #46038, lsl #16
	movk x7, #58153, lsl #32
	movk x7, #33839, lsl #48
	mov v20.d[0], x6
	mov v20.d[1], x7
	movz x6, #53587, lsl #0
	movk x6, #60672, lsl #16
	movk x6, #64544, lsl #32
	movk x6, #23473, lsl #48
	movz x7, #52074, lsl #0
	movk x7, #14782, lsl #16
	movk x7, #19530, lsl #32
	movk x7, #53080, lsl #48
	mov v21.d[0], x6
	mov v21.d[1], x7
	movz x6, #61392, lsl #0
	movk x6, #64426, lsl #16
	movk x6, #19779, lsl #32
	movk x6, #34099, lsl #48
	movz x7, #63813, lsl #0
	movk x7, #32514, lsl #16
	movk x7, #15440, lsl #32
	movk x7, #43167, lsl #48
	mov v22.d[0], x6
	mov v22.d[1], x7
	movz x6, #41809, lsl #0
	movk x6, #36672, lsl #16
	movk x6, #40338, lsl #32
	movk x6, #62776, lsl #48
	movz x7, #46780, lsl #0
	movk x7, #8666, lsl #16
	movk x7, #65296, lsl #32
	movk x7, #54003, lsl #48
	mov v23.d[0], x6
	mov v23.d[1], x7
	movz x6, #3277, lsl #0
	movk x6, #60435, lsl #16
	movk x6, #38751, lsl #32
	movk x6, #5956, lsl #48
	movz x7, #42948, lsl #0
	movk x7, #15742, lsl #16
	movk x7, #23908, lsl #32
	movk x7, #29465, lsl #48
	mov v24.d[0], x6
	mov v24.d[1], x7
	movz x6, #33120, lsl #0
	movk x6, #56399, lsl #16
	movk x6, #10786, lsl #32
	movk x6, #34960, lsl #48
	movz x7, #60998, lsl #0
	movk x7, #5304, lsl #16
	movk x7, #24286, lsl #32
	movk x7, #56075, lsl #48
	mov v25.d[0], x6
	mov v25.d[1], x7
	movz x6, #13024, lsl #0
	movk x6, #2618, lsl #16
	movk x6, #1609, lsl #32
	movk x6, #23588, lsl #48
	movz x7, #54210, lsl #0
	movk x7, #25260, lsl #16
	movk x7, #38289, lsl #32
	movk x7, #31204, lsl #48
	mov v26.d[0], x6
	mov v26.d[1], x7
	movz x6, #51431, lsl #0
	movk x6, #27959, lsl #16
	movk x6, #54669, lsl #32
	movk x6, #43342, lsl #48
	movz x7, #22124, lsl #0
	movk x7, #60148, lsl #16
	movk x7, #31333, lsl #32
	movk x7, #2222, lsl #48
	mov v27.d[0], x6
	mov v27.d[1], x7
	movz x6, #30906, lsl #0
	movk x6, #11813, lsl #16
	movk x6, #42524, lsl #32
	movk x6, #50868, lsl #48
	movz x7, #56808, lsl #0
	movk x7, #8052, lsl #16
	movk x7, #48459, lsl #32
	movk x7, #35467, lsl #48
	mov v28.d[0], x6
	mov v28.d[1], x7
	movz x6, #15984, lsl #0
	movk x6, #26293, lsl #16
	movk x6, #840, lsl #32
	movk x6, #3830, lsl #48
	movz x7, #13665, lsl #0
	movk x7, #47447, lsl #16
	movk x7, #49542, lsl #32
	movk x7, #40477, lsl #48
	mov v29.d[0], x6
	mov v29.d[1], x7
	movz x6, #63713, lsl #0
	movk x6, #4504, lsl #16
	movk x6, #55657, lsl #32
	movk x6, #38030, lsl #48
	movz x7, #7835, lsl #0
	movk x7, #59783, lsl #16
	movk x7, #21966, lsl #32
	movk x7, #57128, lsl #48
	mov v30.d[0], x6
	mov v30.d[1], x7
	movz x6, #41356, lsl #0
	movk x6, #3465, lsl #16
	movk x6, #59071, lsl #32
	movk x6, #26690, lsl #48
	movz x7, #39233, lsl #0
	movk x7, #3885, lsl #16
	movk x7, #21680, lsl #32
	movk x7, #5819, lsl #48
	mov v31.d[0], x6
	mov v31.d[1], x7
	movz x6, #1280, lsl #0
	movk x6, #3850, lsl #16
	movk x6, #2308, lsl #32
	movk x6, #782, lsl #48
	movz x7, #3336, lsl #0
	movk x7, #1794, lsl #16
	movk x7, #268, lsl #32
	movk x7, #2822, lsl #48
	mov v4.d[0], x6
	mov v4.d[1], x7
	movz w6, #128, lsl #0
	dup v5.16b, w6
	movz w6, #64, lsl #0
	dup v6.16b, w6
	movz w6, #27, lsl #0
	dup v7.16b, w6
	ldr q1, [x0, #0]
	eor v0.16b, v0.16b, v1.16b
	sub x1, x1, #1
237:
	tbl v0.16b, {v0.16b}, v4.16b
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	sshr v1.16b, v0.16b, #7
	shl v2.16b, v0.16b, #1
	and v1.16b, v1.16b, v7.16b
	eor v2.16b, v2.16b, v1.16b
	rev32 v1.8h, v0.8h
	eor v2.16b, v2.16b, v1.16b
	eor v0.16b, v0.16b, v2.16b
	ushr v1.4s, v0.4s, #8
	sli v1.4s, v0.4s, #24
	eor v0.16b, v1.16b, v2.16b
	add x0, x0, #16
	ldr q1, [x0, #0]
	eor v0.16b, v0.16b, v1.16b
	sub x1, x1, #1
	cbnz x1, 237b
	tbl v0.16b, {v0.16b}, v4.16b
	eor v1.16b, v0.16b, v6.16b
	eor v2.16b, v0.16b, v5.16b
	eor v3.16b, v1.16b, v5.16b
	tbl v0.16b, {v16.16b, v17.16b, v18.16b, v19.16b}, v0.16b
	tbl v1.16b, {v20.16b, v21.16b, v22.16b, v23.16b}, v1.16b
	tbl v2.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v2.16b
	tbl v3.16b, {v28.16b, v29.16b, v30.16b, v31.16b}, v3.16b
	orr v2.16b, v2.16b, v3.16b
	orr v0.16b, v0.16b, v1.16b
	orr v0.16b, v0.16b, v2.16b
	ldr q1, [x0, #16]
	eor v0.16b, v0.16b, v1.16b
	str q0, [x2, #0]
21:
	ret
	.p2align 6
