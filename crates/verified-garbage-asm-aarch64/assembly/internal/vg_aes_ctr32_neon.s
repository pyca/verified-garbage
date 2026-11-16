// The functions of `src/internal/vg_aes_ctr32_neon.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ctr32_neon:
	cbz x4, 20f
	sub x6, x4, #1
	lsr x6, x6, #2
	cbz x6, 22f
	ldr w10, [x2, #12]
	rev w10, w10
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
	add w12, w10, #0
	rev w12, w12
	ldr q0, [x2, #0]
	mov v0.s[3], w12
	add w12, w10, #1
	rev w12, w12
	ldr q1, [x2, #0]
	mov v1.s[3], w12
	add w12, w10, #2
	rev w12, w12
	ldr q2, [x2, #0]
	mov v2.s[3], w12
	add w12, w10, #3
	rev w12, w12
	ldr q3, [x2, #0]
	mov v3.s[3], w12
	add w12, w10, #4
	rev w12, w12
	ldr q4, [x2, #0]
	mov v4.s[3], w12
	add w12, w10, #5
	rev w12, w12
	ldr q5, [x2, #0]
	mov v5.s[3], w12
	add w12, w10, #6
	rev w12, w12
	ldr q6, [x2, #0]
	mov v6.s[3], w12
	add w12, w10, #7
	rev w12, w12
	ldr q7, [x2, #0]
	mov v7.s[3], w12
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
26:
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
	cbnz x9, 26b
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
	ldr q31, [x3, #0]
	eor v16.16b, v16.16b, v31.16b
	str q16, [x3, #0]
	sub x6, x4, #1
	cbnz x6, 27f
	b 28f
27:
	ldr q31, [x3, #16]
	eor v17.16b, v17.16b, v31.16b
	str q17, [x3, #16]
	sub x6, x4, #2
	cbnz x6, 29f
	b 210f
29:
	ldr q31, [x3, #32]
	eor v18.16b, v18.16b, v31.16b
	str q18, [x3, #32]
	sub x6, x4, #3
	cbnz x6, 211f
	b 212f
211:
	ldr q31, [x3, #48]
	eor v19.16b, v19.16b, v31.16b
	str q19, [x3, #48]
	sub x6, x4, #4
	cbnz x6, 213f
	b 214f
213:
	ldr q31, [x3, #64]
	eor v20.16b, v20.16b, v31.16b
	str q20, [x3, #64]
	sub x6, x4, #5
	cbnz x6, 215f
	b 216f
215:
	ldr q31, [x3, #80]
	eor v21.16b, v21.16b, v31.16b
	str q21, [x3, #80]
	sub x6, x4, #6
	cbnz x6, 217f
	b 218f
217:
	ldr q31, [x3, #96]
	eor v22.16b, v22.16b, v31.16b
	str q22, [x3, #96]
	sub x6, x4, #7
	cbnz x6, 219f
	b 220f
219:
	ldr q31, [x3, #112]
	eor v23.16b, v23.16b, v31.16b
	str q23, [x3, #112]
220:
218:
216:
214:
212:
210:
28:
	sub x6, x4, #1
	lsr x6, x6, #3
	cbnz x6, 221f
	add w10, w10, w4
	movz x4, #0, lsl #0
	b 222f
221:
	add w10, w10, #8
	add x3, x3, #128
	sub x4, x4, #8
222:
	cbnz x4, 25b
	rev w12, w10
	str w12, [x2, #12]
	b 23f
22:
	add x8, x3, #0
	add x9, x0, #0
	add x10, x1, #0
223:
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
224:
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
	cbnz x1, 224b
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
	cbnz x4, 223b
23:
	b 21f
20:
21:
	ret
	.p2align 6
