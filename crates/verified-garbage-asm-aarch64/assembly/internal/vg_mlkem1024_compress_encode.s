// The functions of `src/internal/vg_mlkem1024_compress_encode.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_compress_encode:
	sub x9, x3, #160
	cbz x9, 20f
	movz x9, #60398, lsl #0
	movk x9, #4, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #65280, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #2047, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x9, #256, lsl #0
	movk x9, #770, lsl #16
	movk x9, #1284, lsl #32
	movk x9, #1798, lsl #48
	dup v20.2d, x9
	movz x9, #2312, lsl #0
	movk x9, #4106, lsl #16
	movk x9, #4625, lsl #32
	movk x9, #5139, lsl #48
	mov v20.d[1], x9
	movz x9, #5653, lsl #0
	movk x9, #6167, lsl #16
	movk x9, #6681, lsl #32
	movk x9, #8480, lsl #48
	dup v21.2d, x9
	movz x9, #8994, lsl #0
	movk x9, #9508, lsl #16
	movk x9, #10022, lsl #32
	movk x9, #10536, lsl #48
	mov v21.d[1], x9
	movz x9, #12330, lsl #0
	movk x9, #12849, lsl #16
	movk x9, #13363, lsl #32
	movk x9, #13877, lsl #48
	dup v22.2d, x9
	movz x9, #14391, lsl #0
	movk x9, #14905, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v22.d[1], x9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
22:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
	ldr q4, [x0, #64]
	ldr q5, [x0, #80]
	ldr q6, [x0, #96]
	ldr q7, [x0, #112]
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #19
	and v0.16b, v0.16b, v18.16b
	mul v1.4s, v1.4s, v16.4s
	add v1.4s, v1.4s, v17.4s
	ushr v1.4s, v1.4s, #19
	and v1.16b, v1.16b, v18.16b
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #19
	and v2.16b, v2.16b, v18.16b
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #19
	and v3.16b, v3.16b, v18.16b
	mul v4.4s, v4.4s, v16.4s
	add v4.4s, v4.4s, v17.4s
	ushr v4.4s, v4.4s, #19
	and v4.16b, v4.16b, v18.16b
	mul v5.4s, v5.4s, v16.4s
	add v5.4s, v5.4s, v17.4s
	ushr v5.4s, v5.4s, #19
	and v5.16b, v5.16b, v18.16b
	mul v6.4s, v6.4s, v16.4s
	add v6.4s, v6.4s, v17.4s
	ushr v6.4s, v6.4s, #19
	and v6.16b, v6.16b, v18.16b
	mul v7.4s, v7.4s, v16.4s
	add v7.4s, v7.4s, v17.4s
	ushr v7.4s, v7.4s, #19
	and v7.16b, v7.16b, v18.16b
	uzp2 v19.4s, v0.4s, v1.4s
	uzp1 v0.4s, v0.4s, v1.4s
	shl v19.4s, v19.4s, #11
	orr v0.16b, v0.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v1.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #11
	orr v1.16b, v1.16b, v19.16b
	uzp2 v19.4s, v4.4s, v5.4s
	uzp1 v2.4s, v4.4s, v5.4s
	shl v19.4s, v19.4s, #11
	orr v2.16b, v2.16b, v19.16b
	uzp2 v19.4s, v6.4s, v7.4s
	uzp1 v3.4s, v6.4s, v7.4s
	shl v19.4s, v19.4s, #11
	orr v3.16b, v3.16b, v19.16b
	ushr v19.2d, v0.2d, #32
	sli v0.2d, v19.2d, #22
	ushr v19.2d, v1.2d, #32
	sli v1.2d, v19.2d, #22
	ushr v19.2d, v2.2d, #32
	sli v2.2d, v19.2d, #22
	ushr v19.2d, v3.2d, #32
	sli v3.2d, v19.2d, #22
	ushr v23.2d, v0.2d, #20
	shl v19.2d, v0.2d, #44
	ext v19.16b, v19.16b, v19.16b, #8
	orr v0.16b, v0.16b, v19.16b
	mov v0.d[1], v23.d[1]
	ushr v23.2d, v1.2d, #20
	shl v19.2d, v1.2d, #44
	ext v19.16b, v19.16b, v19.16b, #8
	orr v1.16b, v1.16b, v19.16b
	mov v1.d[1], v23.d[1]
	ushr v23.2d, v2.2d, #20
	shl v19.2d, v2.2d, #44
	ext v19.16b, v19.16b, v19.16b, #8
	orr v2.16b, v2.16b, v19.16b
	mov v2.d[1], v23.d[1]
	ushr v23.2d, v3.2d, #20
	shl v19.2d, v3.2d, #44
	ext v19.16b, v19.16b, v19.16b, #8
	orr v3.16b, v3.16b, v19.16b
	mov v3.d[1], v23.d[1]
	tbl v4.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v20.16b
	tbl v5.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v21.16b
	tbl v6.16b, {v0.16b, v1.16b, v2.16b, v3.16b}, v22.16b
	str q4, [x2, #0]
	str q5, [x2, #16]
	umov x9, v6.d[0]
	str x9, [x2, #32]
	umov w9, v6.s[2]
	str w9, [x2, #40]
	add x0, x0, #128
	add x2, x2, #44
	sub x11, x11, #1
	cbnz x11, 22b
	b 21f
20:
	movz x9, #5040, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #65280, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #31, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x9, #256, lsl #0
	movk x9, #770, lsl #16
	movk x9, #2052, lsl #32
	movk x9, #2569, lsl #48
	dup v20.2d, x9
	movz x9, #3083, lsl #0
	movk x9, #4368, lsl #16
	movk x9, #4882, lsl #32
	movk x9, #6164, lsl #48
	mov v20.d[1], x9
	movz x9, #6681, lsl #0
	movk x9, #7195, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	dup v21.2d, x9
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v21.d[1], x9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
23:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
	ldr q4, [x0, #64]
	ldr q5, [x0, #80]
	ldr q6, [x0, #96]
	ldr q7, [x0, #112]
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #19
	and v0.16b, v0.16b, v18.16b
	mul v1.4s, v1.4s, v16.4s
	add v1.4s, v1.4s, v17.4s
	ushr v1.4s, v1.4s, #19
	and v1.16b, v1.16b, v18.16b
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #19
	and v2.16b, v2.16b, v18.16b
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #19
	and v3.16b, v3.16b, v18.16b
	mul v4.4s, v4.4s, v16.4s
	add v4.4s, v4.4s, v17.4s
	ushr v4.4s, v4.4s, #19
	and v4.16b, v4.16b, v18.16b
	mul v5.4s, v5.4s, v16.4s
	add v5.4s, v5.4s, v17.4s
	ushr v5.4s, v5.4s, #19
	and v5.16b, v5.16b, v18.16b
	mul v6.4s, v6.4s, v16.4s
	add v6.4s, v6.4s, v17.4s
	ushr v6.4s, v6.4s, #19
	and v6.16b, v6.16b, v18.16b
	mul v7.4s, v7.4s, v16.4s
	add v7.4s, v7.4s, v17.4s
	ushr v7.4s, v7.4s, #19
	and v7.16b, v7.16b, v18.16b
	uzp2 v19.4s, v0.4s, v1.4s
	uzp1 v0.4s, v0.4s, v1.4s
	shl v19.4s, v19.4s, #5
	orr v0.16b, v0.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v1.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #5
	orr v1.16b, v1.16b, v19.16b
	uzp2 v19.4s, v4.4s, v5.4s
	uzp1 v2.4s, v4.4s, v5.4s
	shl v19.4s, v19.4s, #5
	orr v2.16b, v2.16b, v19.16b
	uzp2 v19.4s, v6.4s, v7.4s
	uzp1 v3.4s, v6.4s, v7.4s
	shl v19.4s, v19.4s, #5
	orr v3.16b, v3.16b, v19.16b
	uzp2 v19.4s, v0.4s, v1.4s
	uzp1 v4.4s, v0.4s, v1.4s
	shl v19.4s, v19.4s, #10
	orr v4.16b, v4.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v5.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #10
	orr v5.16b, v5.16b, v19.16b
	ushr v19.2d, v4.2d, #32
	sli v4.2d, v19.2d, #20
	ushr v19.2d, v5.2d, #32
	sli v5.2d, v19.2d, #20
	tbl v6.16b, {v4.16b, v5.16b}, v20.16b
	tbl v7.16b, {v4.16b, v5.16b}, v21.16b
	str q6, [x2, #0]
	umov w9, v7.s[0]
	str w9, [x2, #16]
	add x0, x0, #128
	add x2, x2, #20
	sub x11, x11, #1
	cbnz x11, 23b
21:
	ret
	.p2align 6
