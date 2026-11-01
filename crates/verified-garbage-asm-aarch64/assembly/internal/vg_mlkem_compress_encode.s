// The functions of `src/internal/vg_mlkem_compress_encode.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_compress_encode:
	sub x9, x3, #32
	cbz x9, 20f
	sub x9, x3, #128
	cbz x9, 22f
	movz x9, #30199, lsl #0
	movk x9, #2, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #65472, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #1023, lsl #0
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
	movz x11, #16, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
24:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	ldr q2, [x0, #32]
	ldr q3, [x0, #48]
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
	add x0, x0, #64
	add x2, x2, #20
	sub x11, x11, #1
	cbnz x11, 24b
	b 23f
22:
	movz x9, #2520, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #65472, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #15, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
25:
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
	shl v19.4s, v19.4s, #4
	orr v0.16b, v0.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v1.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #4
	orr v1.16b, v1.16b, v19.16b
	uzp2 v19.4s, v4.4s, v5.4s
	uzp1 v2.4s, v4.4s, v5.4s
	shl v19.4s, v19.4s, #4
	orr v2.16b, v2.16b, v19.16b
	uzp2 v19.4s, v6.4s, v7.4s
	uzp1 v3.4s, v6.4s, v7.4s
	shl v19.4s, v19.4s, #4
	orr v3.16b, v3.16b, v19.16b
	uzp1 v0.8h, v0.8h, v1.8h
	uzp1 v2.8h, v2.8h, v3.8h
	uzp1 v0.16b, v0.16b, v2.16b
	str q0, [x2, #0]
	add x0, x0, #128
	add x2, x2, #16
	sub x11, x11, #1
	cbnz x11, 25b
23:
	b 21f
20:
	movz x9, #315, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #65472, lsl #0
	movk x9, #3, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
26:
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
	shl v19.4s, v19.4s, #1
	orr v0.16b, v0.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v1.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #1
	orr v1.16b, v1.16b, v19.16b
	uzp2 v19.4s, v4.4s, v5.4s
	uzp1 v2.4s, v4.4s, v5.4s
	shl v19.4s, v19.4s, #1
	orr v2.16b, v2.16b, v19.16b
	uzp2 v19.4s, v6.4s, v7.4s
	uzp1 v3.4s, v6.4s, v7.4s
	shl v19.4s, v19.4s, #1
	orr v3.16b, v3.16b, v19.16b
	uzp2 v19.4s, v0.4s, v1.4s
	uzp1 v0.4s, v0.4s, v1.4s
	shl v19.4s, v19.4s, #2
	orr v0.16b, v0.16b, v19.16b
	uzp2 v19.4s, v2.4s, v3.4s
	uzp1 v1.4s, v2.4s, v3.4s
	shl v19.4s, v19.4s, #2
	orr v1.16b, v1.16b, v19.16b
	uzp2 v19.4s, v0.4s, v1.4s
	uzp1 v0.4s, v0.4s, v1.4s
	shl v19.4s, v19.4s, #4
	orr v0.16b, v0.16b, v19.16b
	uzp1 v0.8h, v0.8h, v0.8h
	uzp1 v0.16b, v0.16b, v0.16b
	umov w9, v0.s[0]
	str w9, [x2, #0]
	add x0, x0, #128
	add x2, x2, #4
	sub x11, x11, #1
	cbnz x11, 26b
21:
	ret
	.p2align 6
