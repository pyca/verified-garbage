// The functions of `src/mlkem.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_add:
	movz x9, #3329, lsl #0
	dup v16.4s, w9
	movz x10, #64, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	add v2.4s, v0.4s, v1.4s
	sub v3.4s, v2.4s, v16.4s
	umin v2.4s, v2.4s, v3.4s
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6

vg_mlkem_sub:
	movz x9, #3329, lsl #0
	dup v16.4s, w9
	movz x10, #64, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x1, #0]
	sub v2.4s, v0.4s, v1.4s
	add v3.4s, v2.4s, v16.4s
	umin v2.4s, v2.4s, v3.4s
	str q2, [x0, #0]
	add x0, x0, #16
	add x1, x1, #16
	sub x10, x10, #1
	cbnz x10, 20b
	ret
	.p2align 6

vg_mlkem_encode12:
	movz x9, #256, lsl #0
	movk x9, #1026, lsl #16
	movk x9, #1541, lsl #32
	movk x9, #2312, lsl #48
	dup v16.2d, x9
	movz x9, #3082, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v16.d[1], x9
	movz x11, #32, lsl #0
20:
	ldr q0, [x0, #0]
	ldr q1, [x0, #16]
	uzp1 v2.4s, v0.4s, v1.4s
	uzp2 v3.4s, v0.4s, v1.4s
	shl v3.4s, v3.4s, #12
	orr v2.16b, v2.16b, v3.16b
	tbl v0.16b, {v2.16b}, v16.16b
	umov x9, v0.d[0]
	umov x10, v0.d[1]
	str x9, [x1, #0]
	str w10, [x1, #8]
	add x0, x0, #32
	add x1, x1, #12
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6

vg_mlkem_decode12:
	movz x9, #256, lsl #0
	movk x9, #65282, lsl #16
	movk x9, #1027, lsl #32
	movk x9, #65285, lsl #48
	dup v16.2d, x9
	movz x9, #1798, lsl #0
	movk x9, #65288, lsl #16
	movk x9, #2569, lsl #32
	movk x9, #65291, lsl #48
	mov v16.d[1], x9
	movz x9, #4095, lsl #0
	dup v17.4s, w9
	movz x9, #3329, lsl #0
	dup v18.4s, w9
	movz x11, #32, lsl #0
20:
	ldr x9, [x0, #0]
	ldr w10, [x0, #8]
	dup v0.2d, x9
	mov v0.d[1], x10
	tbl v1.16b, {v0.16b}, v16.16b
	and v2.16b, v1.16b, v17.16b
	ushr v3.4s, v1.4s, #12
	sub v4.4s, v2.4s, v18.4s
	umin v2.4s, v2.4s, v4.4s
	sub v4.4s, v3.4s, v18.4s
	umin v3.4s, v3.4s, v4.4s
	zip1 v0.4s, v2.4s, v3.4s
	zip2 v1.4s, v2.4s, v3.4s
	str q0, [x1, #0]
	str q1, [x1, #16]
	add x0, x0, #12
	add x1, x1, #32
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6

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

vg_mlkem_decode_decompress:
	sub x9, x1, #32
	cbz x9, 20f
	sub x9, x1, #128
	cbz x9, 22f
	movz x9, #3329, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #512, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #65535, lsl #0
	movk x9, #15, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x9, #1023, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v19.4s, w9
	movz x9, #256, lsl #0
	movk x9, #770, lsl #16
	movk x9, #65284, lsl #32
	movk x9, #65535, lsl #48
	dup v20.2d, x9
	movz x9, #1541, lsl #0
	movk x9, #2055, lsl #16
	movk x9, #65289, lsl #32
	movk x9, #65535, lsl #48
	mov v20.d[1], x9
	movz x9, #2826, lsl #0
	movk x9, #3340, lsl #16
	movk x9, #65294, lsl #32
	movk x9, #65535, lsl #48
	dup v21.2d, x9
	movz x9, #4111, lsl #0
	movk x9, #4625, lsl #16
	movk x9, #65299, lsl #32
	movk x9, #65535, lsl #48
	mov v21.d[1], x9
	movz x11, #16, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
24:
	ldr q4, [x0, #0]
	ldr w9, [x0, #16]
	mov v5.s[0], w9
	tbl v6.16b, {v4.16b, v5.16b}, v20.16b
	tbl v7.16b, {v4.16b, v5.16b}, v21.16b
	ushr v1.2d, v6.2d, #20
	trn1 v6.4s, v6.4s, v1.4s
	and v6.16b, v6.16b, v18.16b
	ushr v1.4s, v6.4s, #10
	and v6.16b, v6.16b, v19.16b
	zip1 v2.4s, v6.4s, v1.4s
	zip2 v3.4s, v6.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #10
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #10
	str q2, [x3, #0]
	str q3, [x3, #16]
	ushr v1.2d, v7.2d, #20
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #10
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #10
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #10
	str q2, [x3, #32]
	str q3, [x3, #48]
	add x0, x0, #20
	add x3, x3, #64
	sub x11, x11, #1
	cbnz x11, 24b
	b 23f
22:
	movz x9, #3329, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #8, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #15, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.16b, w9
	movi v19.2d, #0
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
25:
	ldr q0, [x0, #0]
	and v1.16b, v0.16b, v18.16b
	ushr v2.16b, v0.16b, #4
	zip1 v0.16b, v1.16b, v2.16b
	zip2 v1.16b, v1.16b, v2.16b
	zip1 v2.16b, v0.16b, v19.16b
	zip2 v3.16b, v0.16b, v19.16b
	zip1 v4.16b, v1.16b, v19.16b
	zip2 v5.16b, v1.16b, v19.16b
	zip1 v0.8h, v2.8h, v19.8h
	zip2 v1.8h, v2.8h, v19.8h
	zip1 v2.8h, v3.8h, v19.8h
	zip2 v3.8h, v3.8h, v19.8h
	zip1 v6.8h, v4.8h, v19.8h
	zip2 v7.8h, v4.8h, v19.8h
	zip1 v20.8h, v5.8h, v19.8h
	zip2 v21.8h, v5.8h, v19.8h
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #4
	mul v1.4s, v1.4s, v16.4s
	add v1.4s, v1.4s, v17.4s
	ushr v1.4s, v1.4s, #4
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #4
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #4
	mul v6.4s, v6.4s, v16.4s
	add v6.4s, v6.4s, v17.4s
	ushr v6.4s, v6.4s, #4
	mul v7.4s, v7.4s, v16.4s
	add v7.4s, v7.4s, v17.4s
	ushr v7.4s, v7.4s, #4
	mul v20.4s, v20.4s, v16.4s
	add v20.4s, v20.4s, v17.4s
	ushr v20.4s, v20.4s, #4
	mul v21.4s, v21.4s, v16.4s
	add v21.4s, v21.4s, v17.4s
	ushr v21.4s, v21.4s, #4
	str q0, [x3, #0]
	str q1, [x3, #16]
	str q2, [x3, #32]
	str q3, [x3, #48]
	str q6, [x3, #64]
	str q7, [x3, #80]
	str q20, [x3, #96]
	str q21, [x3, #112]
	add x0, x0, #16
	add x3, x3, #128
	sub x11, x11, #1
	cbnz x11, 25b
23:
	b 21f
20:
	movz x9, #3329, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #1, lsl #0
	movk x9, #0, lsl #16
	movk x9, #2, lsl #32
	movk x9, #0, lsl #48
	dup v18.2d, x9
	movz x9, #4, lsl #0
	movk x9, #0, lsl #16
	movk x9, #8, lsl #32
	movk x9, #0, lsl #48
	mov v18.d[1], x9
	movz x9, #16, lsl #0
	movk x9, #0, lsl #16
	movk x9, #32, lsl #32
	movk x9, #0, lsl #48
	dup v19.2d, x9
	movz x9, #64, lsl #0
	movk x9, #0, lsl #16
	movk x9, #128, lsl #32
	movk x9, #0, lsl #48
	mov v19.d[1], x9
	movz x9, #1665, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v20.4s, w9
	movi v21.2d, #0
	movz x11, #2, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
26:
	ldr q22, [x0, #0]
	dup v0.16b, v22.b[0]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #0]
	str q2, [x3, #16]
	dup v0.16b, v22.b[1]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #32]
	str q2, [x3, #48]
	dup v0.16b, v22.b[2]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #64]
	str q2, [x3, #80]
	dup v0.16b, v22.b[3]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #96]
	str q2, [x3, #112]
	dup v0.16b, v22.b[4]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #128]
	str q2, [x3, #144]
	dup v0.16b, v22.b[5]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #160]
	str q2, [x3, #176]
	dup v0.16b, v22.b[6]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #192]
	str q2, [x3, #208]
	dup v0.16b, v22.b[7]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #224]
	str q2, [x3, #240]
	dup v0.16b, v22.b[8]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #256]
	str q2, [x3, #272]
	dup v0.16b, v22.b[9]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #288]
	str q2, [x3, #304]
	dup v0.16b, v22.b[10]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #320]
	str q2, [x3, #336]
	dup v0.16b, v22.b[11]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #352]
	str q2, [x3, #368]
	dup v0.16b, v22.b[12]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #384]
	str q2, [x3, #400]
	dup v0.16b, v22.b[13]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #416]
	str q2, [x3, #432]
	dup v0.16b, v22.b[14]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #448]
	str q2, [x3, #464]
	dup v0.16b, v22.b[15]
	and v1.16b, v0.16b, v18.16b
	and v2.16b, v0.16b, v19.16b
	cmeq v1.4s, v1.4s, v21.4s
	cmeq v2.4s, v2.4s, v21.4s
	bic v1.16b, v20.16b, v1.16b
	bic v2.16b, v20.16b, v2.16b
	str q1, [x3, #480]
	str q2, [x3, #496]
	add x0, x0, #16
	add x3, x3, #512
	sub x11, x11, #1
	cbnz x11, 26b
21:
	ret
	.p2align 6

vg_mlkem_multiply_ntts:
	movz x9, #17, lsl #0
	str w9, [x3, #0]
	movz x9, #3312, lsl #0
	str w9, [x3, #4]
	movz x9, #2761, lsl #0
	str w9, [x3, #8]
	movz x9, #568, lsl #0
	str w9, [x3, #12]
	movz x9, #583, lsl #0
	str w9, [x3, #16]
	movz x9, #2746, lsl #0
	str w9, [x3, #20]
	movz x9, #2649, lsl #0
	str w9, [x3, #24]
	movz x9, #680, lsl #0
	str w9, [x3, #28]
	movz x9, #1637, lsl #0
	str w9, [x3, #32]
	movz x9, #1692, lsl #0
	str w9, [x3, #36]
	movz x9, #723, lsl #0
	str w9, [x3, #40]
	movz x9, #2606, lsl #0
	str w9, [x3, #44]
	movz x9, #2288, lsl #0
	str w9, [x3, #48]
	movz x9, #1041, lsl #0
	str w9, [x3, #52]
	movz x9, #1100, lsl #0
	str w9, [x3, #56]
	movz x9, #2229, lsl #0
	str w9, [x3, #60]
	movz x9, #1409, lsl #0
	str w9, [x3, #64]
	movz x9, #1920, lsl #0
	str w9, [x3, #68]
	movz x9, #2662, lsl #0
	str w9, [x3, #72]
	movz x9, #667, lsl #0
	str w9, [x3, #76]
	movz x9, #3281, lsl #0
	str w9, [x3, #80]
	movz x9, #48, lsl #0
	str w9, [x3, #84]
	movz x9, #233, lsl #0
	str w9, [x3, #88]
	movz x9, #3096, lsl #0
	str w9, [x3, #92]
	movz x9, #756, lsl #0
	str w9, [x3, #96]
	movz x9, #2573, lsl #0
	str w9, [x3, #100]
	movz x9, #2156, lsl #0
	str w9, [x3, #104]
	movz x9, #1173, lsl #0
	str w9, [x3, #108]
	movz x9, #3015, lsl #0
	str w9, [x3, #112]
	movz x9, #314, lsl #0
	str w9, [x3, #116]
	movz x9, #3050, lsl #0
	str w9, [x3, #120]
	movz x9, #279, lsl #0
	str w9, [x3, #124]
	movz x9, #1703, lsl #0
	str w9, [x3, #128]
	movz x9, #1626, lsl #0
	str w9, [x3, #132]
	movz x9, #1651, lsl #0
	str w9, [x3, #136]
	movz x9, #1678, lsl #0
	str w9, [x3, #140]
	movz x9, #2789, lsl #0
	str w9, [x3, #144]
	movz x9, #540, lsl #0
	str w9, [x3, #148]
	movz x9, #1789, lsl #0
	str w9, [x3, #152]
	movz x9, #1540, lsl #0
	str w9, [x3, #156]
	movz x9, #1847, lsl #0
	str w9, [x3, #160]
	movz x9, #1482, lsl #0
	str w9, [x3, #164]
	movz x9, #952, lsl #0
	str w9, [x3, #168]
	movz x9, #2377, lsl #0
	str w9, [x3, #172]
	movz x9, #1461, lsl #0
	str w9, [x3, #176]
	movz x9, #1868, lsl #0
	str w9, [x3, #180]
	movz x9, #2687, lsl #0
	str w9, [x3, #184]
	movz x9, #642, lsl #0
	str w9, [x3, #188]
	movz x9, #939, lsl #0
	str w9, [x3, #192]
	movz x9, #2390, lsl #0
	str w9, [x3, #196]
	movz x9, #2308, lsl #0
	str w9, [x3, #200]
	movz x9, #1021, lsl #0
	str w9, [x3, #204]
	movz x9, #2437, lsl #0
	str w9, [x3, #208]
	movz x9, #892, lsl #0
	str w9, [x3, #212]
	movz x9, #2388, lsl #0
	str w9, [x3, #216]
	movz x9, #941, lsl #0
	str w9, [x3, #220]
	movz x9, #733, lsl #0
	str w9, [x3, #224]
	movz x9, #2596, lsl #0
	str w9, [x3, #228]
	movz x9, #2337, lsl #0
	str w9, [x3, #232]
	movz x9, #992, lsl #0
	str w9, [x3, #236]
	movz x9, #268, lsl #0
	str w9, [x3, #240]
	movz x9, #3061, lsl #0
	str w9, [x3, #244]
	movz x9, #641, lsl #0
	str w9, [x3, #248]
	movz x9, #2688, lsl #0
	str w9, [x3, #252]
	movz x9, #1584, lsl #0
	str w9, [x3, #256]
	movz x9, #1745, lsl #0
	str w9, [x3, #260]
	movz x9, #2298, lsl #0
	str w9, [x3, #264]
	movz x9, #1031, lsl #0
	str w9, [x3, #268]
	movz x9, #2037, lsl #0
	str w9, [x3, #272]
	movz x9, #1292, lsl #0
	str w9, [x3, #276]
	movz x9, #3220, lsl #0
	str w9, [x3, #280]
	movz x9, #109, lsl #0
	str w9, [x3, #284]
	movz x9, #375, lsl #0
	str w9, [x3, #288]
	movz x9, #2954, lsl #0
	str w9, [x3, #292]
	movz x9, #2549, lsl #0
	str w9, [x3, #296]
	movz x9, #780, lsl #0
	str w9, [x3, #300]
	movz x9, #2090, lsl #0
	str w9, [x3, #304]
	movz x9, #1239, lsl #0
	str w9, [x3, #308]
	movz x9, #1645, lsl #0
	str w9, [x3, #312]
	movz x9, #1684, lsl #0
	str w9, [x3, #316]
	movz x9, #1063, lsl #0
	str w9, [x3, #320]
	movz x9, #2266, lsl #0
	str w9, [x3, #324]
	movz x9, #319, lsl #0
	str w9, [x3, #328]
	movz x9, #3010, lsl #0
	str w9, [x3, #332]
	movz x9, #2773, lsl #0
	str w9, [x3, #336]
	movz x9, #556, lsl #0
	str w9, [x3, #340]
	movz x9, #757, lsl #0
	str w9, [x3, #344]
	movz x9, #2572, lsl #0
	str w9, [x3, #348]
	movz x9, #2099, lsl #0
	str w9, [x3, #352]
	movz x9, #1230, lsl #0
	str w9, [x3, #356]
	movz x9, #561, lsl #0
	str w9, [x3, #360]
	movz x9, #2768, lsl #0
	str w9, [x3, #364]
	movz x9, #2466, lsl #0
	str w9, [x3, #368]
	movz x9, #863, lsl #0
	str w9, [x3, #372]
	movz x9, #2594, lsl #0
	str w9, [x3, #376]
	movz x9, #735, lsl #0
	str w9, [x3, #380]
	movz x9, #2804, lsl #0
	str w9, [x3, #384]
	movz x9, #525, lsl #0
	str w9, [x3, #388]
	movz x9, #1092, lsl #0
	str w9, [x3, #392]
	movz x9, #2237, lsl #0
	str w9, [x3, #396]
	movz x9, #403, lsl #0
	str w9, [x3, #400]
	movz x9, #2926, lsl #0
	str w9, [x3, #404]
	movz x9, #1026, lsl #0
	str w9, [x3, #408]
	movz x9, #2303, lsl #0
	str w9, [x3, #412]
	movz x9, #1143, lsl #0
	str w9, [x3, #416]
	movz x9, #2186, lsl #0
	str w9, [x3, #420]
	movz x9, #2150, lsl #0
	str w9, [x3, #424]
	movz x9, #1179, lsl #0
	str w9, [x3, #428]
	movz x9, #2775, lsl #0
	str w9, [x3, #432]
	movz x9, #554, lsl #0
	str w9, [x3, #436]
	movz x9, #886, lsl #0
	str w9, [x3, #440]
	movz x9, #2443, lsl #0
	str w9, [x3, #444]
	movz x9, #1722, lsl #0
	str w9, [x3, #448]
	movz x9, #1607, lsl #0
	str w9, [x3, #452]
	movz x9, #1212, lsl #0
	str w9, [x3, #456]
	movz x9, #2117, lsl #0
	str w9, [x3, #460]
	movz x9, #1874, lsl #0
	str w9, [x3, #464]
	movz x9, #1455, lsl #0
	str w9, [x3, #468]
	movz x9, #1029, lsl #0
	str w9, [x3, #472]
	movz x9, #2300, lsl #0
	str w9, [x3, #476]
	movz x9, #2110, lsl #0
	str w9, [x3, #480]
	movz x9, #1219, lsl #0
	str w9, [x3, #484]
	movz x9, #2935, lsl #0
	str w9, [x3, #488]
	movz x9, #394, lsl #0
	str w9, [x3, #492]
	movz x9, #885, lsl #0
	str w9, [x3, #496]
	movz x9, #2444, lsl #0
	str w9, [x3, #500]
	movz x9, #2154, lsl #0
	str w9, [x3, #504]
	movz x9, #1175, lsl #0
	str w9, [x3, #508]
	movz x9, #3329, lsl #0
	movz x10, #55259, lsl #0
	movk x10, #9, lsl #16
	movk x10, #0, lsl #32
	movk x10, #0, lsl #48
	dup v16.4s, w9
	dup v17.4s, w10
	movz x11, #32, lsl #0
20:
	ldr q0, [x1, #0]
	ldr q1, [x1, #16]
	ldr q4, [x2, #0]
	ldr q5, [x2, #16]
	ldr q18, [x3, #0]
	uzp1 v6.4s, v0.4s, v1.4s
	uzp2 v7.4s, v0.4s, v1.4s
	uzp1 v19.4s, v4.4s, v5.4s
	uzp2 v20.4s, v4.4s, v5.4s
	mul v21.4s, v7.4s, v20.4s
	sqdmulh v22.4s, v21.4s, v17.4s
	mls v21.4s, v22.4s, v16.4s
	mul v23.4s, v6.4s, v19.4s
	mla v23.4s, v21.4s, v18.4s
	sqdmulh v22.4s, v23.4s, v17.4s
	mls v23.4s, v22.4s, v16.4s
	sub v22.4s, v23.4s, v16.4s
	umin v23.4s, v23.4s, v22.4s
	mul v24.4s, v6.4s, v20.4s
	mla v24.4s, v7.4s, v19.4s
	sqdmulh v22.4s, v24.4s, v17.4s
	mls v24.4s, v22.4s, v16.4s
	sub v22.4s, v24.4s, v16.4s
	umin v24.4s, v24.4s, v22.4s
	zip1 v0.4s, v23.4s, v24.4s
	zip2 v1.4s, v23.4s, v24.4s
	str q0, [x0, #0]
	str q1, [x0, #16]
	add x0, x0, #32
	add x1, x1, #32
	add x2, x2, #32
	add x3, x3, #16
	sub x11, x11, #1
	cbnz x11, 20b
	ret
	.p2align 6

vg_mlkem_ntt:
	movz x9, #1062, lsl #0
	movk x9, #296, lsl #16
	movk x9, #2447, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #512]
	movz x9, #289, lsl #0
	movk x9, #331, lsl #16
	movk x9, #3253, lsl #32
	movk x9, #1756, lsl #48
	str x9, [x1, #520]
	movz x9, #10453, lsl #0
	movk x9, #2914, lsl #16
	movk x9, #24086, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #528]
	movz x9, #2845, lsl #0
	movk x9, #3258, lsl #16
	movk x9, #32020, lsl #32
	movk x9, #17285, lsl #48
	str x9, [x1, #536]
	movz x9, #17, lsl #0
	movk x9, #2761, lsl #16
	movk x9, #583, lsl #32
	movk x9, #2649, lsl #48
	str x9, [x1, #544]
	movz x9, #1637, lsl #0
	movk x9, #723, lsl #16
	movk x9, #2288, lsl #32
	movk x9, #1100, lsl #48
	str x9, [x1, #552]
	movz x9, #167, lsl #0
	movk x9, #27177, lsl #16
	movk x9, #5739, lsl #32
	movk x9, #26075, lsl #48
	str x9, [x1, #560]
	movz x9, #16113, lsl #0
	movk x9, #7117, lsl #16
	movk x9, #22521, lsl #32
	movk x9, #10828, lsl #48
	str x9, [x1, #568]
	movz x9, #1919, lsl #0
	movk x9, #1339, lsl #16
	movk x9, #1476, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #576]
	movz x9, #1197, lsl #0
	movk x9, #2304, lsl #16
	movk x9, #2277, lsl #32
	movk x9, #2055, lsl #48
	str x9, [x1, #584]
	movz x9, #18889, lsl #0
	movk x9, #13180, lsl #16
	movk x9, #14529, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #592]
	movz x9, #11782, lsl #0
	movk x9, #22679, lsl #16
	movk x9, #22413, lsl #32
	movk x9, #20228, lsl #48
	str x9, [x1, #600]
	movz x9, #1409, lsl #0
	movk x9, #2662, lsl #16
	movk x9, #3281, lsl #32
	movk x9, #233, lsl #48
	str x9, [x1, #608]
	movz x9, #756, lsl #0
	movk x9, #2156, lsl #16
	movk x9, #3015, lsl #32
	movk x9, #3050, lsl #48
	str x9, [x1, #616]
	movz x9, #13869, lsl #0
	movk x9, #26203, lsl #16
	movk x9, #32296, lsl #32
	movk x9, #2293, lsl #48
	str x9, [x1, #624]
	movz x9, #7441, lsl #0
	movk x9, #21222, lsl #16
	movk x9, #29677, lsl #32
	movk x9, #30022, lsl #48
	str x9, [x1, #632]
	movz x9, #193, lsl #0
	movk x9, #3046, lsl #16
	movk x9, #56, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #640]
	movz x9, #650, lsl #0
	movk x9, #1977, lsl #16
	movk x9, #2513, lsl #32
	movk x9, #632, lsl #48
	str x9, [x1, #648]
	movz x9, #1900, lsl #0
	movk x9, #29982, lsl #16
	movk x9, #551, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #656]
	movz x9, #6398, lsl #0
	movk x9, #19460, lsl #16
	movk x9, #24736, lsl #32
	movk x9, #6221, lsl #48
	str x9, [x1, #664]
	movz x9, #1703, lsl #0
	movk x9, #1651, lsl #16
	movk x9, #2789, lsl #32
	movk x9, #1789, lsl #48
	str x9, [x1, #672]
	movz x9, #1847, lsl #0
	movk x9, #952, lsl #16
	movk x9, #1461, lsl #32
	movk x9, #2687, lsl #48
	str x9, [x1, #680]
	movz x9, #16763, lsl #0
	movk x9, #16251, lsl #16
	movk x9, #27453, lsl #32
	movk x9, #17609, lsl #48
	str x9, [x1, #688]
	movz x9, #18180, lsl #0
	movk x9, #9371, lsl #16
	movk x9, #14381, lsl #32
	movk x9, #26449, lsl #48
	str x9, [x1, #696]
	movz x9, #797, lsl #0
	movk x9, #2240, lsl #16
	movk x9, #1333, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #704]
	movz x9, #2865, lsl #0
	movk x9, #33, lsl #16
	movk x9, #1320, lsl #32
	movk x9, #1915, lsl #48
	str x9, [x1, #712]
	movz x9, #7845, lsl #0
	movk x9, #22049, lsl #16
	movk x9, #13121, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #720]
	movz x9, #28201, lsl #0
	movk x9, #325, lsl #16
	movk x9, #12993, lsl #32
	movk x9, #18850, lsl #48
	str x9, [x1, #728]
	movz x9, #939, lsl #0
	movk x9, #2308, lsl #16
	movk x9, #2437, lsl #32
	movk x9, #2388, lsl #48
	str x9, [x1, #736]
	movz x9, #733, lsl #0
	movk x9, #2337, lsl #16
	movk x9, #268, lsl #32
	movk x9, #641, lsl #48
	str x9, [x1, #744]
	movz x9, #9243, lsl #0
	movk x9, #22718, lsl #16
	movk x9, #23988, lsl #32
	movk x9, #23506, lsl #48
	str x9, [x1, #752]
	movz x9, #7215, lsl #0
	movk x9, #23004, lsl #16
	movk x9, #2638, lsl #32
	movk x9, #6309, lsl #48
	str x9, [x1, #760]
	movz x9, #2786, lsl #0
	movk x9, #1426, lsl #16
	movk x9, #2094, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #768]
	movz x9, #2319, lsl #0
	movk x9, #1435, lsl #16
	movk x9, #807, lsl #32
	movk x9, #452, lsl #48
	str x9, [x1, #776]
	movz x9, #27423, lsl #0
	movk x9, #14036, lsl #16
	movk x9, #20612, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #784]
	movz x9, #22826, lsl #0
	movk x9, #14125, lsl #16
	movk x9, #7943, lsl #32
	movk x9, #4449, lsl #48
	str x9, [x1, #792]
	movz x9, #1584, lsl #0
	movk x9, #2298, lsl #16
	movk x9, #2037, lsl #32
	movk x9, #3220, lsl #48
	str x9, [x1, #800]
	movz x9, #375, lsl #0
	movk x9, #2549, lsl #16
	movk x9, #2090, lsl #32
	movk x9, #1645, lsl #48
	str x9, [x1, #808]
	movz x9, #15592, lsl #0
	movk x9, #22620, lsl #16
	movk x9, #20051, lsl #32
	movk x9, #31695, lsl #48
	str x9, [x1, #816]
	movz x9, #3691, lsl #0
	movk x9, #25090, lsl #16
	movk x9, #20572, lsl #32
	movk x9, #16192, lsl #48
	str x9, [x1, #824]
	movz x9, #3260, lsl #0
	movk x9, #535, lsl #16
	movk x9, #2882, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #832]
	movz x9, #1438, lsl #0
	movk x9, #2868, lsl #16
	movk x9, #1534, lsl #32
	movk x9, #2402, lsl #48
	str x9, [x1, #840]
	movz x9, #32089, lsl #0
	movk x9, #5266, lsl #16
	movk x9, #28368, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #848]
	movz x9, #14155, lsl #0
	movk x9, #28230, lsl #16
	movk x9, #15099, lsl #32
	movk x9, #23643, lsl #48
	str x9, [x1, #856]
	movz x9, #1063, lsl #0
	movk x9, #319, lsl #16
	movk x9, #2773, lsl #32
	movk x9, #757, lsl #48
	str x9, [x1, #864]
	movz x9, #2099, lsl #0
	movk x9, #561, lsl #16
	movk x9, #2466, lsl #32
	movk x9, #2594, lsl #48
	str x9, [x1, #872]
	movz x9, #10463, lsl #0
	movk x9, #3140, lsl #16
	movk x9, #27295, lsl #32
	movk x9, #7451, lsl #48
	str x9, [x1, #880]
	movz x9, #20661, lsl #0
	movk x9, #5522, lsl #16
	movk x9, #24273, lsl #32
	movk x9, #25533, lsl #48
	str x9, [x1, #888]
	movz x9, #569, lsl #0
	movk x9, #2393, lsl #16
	movk x9, #2879, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #896]
	movz x9, #2647, lsl #0
	movk x9, #2617, lsl #16
	movk x9, #1481, lsl #32
	movk x9, #648, lsl #48
	str x9, [x1, #904]
	movz x9, #5601, lsl #0
	movk x9, #23555, lsl #16
	movk x9, #28339, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #912]
	movz x9, #26055, lsl #0
	movk x9, #25760, lsl #16
	movk x9, #14578, lsl #32
	movk x9, #6378, lsl #48
	str x9, [x1, #920]
	movz x9, #2804, lsl #0
	movk x9, #1092, lsl #16
	movk x9, #403, lsl #32
	movk x9, #1026, lsl #48
	str x9, [x1, #928]
	movz x9, #1143, lsl #0
	movk x9, #2150, lsl #16
	movk x9, #2775, lsl #32
	movk x9, #886, lsl #48
	str x9, [x1, #936]
	movz x9, #27600, lsl #0
	movk x9, #10749, lsl #16
	movk x9, #3967, lsl #32
	movk x9, #10099, lsl #48
	str x9, [x1, #944]
	movz x9, #11251, lsl #0
	movk x9, #21163, lsl #16
	movk x9, #27315, lsl #32
	movk x9, #8721, lsl #48
	str x9, [x1, #952]
	movz x9, #1746, lsl #0
	movk x9, #1974, lsl #16
	movk x9, #821, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #960]
	movz x9, #2474, lsl #0
	movk x9, #3110, lsl #16
	movk x9, #1227, lsl #32
	movk x9, #910, lsl #48
	str x9, [x1, #968]
	movz x9, #17186, lsl #0
	movk x9, #19430, lsl #16
	movk x9, #8081, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #976]
	movz x9, #24352, lsl #0
	movk x9, #30612, lsl #16
	movk x9, #12078, lsl #32
	movk x9, #8957, lsl #48
	str x9, [x1, #984]
	movz x9, #1722, lsl #0
	movk x9, #1212, lsl #16
	movk x9, #1874, lsl #32
	movk x9, #1029, lsl #48
	str x9, [x1, #992]
	movz x9, #2110, lsl #0
	movk x9, #2935, lsl #16
	movk x9, #885, lsl #32
	movk x9, #2154, lsl #48
	str x9, [x1, #1000]
	movz x9, #16950, lsl #0
	movk x9, #11930, lsl #16
	movk x9, #18446, lsl #32
	movk x9, #10129, lsl #48
	str x9, [x1, #1008]
	movz x9, #20769, lsl #0
	movk x9, #28890, lsl #16
	movk x9, #8711, lsl #32
	movk x9, #21202, lsl #48
	str x9, [x1, #1016]
	movz x9, #3329, lsl #0
	dup v31.8h, w9
	movz x9, #10, lsl #0
	dup v30.8h, w9
	movi v29.2d, #0
	movz x9, #1729, lsl #0
	mov v18.h[0], w9
	movz x9, #17019, lsl #0
	mov v19.h[0], w9
	movz x9, #2580, lsl #0
	mov v18.h[1], w9
	movz x9, #25395, lsl #0
	mov v19.h[1], w9
	movz x9, #3289, lsl #0
	mov v18.h[2], w9
	movz x9, #32374, lsl #0
	mov v19.h[2], w9
	movz x9, #2642, lsl #0
	mov v18.h[3], w9
	movz x9, #26006, lsl #0
	mov v19.h[3], w9
	movz x9, #630, lsl #0
	mov v18.h[4], w9
	movz x9, #6201, lsl #0
	mov v19.h[4], w9
	movz x9, #1897, lsl #0
	mov v18.h[5], w9
	movz x9, #18673, lsl #0
	mov v19.h[5], w9
	movz x9, #848, lsl #0
	mov v18.h[6], w9
	movz x9, #8347, lsl #0
	mov v19.h[6], w9
	add x2, x0, #0
	add x3, x1, #0
	movz x5, #4, lsl #0
20:
	ldr q20, [x2, #0]
	ldr q21, [x2, #16]
	uzp1 v0.8h, v20.8h, v21.8h
	ldr q20, [x2, #128]
	ldr q21, [x2, #144]
	uzp1 v1.8h, v20.8h, v21.8h
	ldr q20, [x2, #256]
	ldr q21, [x2, #272]
	uzp1 v2.8h, v20.8h, v21.8h
	ldr q20, [x2, #384]
	ldr q21, [x2, #400]
	uzp1 v3.8h, v20.8h, v21.8h
	ldr q20, [x2, #512]
	ldr q21, [x2, #528]
	uzp1 v4.8h, v20.8h, v21.8h
	ldr q20, [x2, #640]
	ldr q21, [x2, #656]
	uzp1 v5.8h, v20.8h, v21.8h
	ldr q20, [x2, #768]
	ldr q21, [x2, #784]
	uzp1 v6.8h, v20.8h, v21.8h
	ldr q20, [x2, #896]
	ldr q21, [x2, #912]
	uzp1 v7.8h, v20.8h, v21.8h
	dup v22.8h, v18.h[0]
	dup v23.8h, v19.h[0]
	mul v16.8h, v4.8h, v22.8h
	sqrdmulh v17.8h, v4.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v4.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	mul v16.8h, v5.8h, v22.8h
	sqrdmulh v17.8h, v5.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v5.8h, v1.8h, v16.8h
	add v1.8h, v1.8h, v16.8h
	mul v16.8h, v6.8h, v22.8h
	sqrdmulh v17.8h, v6.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v6.8h, v2.8h, v16.8h
	add v2.8h, v2.8h, v16.8h
	mul v16.8h, v7.8h, v22.8h
	sqrdmulh v17.8h, v7.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v7.8h, v3.8h, v16.8h
	add v3.8h, v3.8h, v16.8h
	dup v22.8h, v18.h[1]
	dup v23.8h, v19.h[1]
	mul v16.8h, v2.8h, v22.8h
	sqrdmulh v17.8h, v2.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v2.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	mul v16.8h, v3.8h, v22.8h
	sqrdmulh v17.8h, v3.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v3.8h, v1.8h, v16.8h
	add v1.8h, v1.8h, v16.8h
	dup v22.8h, v18.h[2]
	dup v23.8h, v19.h[2]
	mul v16.8h, v6.8h, v22.8h
	sqrdmulh v17.8h, v6.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v6.8h, v4.8h, v16.8h
	add v4.8h, v4.8h, v16.8h
	mul v16.8h, v7.8h, v22.8h
	sqrdmulh v17.8h, v7.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v7.8h, v5.8h, v16.8h
	add v5.8h, v5.8h, v16.8h
	dup v22.8h, v18.h[3]
	dup v23.8h, v19.h[3]
	mul v16.8h, v1.8h, v22.8h
	sqrdmulh v17.8h, v1.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v1.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	dup v22.8h, v18.h[4]
	dup v23.8h, v19.h[4]
	mul v16.8h, v3.8h, v22.8h
	sqrdmulh v17.8h, v3.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v3.8h, v2.8h, v16.8h
	add v2.8h, v2.8h, v16.8h
	dup v22.8h, v18.h[5]
	dup v23.8h, v19.h[5]
	mul v16.8h, v5.8h, v22.8h
	sqrdmulh v17.8h, v5.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v5.8h, v4.8h, v16.8h
	add v4.8h, v4.8h, v16.8h
	dup v22.8h, v18.h[6]
	dup v23.8h, v19.h[6]
	mul v16.8h, v7.8h, v22.8h
	sqrdmulh v17.8h, v7.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sub v7.8h, v6.8h, v16.8h
	add v6.8h, v6.8h, v16.8h
	str q0, [x3, #0]
	str q1, [x3, #64]
	str q2, [x3, #128]
	str q3, [x3, #192]
	str q4, [x3, #256]
	str q5, [x3, #320]
	str q6, [x3, #384]
	str q7, [x3, #448]
	add x2, x2, #32
	add x3, x3, #16
	sub x5, x5, #1
	cbnz x5, 20b
	add x2, x1, #0
	add x6, x1, #512
	add x4, x0, #0
	movz x5, #8, lsl #0
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #16]
	ldr q2, [x2, #32]
	ldr q3, [x2, #48]
	ldr q20, [x6, #0]
	ldr q21, [x6, #16]
	ldr q22, [x6, #32]
	ldr q23, [x6, #48]
	dup v24.8h, v20.h[0]
	dup v25.8h, v21.h[0]
	mul v16.8h, v2.8h, v24.8h
	sqrdmulh v17.8h, v2.8h, v25.8h
	mls v16.8h, v17.8h, v31.8h
	sub v2.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	mul v16.8h, v3.8h, v24.8h
	sqrdmulh v17.8h, v3.8h, v25.8h
	mls v16.8h, v17.8h, v31.8h
	sub v3.8h, v1.8h, v16.8h
	add v1.8h, v1.8h, v16.8h
	dup v24.8h, v20.h[1]
	dup v25.8h, v21.h[1]
	mul v16.8h, v1.8h, v24.8h
	sqrdmulh v17.8h, v1.8h, v25.8h
	mls v16.8h, v17.8h, v31.8h
	sub v1.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	dup v24.8h, v20.h[2]
	dup v25.8h, v21.h[2]
	mul v16.8h, v3.8h, v24.8h
	sqrdmulh v17.8h, v3.8h, v25.8h
	mls v16.8h, v17.8h, v31.8h
	sub v3.8h, v2.8h, v16.8h
	add v2.8h, v2.8h, v16.8h
	zip2 v24.8h, v20.8h, v20.8h
	zip2 v25.8h, v21.8h, v21.8h
	zip1 v26.4s, v24.4s, v24.4s
	zip1 v27.4s, v25.4s, v25.4s
	zip1 v28.8h, v22.8h, v22.8h
	zip1 v19.8h, v23.8h, v23.8h
	trn1 v4.2d, v0.2d, v1.2d
	trn2 v5.2d, v0.2d, v1.2d
	mul v16.8h, v5.8h, v26.8h
	sqrdmulh v17.8h, v5.8h, v27.8h
	mls v16.8h, v17.8h, v31.8h
	sub v5.8h, v4.8h, v16.8h
	add v4.8h, v4.8h, v16.8h
	trn1 v0.4s, v4.4s, v5.4s
	trn2 v1.4s, v4.4s, v5.4s
	mul v16.8h, v1.8h, v28.8h
	sqrdmulh v17.8h, v1.8h, v19.8h
	mls v16.8h, v17.8h, v31.8h
	sub v1.8h, v0.8h, v16.8h
	add v0.8h, v0.8h, v16.8h
	trn1 v4.4s, v0.4s, v1.4s
	trn2 v5.4s, v0.4s, v1.4s
	trn1 v0.2d, v4.2d, v5.2d
	trn2 v1.2d, v4.2d, v5.2d
	zip2 v26.4s, v24.4s, v24.4s
	zip2 v27.4s, v25.4s, v25.4s
	zip2 v28.8h, v22.8h, v22.8h
	zip2 v19.8h, v23.8h, v23.8h
	trn1 v4.2d, v2.2d, v3.2d
	trn2 v5.2d, v2.2d, v3.2d
	mul v16.8h, v5.8h, v26.8h
	sqrdmulh v17.8h, v5.8h, v27.8h
	mls v16.8h, v17.8h, v31.8h
	sub v5.8h, v4.8h, v16.8h
	add v4.8h, v4.8h, v16.8h
	trn1 v2.4s, v4.4s, v5.4s
	trn2 v3.4s, v4.4s, v5.4s
	mul v16.8h, v3.8h, v28.8h
	sqrdmulh v17.8h, v3.8h, v19.8h
	mls v16.8h, v17.8h, v31.8h
	sub v3.8h, v2.8h, v16.8h
	add v2.8h, v2.8h, v16.8h
	trn1 v4.4s, v2.4s, v3.4s
	trn2 v5.4s, v2.4s, v3.4s
	trn1 v2.2d, v4.2d, v5.2d
	trn2 v3.2d, v4.2d, v5.2d
	sqrdmulh v16.8h, v0.8h, v30.8h
	mls v0.8h, v16.8h, v31.8h
	sshr v16.8h, v0.8h, #15
	and v16.16b, v16.16b, v31.16b
	add v0.8h, v0.8h, v16.8h
	sqrdmulh v16.8h, v1.8h, v30.8h
	mls v1.8h, v16.8h, v31.8h
	sshr v16.8h, v1.8h, #15
	and v16.16b, v16.16b, v31.16b
	add v1.8h, v1.8h, v16.8h
	sqrdmulh v16.8h, v2.8h, v30.8h
	mls v2.8h, v16.8h, v31.8h
	sshr v16.8h, v2.8h, #15
	and v16.16b, v16.16b, v31.16b
	add v2.8h, v2.8h, v16.8h
	sqrdmulh v16.8h, v3.8h, v30.8h
	mls v3.8h, v16.8h, v31.8h
	sshr v16.8h, v3.8h, #15
	and v16.16b, v16.16b, v31.16b
	add v3.8h, v3.8h, v16.8h
	zip1 v24.8h, v0.8h, v29.8h
	zip2 v25.8h, v0.8h, v29.8h
	str q24, [x4, #0]
	str q25, [x4, #16]
	zip1 v24.8h, v1.8h, v29.8h
	zip2 v25.8h, v1.8h, v29.8h
	str q24, [x4, #32]
	str q25, [x4, #48]
	zip1 v24.8h, v2.8h, v29.8h
	zip2 v25.8h, v2.8h, v29.8h
	str q24, [x4, #64]
	str q25, [x4, #80]
	zip1 v24.8h, v3.8h, v29.8h
	zip2 v25.8h, v3.8h, v29.8h
	str q24, [x4, #96]
	str q25, [x4, #112]
	add x2, x2, #64
	add x6, x6, #64
	add x4, x4, #128
	sub x5, x5, #1
	cbnz x5, 21b
	ret
	.p2align 6

vg_mlkem_inv_ntt:
	movz x9, #1746, lsl #0
	movk x9, #821, lsl #16
	movk x9, #1974, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #512]
	movz x9, #910, lsl #0
	movk x9, #1227, lsl #16
	movk x9, #3110, lsl #32
	movk x9, #2474, lsl #48
	str x9, [x1, #520]
	movz x9, #17186, lsl #0
	movk x9, #8081, lsl #16
	movk x9, #19430, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #528]
	movz x9, #8957, lsl #0
	movk x9, #12078, lsl #16
	movk x9, #30612, lsl #32
	movk x9, #24352, lsl #48
	str x9, [x1, #536]
	movz x9, #2154, lsl #0
	movk x9, #885, lsl #16
	movk x9, #2935, lsl #32
	movk x9, #2110, lsl #48
	str x9, [x1, #544]
	movz x9, #1029, lsl #0
	movk x9, #1874, lsl #16
	movk x9, #1212, lsl #32
	movk x9, #1722, lsl #48
	str x9, [x1, #552]
	movz x9, #21202, lsl #0
	movk x9, #8711, lsl #16
	movk x9, #28890, lsl #32
	movk x9, #20769, lsl #48
	str x9, [x1, #560]
	movz x9, #10129, lsl #0
	movk x9, #18446, lsl #16
	movk x9, #11930, lsl #32
	movk x9, #16950, lsl #48
	str x9, [x1, #568]
	movz x9, #569, lsl #0
	movk x9, #2879, lsl #16
	movk x9, #2393, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #576]
	movz x9, #648, lsl #0
	movk x9, #1481, lsl #16
	movk x9, #2617, lsl #32
	movk x9, #2647, lsl #48
	str x9, [x1, #584]
	movz x9, #5601, lsl #0
	movk x9, #28339, lsl #16
	movk x9, #23555, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #592]
	movz x9, #6378, lsl #0
	movk x9, #14578, lsl #16
	movk x9, #25760, lsl #32
	movk x9, #26055, lsl #48
	str x9, [x1, #600]
	movz x9, #886, lsl #0
	movk x9, #2775, lsl #16
	movk x9, #2150, lsl #32
	movk x9, #1143, lsl #48
	str x9, [x1, #608]
	movz x9, #1026, lsl #0
	movk x9, #403, lsl #16
	movk x9, #1092, lsl #32
	movk x9, #2804, lsl #48
	str x9, [x1, #616]
	movz x9, #8721, lsl #0
	movk x9, #27315, lsl #16
	movk x9, #21163, lsl #32
	movk x9, #11251, lsl #48
	str x9, [x1, #624]
	movz x9, #10099, lsl #0
	movk x9, #3967, lsl #16
	movk x9, #10749, lsl #32
	movk x9, #27600, lsl #48
	str x9, [x1, #632]
	movz x9, #3260, lsl #0
	movk x9, #2882, lsl #16
	movk x9, #535, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #640]
	movz x9, #2402, lsl #0
	movk x9, #1534, lsl #16
	movk x9, #2868, lsl #32
	movk x9, #1438, lsl #48
	str x9, [x1, #648]
	movz x9, #32089, lsl #0
	movk x9, #28368, lsl #16
	movk x9, #5266, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #656]
	movz x9, #23643, lsl #0
	movk x9, #15099, lsl #16
	movk x9, #28230, lsl #32
	movk x9, #14155, lsl #48
	str x9, [x1, #664]
	movz x9, #2594, lsl #0
	movk x9, #2466, lsl #16
	movk x9, #561, lsl #32
	movk x9, #2099, lsl #48
	str x9, [x1, #672]
	movz x9, #757, lsl #0
	movk x9, #2773, lsl #16
	movk x9, #319, lsl #32
	movk x9, #1063, lsl #48
	str x9, [x1, #680]
	movz x9, #25533, lsl #0
	movk x9, #24273, lsl #16
	movk x9, #5522, lsl #32
	movk x9, #20661, lsl #48
	str x9, [x1, #688]
	movz x9, #7451, lsl #0
	movk x9, #27295, lsl #16
	movk x9, #3140, lsl #32
	movk x9, #10463, lsl #48
	str x9, [x1, #696]
	movz x9, #2786, lsl #0
	movk x9, #2094, lsl #16
	movk x9, #1426, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #704]
	movz x9, #452, lsl #0
	movk x9, #807, lsl #16
	movk x9, #1435, lsl #32
	movk x9, #2319, lsl #48
	str x9, [x1, #712]
	movz x9, #27423, lsl #0
	movk x9, #20612, lsl #16
	movk x9, #14036, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #720]
	movz x9, #4449, lsl #0
	movk x9, #7943, lsl #16
	movk x9, #14125, lsl #32
	movk x9, #22826, lsl #48
	str x9, [x1, #728]
	movz x9, #1645, lsl #0
	movk x9, #2090, lsl #16
	movk x9, #2549, lsl #32
	movk x9, #375, lsl #48
	str x9, [x1, #736]
	movz x9, #3220, lsl #0
	movk x9, #2037, lsl #16
	movk x9, #2298, lsl #32
	movk x9, #1584, lsl #48
	str x9, [x1, #744]
	movz x9, #16192, lsl #0
	movk x9, #20572, lsl #16
	movk x9, #25090, lsl #32
	movk x9, #3691, lsl #48
	str x9, [x1, #752]
	movz x9, #31695, lsl #0
	movk x9, #20051, lsl #16
	movk x9, #22620, lsl #32
	movk x9, #15592, lsl #48
	str x9, [x1, #760]
	movz x9, #797, lsl #0
	movk x9, #1333, lsl #16
	movk x9, #2240, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #768]
	movz x9, #1915, lsl #0
	movk x9, #1320, lsl #16
	movk x9, #33, lsl #32
	movk x9, #2865, lsl #48
	str x9, [x1, #776]
	movz x9, #7845, lsl #0
	movk x9, #13121, lsl #16
	movk x9, #22049, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #784]
	movz x9, #18850, lsl #0
	movk x9, #12993, lsl #16
	movk x9, #325, lsl #32
	movk x9, #28201, lsl #48
	str x9, [x1, #792]
	movz x9, #641, lsl #0
	movk x9, #268, lsl #16
	movk x9, #2337, lsl #32
	movk x9, #733, lsl #48
	str x9, [x1, #800]
	movz x9, #2388, lsl #0
	movk x9, #2437, lsl #16
	movk x9, #2308, lsl #32
	movk x9, #939, lsl #48
	str x9, [x1, #808]
	movz x9, #6309, lsl #0
	movk x9, #2638, lsl #16
	movk x9, #23004, lsl #32
	movk x9, #7215, lsl #48
	str x9, [x1, #816]
	movz x9, #23506, lsl #0
	movk x9, #23988, lsl #16
	movk x9, #22718, lsl #32
	movk x9, #9243, lsl #48
	str x9, [x1, #824]
	movz x9, #193, lsl #0
	movk x9, #56, lsl #16
	movk x9, #3046, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #832]
	movz x9, #632, lsl #0
	movk x9, #2513, lsl #16
	movk x9, #1977, lsl #32
	movk x9, #650, lsl #48
	str x9, [x1, #840]
	movz x9, #1900, lsl #0
	movk x9, #551, lsl #16
	movk x9, #29982, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #848]
	movz x9, #6221, lsl #0
	movk x9, #24736, lsl #16
	movk x9, #19460, lsl #32
	movk x9, #6398, lsl #48
	str x9, [x1, #856]
	movz x9, #2687, lsl #0
	movk x9, #1461, lsl #16
	movk x9, #952, lsl #32
	movk x9, #1847, lsl #48
	str x9, [x1, #864]
	movz x9, #1789, lsl #0
	movk x9, #2789, lsl #16
	movk x9, #1651, lsl #32
	movk x9, #1703, lsl #48
	str x9, [x1, #872]
	movz x9, #26449, lsl #0
	movk x9, #14381, lsl #16
	movk x9, #9371, lsl #32
	movk x9, #18180, lsl #48
	str x9, [x1, #880]
	movz x9, #17609, lsl #0
	movk x9, #27453, lsl #16
	movk x9, #16251, lsl #32
	movk x9, #16763, lsl #48
	str x9, [x1, #888]
	movz x9, #1919, lsl #0
	movk x9, #1476, lsl #16
	movk x9, #1339, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #896]
	movz x9, #2055, lsl #0
	movk x9, #2277, lsl #16
	movk x9, #2304, lsl #32
	movk x9, #1197, lsl #48
	str x9, [x1, #904]
	movz x9, #18889, lsl #0
	movk x9, #14529, lsl #16
	movk x9, #13180, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #912]
	movz x9, #20228, lsl #0
	movk x9, #22413, lsl #16
	movk x9, #22679, lsl #32
	movk x9, #11782, lsl #48
	str x9, [x1, #920]
	movz x9, #3050, lsl #0
	movk x9, #3015, lsl #16
	movk x9, #2156, lsl #32
	movk x9, #756, lsl #48
	str x9, [x1, #928]
	movz x9, #233, lsl #0
	movk x9, #3281, lsl #16
	movk x9, #2662, lsl #32
	movk x9, #1409, lsl #48
	str x9, [x1, #936]
	movz x9, #30022, lsl #0
	movk x9, #29677, lsl #16
	movk x9, #21222, lsl #32
	movk x9, #7441, lsl #48
	str x9, [x1, #944]
	movz x9, #2293, lsl #0
	movk x9, #32296, lsl #16
	movk x9, #26203, lsl #32
	movk x9, #13869, lsl #48
	str x9, [x1, #952]
	movz x9, #1062, lsl #0
	movk x9, #2447, lsl #16
	movk x9, #296, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #960]
	movz x9, #1756, lsl #0
	movk x9, #3253, lsl #16
	movk x9, #331, lsl #32
	movk x9, #289, lsl #48
	str x9, [x1, #968]
	movz x9, #10453, lsl #0
	movk x9, #24086, lsl #16
	movk x9, #2914, lsl #32
	movk x9, #0, lsl #48
	str x9, [x1, #976]
	movz x9, #17285, lsl #0
	movk x9, #32020, lsl #16
	movk x9, #3258, lsl #32
	movk x9, #2845, lsl #48
	str x9, [x1, #984]
	movz x9, #1100, lsl #0
	movk x9, #2288, lsl #16
	movk x9, #723, lsl #32
	movk x9, #1637, lsl #48
	str x9, [x1, #992]
	movz x9, #2649, lsl #0
	movk x9, #583, lsl #16
	movk x9, #2761, lsl #32
	movk x9, #17, lsl #48
	str x9, [x1, #1000]
	movz x9, #10828, lsl #0
	movk x9, #22521, lsl #16
	movk x9, #7117, lsl #32
	movk x9, #16113, lsl #48
	str x9, [x1, #1008]
	movz x9, #26075, lsl #0
	movk x9, #5739, lsl #16
	movk x9, #27177, lsl #32
	movk x9, #167, lsl #48
	str x9, [x1, #1016]
	movz x9, #3329, lsl #0
	dup v31.8h, w9
	movz x9, #10, lsl #0
	dup v30.8h, w9
	movi v29.2d, #0
	add x2, x0, #0
	add x3, x1, #0
	add x6, x1, #512
	movz x5, #8, lsl #0
20:
	ldr q20, [x2, #0]
	ldr q21, [x2, #16]
	uzp1 v0.8h, v20.8h, v21.8h
	ldr q20, [x2, #32]
	ldr q21, [x2, #48]
	uzp1 v1.8h, v20.8h, v21.8h
	ldr q20, [x2, #64]
	ldr q21, [x2, #80]
	uzp1 v2.8h, v20.8h, v21.8h
	ldr q20, [x2, #96]
	ldr q21, [x2, #112]
	uzp1 v3.8h, v20.8h, v21.8h
	ldr q20, [x6, #0]
	ldr q21, [x6, #16]
	ldr q22, [x6, #32]
	ldr q23, [x6, #48]
	zip2 v24.8h, v20.8h, v20.8h
	zip2 v25.8h, v21.8h, v21.8h
	zip1 v28.8h, v22.8h, v22.8h
	zip1 v19.8h, v23.8h, v23.8h
	zip1 v26.4s, v24.4s, v24.4s
	zip1 v27.4s, v25.4s, v25.4s
	trn1 v4.2d, v0.2d, v1.2d
	trn2 v5.2d, v0.2d, v1.2d
	trn1 v0.4s, v4.4s, v5.4s
	trn2 v1.4s, v4.4s, v5.4s
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v28.8h
	sqrdmulh v17.8h, v17.8h, v19.8h
	mls v1.8h, v17.8h, v31.8h
	trn1 v4.4s, v0.4s, v1.4s
	trn2 v5.4s, v0.4s, v1.4s
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v26.8h
	sqrdmulh v17.8h, v17.8h, v27.8h
	mls v5.8h, v17.8h, v31.8h
	trn1 v0.2d, v4.2d, v5.2d
	trn2 v1.2d, v4.2d, v5.2d
	zip2 v28.8h, v22.8h, v22.8h
	zip2 v19.8h, v23.8h, v23.8h
	zip2 v26.4s, v24.4s, v24.4s
	zip2 v27.4s, v25.4s, v25.4s
	trn1 v4.2d, v2.2d, v3.2d
	trn2 v5.2d, v2.2d, v3.2d
	trn1 v2.4s, v4.4s, v5.4s
	trn2 v3.4s, v4.4s, v5.4s
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v28.8h
	sqrdmulh v17.8h, v17.8h, v19.8h
	mls v3.8h, v17.8h, v31.8h
	trn1 v4.4s, v2.4s, v3.4s
	trn2 v5.4s, v2.4s, v3.4s
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v26.8h
	sqrdmulh v17.8h, v17.8h, v27.8h
	mls v5.8h, v17.8h, v31.8h
	trn1 v2.2d, v4.2d, v5.2d
	trn2 v3.2d, v4.2d, v5.2d
	dup v24.8h, v20.h[1]
	dup v25.8h, v21.h[1]
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v1.8h, v17.8h, v31.8h
	dup v24.8h, v20.h[2]
	dup v25.8h, v21.h[2]
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v3.8h, v17.8h, v31.8h
	sqrdmulh v16.8h, v0.8h, v30.8h
	mls v0.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v1.8h, v30.8h
	mls v1.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v2.8h, v30.8h
	mls v2.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v3.8h, v30.8h
	mls v3.8h, v16.8h, v31.8h
	dup v24.8h, v20.h[0]
	dup v25.8h, v21.h[0]
	sub v17.8h, v2.8h, v0.8h
	add v0.8h, v0.8h, v2.8h
	mul v2.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v2.8h, v17.8h, v31.8h
	sub v17.8h, v3.8h, v1.8h
	add v1.8h, v1.8h, v3.8h
	mul v3.8h, v17.8h, v24.8h
	sqrdmulh v17.8h, v17.8h, v25.8h
	mls v3.8h, v17.8h, v31.8h
	str q0, [x3, #0]
	str q1, [x3, #16]
	str q2, [x3, #32]
	str q3, [x3, #48]
	add x2, x2, #128
	add x3, x3, #64
	add x6, x6, #64
	sub x5, x5, #1
	cbnz x5, 20b
	movz x9, #848, lsl #0
	mov v18.h[0], w9
	movz x9, #8347, lsl #0
	mov v19.h[0], w9
	movz x9, #1897, lsl #0
	mov v18.h[1], w9
	movz x9, #18673, lsl #0
	mov v19.h[1], w9
	movz x9, #630, lsl #0
	mov v18.h[2], w9
	movz x9, #6201, lsl #0
	mov v19.h[2], w9
	movz x9, #2642, lsl #0
	mov v18.h[3], w9
	movz x9, #26006, lsl #0
	mov v19.h[3], w9
	movz x9, #3289, lsl #0
	mov v18.h[4], w9
	movz x9, #32374, lsl #0
	mov v19.h[4], w9
	movz x9, #2580, lsl #0
	mov v18.h[5], w9
	movz x9, #25395, lsl #0
	mov v19.h[5], w9
	movz x9, #1729, lsl #0
	mov v18.h[6], w9
	movz x9, #17019, lsl #0
	mov v19.h[6], w9
	movz x9, #3303, lsl #0
	mov v18.h[7], w9
	movz x9, #32512, lsl #0
	mov v19.h[7], w9
	add x2, x1, #0
	add x3, x0, #0
	movz x5, #4, lsl #0
21:
	ldr q0, [x2, #0]
	ldr q1, [x2, #64]
	ldr q2, [x2, #128]
	ldr q3, [x2, #192]
	ldr q4, [x2, #256]
	ldr q5, [x2, #320]
	ldr q6, [x2, #384]
	ldr q7, [x2, #448]
	dup v22.8h, v18.h[0]
	dup v23.8h, v19.h[0]
	sub v17.8h, v1.8h, v0.8h
	add v0.8h, v0.8h, v1.8h
	mul v1.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v1.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[1]
	dup v23.8h, v19.h[1]
	sub v17.8h, v3.8h, v2.8h
	add v2.8h, v2.8h, v3.8h
	mul v3.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v3.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[2]
	dup v23.8h, v19.h[2]
	sub v17.8h, v5.8h, v4.8h
	add v4.8h, v4.8h, v5.8h
	mul v5.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v5.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[3]
	dup v23.8h, v19.h[3]
	sub v17.8h, v7.8h, v6.8h
	add v6.8h, v6.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[4]
	dup v23.8h, v19.h[4]
	sub v17.8h, v2.8h, v0.8h
	add v0.8h, v0.8h, v2.8h
	mul v2.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v2.8h, v17.8h, v31.8h
	sub v17.8h, v3.8h, v1.8h
	add v1.8h, v1.8h, v3.8h
	mul v3.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v3.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[5]
	dup v23.8h, v19.h[5]
	sub v17.8h, v6.8h, v4.8h
	add v4.8h, v4.8h, v6.8h
	mul v6.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v6.8h, v17.8h, v31.8h
	sub v17.8h, v7.8h, v5.8h
	add v5.8h, v5.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	sqrdmulh v16.8h, v0.8h, v30.8h
	mls v0.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v1.8h, v30.8h
	mls v1.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v2.8h, v30.8h
	mls v2.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v3.8h, v30.8h
	mls v3.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v4.8h, v30.8h
	mls v4.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v5.8h, v30.8h
	mls v5.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v6.8h, v30.8h
	mls v6.8h, v16.8h, v31.8h
	sqrdmulh v16.8h, v7.8h, v30.8h
	mls v7.8h, v16.8h, v31.8h
	dup v22.8h, v18.h[6]
	dup v23.8h, v19.h[6]
	sub v17.8h, v4.8h, v0.8h
	add v0.8h, v0.8h, v4.8h
	mul v4.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v4.8h, v17.8h, v31.8h
	sub v17.8h, v5.8h, v1.8h
	add v1.8h, v1.8h, v5.8h
	mul v5.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v5.8h, v17.8h, v31.8h
	sub v17.8h, v6.8h, v2.8h
	add v2.8h, v2.8h, v6.8h
	mul v6.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v6.8h, v17.8h, v31.8h
	sub v17.8h, v7.8h, v3.8h
	add v3.8h, v3.8h, v7.8h
	mul v7.8h, v17.8h, v22.8h
	sqrdmulh v17.8h, v17.8h, v23.8h
	mls v7.8h, v17.8h, v31.8h
	dup v22.8h, v18.h[7]
	dup v23.8h, v19.h[7]
	mul v16.8h, v0.8h, v22.8h
	sqrdmulh v17.8h, v0.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #0]
	str q25, [x3, #16]
	mul v16.8h, v1.8h, v22.8h
	sqrdmulh v17.8h, v1.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #128]
	str q25, [x3, #144]
	mul v16.8h, v2.8h, v22.8h
	sqrdmulh v17.8h, v2.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #256]
	str q25, [x3, #272]
	mul v16.8h, v3.8h, v22.8h
	sqrdmulh v17.8h, v3.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #384]
	str q25, [x3, #400]
	mul v16.8h, v4.8h, v22.8h
	sqrdmulh v17.8h, v4.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #512]
	str q25, [x3, #528]
	mul v16.8h, v5.8h, v22.8h
	sqrdmulh v17.8h, v5.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #640]
	str q25, [x3, #656]
	mul v16.8h, v6.8h, v22.8h
	sqrdmulh v17.8h, v6.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #768]
	str q25, [x3, #784]
	mul v16.8h, v7.8h, v22.8h
	sqrdmulh v17.8h, v7.8h, v23.8h
	mls v16.8h, v17.8h, v31.8h
	sshr v17.8h, v16.8h, #15
	and v17.16b, v17.16b, v31.16b
	add v16.8h, v16.8h, v17.8h
	zip1 v24.8h, v16.8h, v29.8h
	zip2 v25.8h, v16.8h, v29.8h
	str q24, [x3, #896]
	str q25, [x3, #912]
	add x2, x2, #16
	add x3, x3, #32
	sub x5, x5, #1
	cbnz x5, 21b
	ret
	.p2align 6

vg_mlkem_sample_ntt:
	str x25, [x2, #1680]
	str x26, [x2, #1688]
	str x30, [x2, #1696]
	str x24, [x2, #1704]
	add x24, x0, #0
	add x25, x1, #0
	add x26, x2, #0
	movz x9, #0, lsl #0
	str x9, [x2, #840]
	str x9, [x2, #848]
	str x9, [x2, #856]
	str x9, [x2, #864]
	str x9, [x2, #872]
	str x9, [x2, #880]
	str x9, [x2, #888]
	str x9, [x2, #896]
	str x9, [x2, #904]
	str x9, [x2, #912]
	str x9, [x2, #920]
	str x9, [x2, #928]
	str x9, [x2, #936]
	str x9, [x2, #944]
	str x9, [x2, #952]
	str x9, [x2, #960]
	str x9, [x2, #968]
	str x9, [x2, #976]
	str x9, [x2, #984]
	str x9, [x2, #992]
	str x9, [x2, #1000]
	str x9, [x2, #1008]
	str x9, [x2, #1016]
	str x9, [x2, #1024]
	str x9, [x2, #1032]
	add x3, x0, #0
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	movz x4, #34, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_absorb_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #34, lsl #0
	movz x3, #31, lsl #0
	add x4, x26, #1040
	bl {vg_keccak_pad_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x26, #0
	movz x4, #504, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x25, #0
	movz x4, #256, lsl #0
20:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 20b
	add x2, x26, #0
	add x3, x25, #0
	movz x4, #256, lsl #0
	movz x5, #168, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
21:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 22f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 24f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 25f
24:
25:
	b 23f
22:
23:
	cbnz x5, 21b
	cbz x4, 26f
	add x0, x24, #0
	add x1, x25, #0
	add x2, x26, #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
	str x25, [x2, #1680]
	str x26, [x2, #1688]
	str x30, [x2, #1696]
	str x24, [x2, #1704]
	add x24, x0, #0
	add x25, x1, #0
	add x26, x2, #0
	movz x9, #0, lsl #0
	str x9, [x2, #840]
	str x9, [x2, #848]
	str x9, [x2, #856]
	str x9, [x2, #864]
	str x9, [x2, #872]
	str x9, [x2, #880]
	str x9, [x2, #888]
	str x9, [x2, #896]
	str x9, [x2, #904]
	str x9, [x2, #912]
	str x9, [x2, #920]
	str x9, [x2, #928]
	str x9, [x2, #936]
	str x9, [x2, #944]
	str x9, [x2, #952]
	str x9, [x2, #960]
	str x9, [x2, #968]
	str x9, [x2, #976]
	str x9, [x2, #984]
	str x9, [x2, #992]
	str x9, [x2, #1000]
	str x9, [x2, #1008]
	str x9, [x2, #1016]
	str x9, [x2, #1024]
	str x9, [x2, #1032]
	add x3, x0, #0
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	movz x4, #34, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_absorb_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #34, lsl #0
	movz x3, #31, lsl #0
	add x4, x26, #1040
	bl {vg_keccak_pad_scratch}
	add x0, x26, #840
	movz x1, #168, lsl #0
	movz x2, #0, lsl #0
	add x3, x26, #0
	movz x4, #840, lsl #0
	add x5, x26, #1040
	bl {vg_keccak_squeeze_scratch}
	movz x9, #0, lsl #0
	add x3, x25, #0
	movz x4, #256, lsl #0
28:
	str w9, [x3, #0]
	add x3, x3, #4
	sub x4, x4, #1
	cbnz x4, 28b
	add x2, x26, #0
	add x3, x25, #0
	movz x4, #256, lsl #0
	movz x5, #280, lsl #0
	movz x9, #3329, lsl #0
	movz x10, #15, lsl #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
29:
	ldrb w6, [x2, #0]
	ldrb w7, [x2, #1]
	ldrb w8, [x2, #2]
	add x2, x2, #3
	sub x5, x5, #1
	and x11, x7, x10
	lsl x11, x11, #8
	add x11, x11, x6
	lsr x12, x7, #4
	lsl x13, x8, #4
	add x12, x12, x13
	cbz x4, 210f
	sub x13, x11, x9
	lsr x14, x13, #63
	str w11, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	cbz x4, 212f
	sub x13, x12, x9
	lsr x14, x13, #63
	str w12, [x3, #0]
	lsl x15, x14, #2
	add x3, x3, x15
	sub x4, x4, x14
	b 213f
212:
213:
	b 211f
210:
211:
	cbnz x5, 29b
	cbz x4, 214f
	movz x13, #0, lsl #0
	str w13, [x3, #0]
	b 215f
214:
215:
	sub x0, x4, #1
	lsr x0, x0, #63
	b 27f
26:
	movz x0, #1, lsl #0
	ldr x30, [x26, #1696]
	ldr x24, [x26, #1704]
	ldr x25, [x26, #1680]
	ldr x26, [x26, #1688]
27:
	ret
	.p2align 6
