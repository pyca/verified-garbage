// The functions of `src/internal/vg_mlkem1024_decode_decompress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem1024_decode_decompress:
	sub x9, x1, #160
	cbz x9, 20f
	movz x9, #3329, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #1024, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v17.4s, w9
	movz x9, #65535, lsl #0
	movk x9, #63, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v18.4s, w9
	movz x9, #2047, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v19.4s, w9
	movz x9, #256, lsl #0
	movk x9, #770, lsl #16
	movk x9, #1284, lsl #32
	movk x9, #1798, lsl #48
	dup v20.2d, x9
	movz x9, #2312, lsl #0
	movk x9, #65290, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v20.d[1], x9
	movz x9, #3083, lsl #0
	movk x9, #3597, lsl #16
	movk x9, #4111, lsl #32
	movk x9, #4625, lsl #48
	dup v21.2d, x9
	movz x9, #5139, lsl #0
	movk x9, #65301, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v21.d[1], x9
	movz x9, #5910, lsl #0
	movk x9, #6424, lsl #16
	movk x9, #6938, lsl #32
	movk x9, #7452, lsl #48
	dup v22.2d, x9
	movz x9, #7966, lsl #0
	movk x9, #65312, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v22.d[1], x9
	movz x9, #8737, lsl #0
	movk x9, #9251, lsl #16
	movk x9, #9765, lsl #32
	movk x9, #10279, lsl #48
	dup v23.2d, x9
	movz x9, #10793, lsl #0
	movk x9, #65323, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #65535, lsl #48
	mov v23.d[1], x9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
22:
	ldr q4, [x0, #0]
	ldr q5, [x0, #16]
	ldr x9, [x0, #32]
	mov v6.d[0], x9
	ldr w9, [x0, #40]
	mov v6.s[2], w9
	tbl v7.16b, {v4.16b, v5.16b, v6.16b}, v20.16b
	ushr v1.2d, v7.2d, #44
	shl v2.2d, v7.2d, #20
	ext v2.16b, v2.16b, v2.16b, #8
	orr v1.16b, v1.16b, v2.16b
	zip1 v7.2d, v7.2d, v1.2d
	ushr v1.2d, v7.2d, #22
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #11
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #11
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #11
	str q2, [x3, #0]
	str q3, [x3, #16]
	tbl v7.16b, {v4.16b, v5.16b, v6.16b}, v21.16b
	ushr v1.2d, v7.2d, #44
	shl v2.2d, v7.2d, #20
	ext v2.16b, v2.16b, v2.16b, #8
	orr v1.16b, v1.16b, v2.16b
	zip1 v7.2d, v7.2d, v1.2d
	ushr v1.2d, v7.2d, #22
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #11
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #11
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #11
	str q2, [x3, #32]
	str q3, [x3, #48]
	tbl v7.16b, {v4.16b, v5.16b, v6.16b}, v22.16b
	ushr v1.2d, v7.2d, #44
	shl v2.2d, v7.2d, #20
	ext v2.16b, v2.16b, v2.16b, #8
	orr v1.16b, v1.16b, v2.16b
	zip1 v7.2d, v7.2d, v1.2d
	ushr v1.2d, v7.2d, #22
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #11
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #11
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #11
	str q2, [x3, #64]
	str q3, [x3, #80]
	tbl v7.16b, {v4.16b, v5.16b, v6.16b}, v23.16b
	ushr v1.2d, v7.2d, #44
	shl v2.2d, v7.2d, #20
	ext v2.16b, v2.16b, v2.16b, #8
	orr v1.16b, v1.16b, v2.16b
	zip1 v7.2d, v7.2d, v1.2d
	ushr v1.2d, v7.2d, #22
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #11
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #11
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #11
	str q2, [x3, #96]
	str q3, [x3, #112]
	add x0, x0, #44
	add x3, x3, #128
	sub x11, x11, #1
	cbnz x11, 22b
	b 21f
20:
	movz x9, #3329, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v16.4s, w9
	movz x9, #16, lsl #0
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
	movz x9, #31, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	dup v22.4s, w9
	movz x11, #8, lsl #0
	movk x11, #0, lsl #16
	movk x11, #0, lsl #32
	movk x11, #0, lsl #48
23:
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
	ushr v1.4s, v2.4s, #5
	and v2.16b, v2.16b, v22.16b
	zip1 v0.4s, v2.4s, v1.4s
	zip2 v2.4s, v2.4s, v1.4s
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #5
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #5
	str q0, [x3, #0]
	str q2, [x3, #16]
	ushr v1.4s, v3.4s, #5
	and v3.16b, v3.16b, v22.16b
	zip1 v0.4s, v3.4s, v1.4s
	zip2 v3.4s, v3.4s, v1.4s
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #5
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #5
	str q0, [x3, #32]
	str q3, [x3, #48]
	ushr v1.2d, v7.2d, #20
	trn1 v7.4s, v7.4s, v1.4s
	and v7.16b, v7.16b, v18.16b
	ushr v1.4s, v7.4s, #10
	and v7.16b, v7.16b, v19.16b
	zip1 v2.4s, v7.4s, v1.4s
	zip2 v3.4s, v7.4s, v1.4s
	ushr v1.4s, v2.4s, #5
	and v2.16b, v2.16b, v22.16b
	zip1 v0.4s, v2.4s, v1.4s
	zip2 v2.4s, v2.4s, v1.4s
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #5
	mul v2.4s, v2.4s, v16.4s
	add v2.4s, v2.4s, v17.4s
	ushr v2.4s, v2.4s, #5
	str q0, [x3, #64]
	str q2, [x3, #80]
	ushr v1.4s, v3.4s, #5
	and v3.16b, v3.16b, v22.16b
	zip1 v0.4s, v3.4s, v1.4s
	zip2 v3.4s, v3.4s, v1.4s
	mul v0.4s, v0.4s, v16.4s
	add v0.4s, v0.4s, v17.4s
	ushr v0.4s, v0.4s, #5
	mul v3.4s, v3.4s, v16.4s
	add v3.4s, v3.4s, v17.4s
	ushr v3.4s, v3.4s, #5
	str q0, [x3, #96]
	str q3, [x3, #112]
	add x0, x0, #20
	add x3, x3, #128
	sub x11, x11, #1
	cbnz x11, 23b
21:
	ret
	.p2align 6
