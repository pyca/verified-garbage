// The functions of `src/internal/vg_mlkem_decode_decompress.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

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
