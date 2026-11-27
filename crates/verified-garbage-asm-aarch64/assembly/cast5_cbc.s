// The functions of `src/cast5_cbc.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_cbc_encrypt_chained:
	sub sp, sp, #112
	add x5, sp, #0
	add x5, x5, #0
	str x19, [x5, #8]
	str x20, [x5, #16]
	str x21, [x5, #24]
	str x22, [x5, #32]
	str x23, [x5, #40]
	str x24, [x5, #48]
	str x25, [x5, #56]
	str x26, [x5, #64]
	str x27, [x5, #72]
	str x28, [x5, #80]
	add x25, x2, #0
	cbz x4, 20f
	ldr x6, [x3, #0]
	ldr x7, [x2, #0]
	eor x6, x6, x7
	str x6, [x3, #0]
	b 21f
20:
21:
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 22f
24:
	ldr x6, [x23, #0]
	str x6, [x5, #0]
	add x16, x5, #0
	add x2, x5, #0
	ldr w5, [x2, #0]
	rev w5, w5
	ldr w6, [x2, #4]
	rev w6, w6
	add x12, x0, #0
	lsr x7, x1, #2
	add x7, x7, #1
	sub x8, x1, #16
25:
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
	and v4.16b, v0.16b, v3.16b
	movi v16.2d, #0
	sub v16.4s, v16.4s, v4.4s
	ushr v4.4s, v0.4s, #1
	and v4.16b, v4.16b, v3.16b
	movi v17.2d, #0
	sub v17.4s, v17.4s, v4.4s
	ushr v18.4s, v0.4s, #2
26:
	ldr q4, [x10, #0]
	ldr q5, [x10, #16]
	bit v4.16b, v5.16b, v16.16b
	ldr q19, [x10, #32]
	ldr q5, [x10, #48]
	bit v19.16b, v5.16b, v16.16b
	bit v4.16b, v19.16b, v17.16b
	cmeq v5.4s, v18.4s, v2.4s
	and v4.16b, v4.16b, v5.16b
	orr v1.16b, v1.16b, v4.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 26b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	ldr w9, [x12, #0]
	eor w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
	and v4.16b, v0.16b, v3.16b
	movi v16.2d, #0
	sub v16.4s, v16.4s, v4.4s
	ushr v4.4s, v0.4s, #1
	and v4.16b, v4.16b, v3.16b
	movi v17.2d, #0
	sub v17.4s, v17.4s, v4.4s
	ushr v18.4s, v0.4s, #2
27:
	ldr q4, [x10, #0]
	ldr q5, [x10, #16]
	bit v4.16b, v5.16b, v16.16b
	ldr q19, [x10, #32]
	ldr q5, [x10, #48]
	bit v19.16b, v5.16b, v16.16b
	bit v4.16b, v19.16b, v17.16b
	cmeq v5.4s, v18.4s, v2.4s
	and v4.16b, v4.16b, v5.16b
	orr v1.16b, v1.16b, v4.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 27b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	sub w4, w9, w14
	add w4, w4, w15
	eor w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	ldr w9, [x12, #0]
	sub w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
	and v4.16b, v0.16b, v3.16b
	movi v16.2d, #0
	sub v16.4s, v16.4s, v4.4s
	ushr v4.4s, v0.4s, #1
	and v4.16b, v4.16b, v3.16b
	movi v17.2d, #0
	sub v17.4s, v17.4s, v4.4s
	ushr v18.4s, v0.4s, #2
28:
	ldr q4, [x10, #0]
	ldr q5, [x10, #16]
	bit v4.16b, v5.16b, v16.16b
	ldr q19, [x10, #32]
	ldr q5, [x10, #48]
	bit v19.16b, v5.16b, v16.16b
	bit v4.16b, v19.16b, v17.16b
	cmeq v5.4s, v18.4s, v2.4s
	and v4.16b, v4.16b, v5.16b
	orr v1.16b, v1.16b, v4.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 28b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	add w4, w9, w14
	eor w4, w4, w15
	sub w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 25b
	cbz x8, 29f
	b 210f
29:
	ldr w9, [x12, #0]
	add w4, w9, w6
	ldr w13, [x12, #64]
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #31
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #30
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #28
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #24
	csel w4, w15, w4, ne
	lsr w13, w13, #1
	movz w14, #1, lsl #0
	tst w13, w14
	ror w15, w4, #16
	csel w4, w15, w4, ne
	lsl w14, w4, #24
	lsr w14, w14, #24
	mov v0.s[0], w14
	lsl w14, w4, #16
	lsr w14, w14, #24
	mov v0.s[1], w14
	lsl w14, w4, #8
	lsr w14, w14, #24
	mov v0.s[2], w14
	lsr w14, w4, #24
	mov v0.s[3], w14
	adrp x10, {VG_CAST5_S1234}
	add x10, x10, {VG_CAST5_S1234}
	movz x11, #64, lsl #0
	movi v1.2d, #0
	movi v2.2d, #0
	cmeq v3.4s, v3.4s, v3.4s
	ushr v3.4s, v3.4s, #31
	and v4.16b, v0.16b, v3.16b
	movi v16.2d, #0
	sub v16.4s, v16.4s, v4.4s
	ushr v4.4s, v0.4s, #1
	and v4.16b, v4.16b, v3.16b
	movi v17.2d, #0
	sub v17.4s, v17.4s, v4.4s
	ushr v18.4s, v0.4s, #2
211:
	ldr q4, [x10, #0]
	ldr q5, [x10, #16]
	bit v4.16b, v5.16b, v16.16b
	ldr q19, [x10, #32]
	ldr q5, [x10, #48]
	bit v19.16b, v5.16b, v16.16b
	bit v4.16b, v19.16b, v17.16b
	cmeq v5.4s, v18.4s, v2.4s
	and v4.16b, v4.16b, v5.16b
	orr v1.16b, v1.16b, v4.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 211b
	umov w9, v1.s[3]
	umov w14, v1.s[2]
	umov w15, v1.s[1]
	umov w10, v1.s[0]
	eor w4, w9, w14
	sub w4, w4, w15
	add w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
210:
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	add x5, x16, #0
	ldr x6, [x5, #0]
	str x6, [x23, #0]
	sub x24, x24, #1
	cbz x24, 212f
	ldr x6, [x23, #8]
	ldr x7, [x5, #0]
	eor x6, x6, x7
	str x6, [x23, #8]
	b 213f
212:
213:
	add x23, x23, #8
	cbnz x24, 24b
	ldr x6, [x5, #0]
	str x6, [x25, #0]
	b 23f
22:
23:
	ldr x19, [x5, #8]
	ldr x20, [x5, #16]
	ldr x21, [x5, #24]
	ldr x22, [x5, #32]
	ldr x23, [x5, #40]
	ldr x24, [x5, #48]
	ldr x25, [x5, #56]
	ldr x26, [x5, #64]
	ldr x27, [x5, #72]
	ldr x28, [x5, #80]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	str x17, [sp, #96]
	add sp, sp, #112
	movz x4, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x10, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	tst x4, x4
	sub sp, sp, #112
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #96]
	add sp, sp, #112
	ret
	.p2align 6

vg_cast5_cbc_decrypt_chained:
	sub sp, sp, #224
	add x5, sp, #0
	add x5, x5, #0
	str x19, [x5, #128]
	str x20, [x5, #136]
	str x21, [x5, #144]
	str x22, [x5, #152]
	str x23, [x5, #160]
	str x24, [x5, #168]
	str x25, [x5, #176]
	str x26, [x5, #184]
	str x27, [x5, #192]
	str x28, [x5, #200]
	ldr x6, [x2, #0]
	str x6, [x5, #208]
	cbz x4, 20f
	sub x7, x4, #1
	lsl x7, x7, #3
	add x7, x7, x3
	ldr x6, [x7, #0]
	str x6, [x2, #0]
	b 21f
20:
21:
	add x23, x3, #0
	add x24, x4, #0
	cbz x24, 22f
24:
	lsr x13, x24, #4
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #16, lsl #0
26:
	add x14, x5, #0
	add x14, x14, #0
	add x15, x23, #0
	add x17, x16, #0
27:
	ldr x8, [x15, #0]
	str x8, [x14, #0]
	add x14, x14, #8
	add x15, x15, #8
	sub x17, x17, #1
	cbnz x17, 27b
	umov x11, v8.d[0]
	umov x12, v9.d[0]
	umov x19, v10.d[0]
	umov x20, v11.d[0]
	umov x21, v12.d[0]
	umov x26, v13.d[0]
	umov x27, v14.d[0]
	umov x28, v15.d[0]
	add x22, x5, #0
	add x4, x5, #0
	add x16, x1, #0
	movz x6, #64, lsl #0
	dup v2.16b, w6
	movz x6, #128, lsl #0
	dup v3.16b, w6
	add x10, x30, #0
	add x14, x16, #0
	bl {vg_cast5_batch_decrypt}
	add x30, x10, #0
	dup v8.2d, x11
	dup v9.2d, x12
	dup v10.2d, x19
	dup v11.2d, x20
	dup v12.2d, x21
	dup v13.2d, x26
	dup v14.2d, x27
	dup v15.2d, x28
	add x5, x22, #0
	lsr x13, x24, #4
	cbnz x13, 28f
	add x16, x24, #0
	b 29f
28:
	movz x16, #16, lsl #0
29:
	add x14, x5, #0
	add x14, x14, #0
	add x15, x23, #0
	add x17, x16, #0
210:
	ldr x8, [x14, #0]
	ldr x9, [x5, #208]
	eor x8, x8, x9
	str x8, [x14, #0]
	ldr x8, [x15, #0]
	str x8, [x5, #208]
	ldr x8, [x14, #0]
	str x8, [x15, #0]
	add x14, x14, #8
	add x15, x15, #8
	sub x17, x17, #1
	cbnz x17, 210b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 24b
	b 23f
22:
23:
	ldr x19, [x5, #128]
	ldr x20, [x5, #136]
	ldr x21, [x5, #144]
	ldr x22, [x5, #152]
	ldr x23, [x5, #160]
	ldr x24, [x5, #168]
	ldr x25, [x5, #176]
	ldr x26, [x5, #184]
	ldr x27, [x5, #192]
	ldr x28, [x5, #200]
	movz x17, #0, lsl #0
	add x16, sp, #0
	stp x17, x17, [x16, #0]
	stp x17, x17, [x16, #16]
	stp x17, x17, [x16, #32]
	stp x17, x17, [x16, #48]
	stp x17, x17, [x16, #64]
	stp x17, x17, [x16, #80]
	stp x17, x17, [x16, #96]
	stp x17, x17, [x16, #112]
	stp x17, x17, [x16, #128]
	stp x17, x17, [x16, #144]
	stp x17, x17, [x16, #160]
	stp x17, x17, [x16, #176]
	stp x17, x17, [x16, #192]
	stp x17, x17, [x16, #208]
	add sp, sp, #224
	movz x6, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v4.2d, #0
	movi v5.2d, #0
	movi v6.2d, #0
	movi v7.2d, #0
	movi v16.2d, #0
	movi v17.2d, #0
	movi v18.2d, #0
	movi v19.2d, #0
	movi v20.2d, #0
	movi v21.2d, #0
	movi v22.2d, #0
	movi v23.2d, #0
	movi v24.2d, #0
	movi v25.2d, #0
	movi v26.2d, #0
	movi v27.2d, #0
	tst x6, x6
	ret
	.p2align 6
