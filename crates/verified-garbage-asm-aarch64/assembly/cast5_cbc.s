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
26:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
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
27:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
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
28:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
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
211:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
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
	ret
	.p2align 6

vg_cast5_cbc_decrypt_chained:
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
	ldr x6, [x2, #0]
	str x6, [x5, #88]
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
	lsr x13, x24, #0
	cbnz x13, 25f
	add x16, x24, #0
	b 26f
25:
	movz x16, #1, lsl #0
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
	add x16, x5, #0
	add x2, x5, #0
	ldr w5, [x2, #0]
	rev w5, w5
	ldr w6, [x2, #4]
	rev w6, w6
	lsl x12, x1, #2
	add x12, x12, x0
	sub x12, x12, #4
	lsr x7, x1, #2
	add x7, x7, #1
	sub x8, x1, #16
	cbz x8, 28f
	b 29f
28:
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
210:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 210b
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
	sub x12, x12, #4
29:
211:
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
212:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 212b
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
	sub x12, x12, #4
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
213:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 213b
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
	sub x12, x12, #4
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
214:
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #0]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #16]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #32]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	cmeq v4.4s, v0.4s, v2.4s
	ldr q5, [x10, #48]
	and v5.16b, v5.16b, v4.16b
	orr v1.16b, v1.16b, v5.16b
	add v2.4s, v2.4s, v3.4s
	add x10, x10, #64
	sub x11, x11, #1
	cbnz x11, 214b
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
	sub x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 211b
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	add x5, x16, #0
	lsr x13, x24, #0
	cbnz x13, 215f
	add x16, x24, #0
	b 216f
215:
	movz x16, #1, lsl #0
216:
	add x14, x5, #0
	add x14, x14, #0
	add x15, x23, #0
	add x17, x16, #0
217:
	ldr x8, [x14, #0]
	ldr x9, [x5, #88]
	eor x8, x8, x9
	str x8, [x14, #0]
	ldr x8, [x15, #0]
	str x8, [x5, #88]
	ldr x8, [x14, #0]
	str x8, [x15, #0]
	add x14, x14, #8
	add x15, x15, #8
	sub x17, x17, #1
	cbnz x17, 217b
	add x23, x15, #0
	sub x24, x24, x16
	cbnz x24, 24b
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
	ret
	.p2align 6
