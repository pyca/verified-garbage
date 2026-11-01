// The functions of `src/cast5_cfb.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cast5_cfb64_encrypt:
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
	add x23, x3, #0
	add x24, x4, #0
	ldr x6, [x25, #0]
	str x6, [x5, #0]
	cbz x24, 20f
22:
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
23:
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
24:
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
	cbnz x11, 24b
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
25:
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
	cbnz x11, 25b
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
	add w4, w9, w14
	eor w4, w4, w15
	sub w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 23b
	cbz x8, 27f
	b 28f
27:
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
29:
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
	cbnz x11, 29b
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
28:
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	add x5, x16, #0
	ldr x6, [x23, #0]
	ldr x7, [x5, #0]
	eor x6, x6, x7
	str x6, [x23, #0]
	ldr x6, [x23, #0]
	str x6, [x5, #0]
	add x23, x23, #8
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x6, [x5, #0]
	str x6, [x25, #0]
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

vg_cast5_cfb64_decrypt:
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
	add x23, x3, #0
	add x24, x4, #0
	ldr x6, [x25, #0]
	str x6, [x5, #0]
	cbz x24, 20f
22:
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
23:
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
24:
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
	cbnz x11, 24b
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
25:
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
	cbnz x11, 25b
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
	add w4, w9, w14
	eor w4, w4, w15
	sub w4, w4, w10
	eor w4, w4, w5
	orr w5, w6, w6
	orr w6, w4, w4
	add x12, x12, #4
	sub x7, x7, #1
	cbnz x7, 23b
	cbz x8, 27f
	b 28f
27:
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
29:
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
	cbnz x11, 29b
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
28:
	rev w6, w6
	str w6, [x2, #0]
	rev w5, w5
	str w5, [x2, #4]
	add x2, x2, #8
	sub x3, x3, #1
	add x5, x16, #0
	ldr x6, [x23, #0]
	ldr x7, [x5, #0]
	eor x6, x6, x7
	str x6, [x23, #0]
	ldr x6, [x5, #0]
	ldr x7, [x23, #0]
	eor x6, x6, x7
	str x6, [x5, #0]
	add x23, x23, #8
	sub x24, x24, #1
	cbnz x24, 22b
	b 21f
20:
21:
	ldr x6, [x5, #0]
	str x6, [x25, #0]
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
