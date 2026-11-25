// The functions of `src/x25519.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x25519_exchange:
	str x30, [sp, #-16]!
	add x9, sp, #0
	str x0, [x9, #8]
	bl {vg_x25519}
	add x9, sp, #0
	ldr x9, [x9, #8]
	movz x10, #0, lsl #0
	ldrb w11, [x9, #0]
	orr x10, x10, x11
	ldrb w11, [x9, #1]
	orr x10, x10, x11
	ldrb w11, [x9, #2]
	orr x10, x10, x11
	ldrb w11, [x9, #3]
	orr x10, x10, x11
	ldrb w11, [x9, #4]
	orr x10, x10, x11
	ldrb w11, [x9, #5]
	orr x10, x10, x11
	ldrb w11, [x9, #6]
	orr x10, x10, x11
	ldrb w11, [x9, #7]
	orr x10, x10, x11
	ldrb w11, [x9, #8]
	orr x10, x10, x11
	ldrb w11, [x9, #9]
	orr x10, x10, x11
	ldrb w11, [x9, #10]
	orr x10, x10, x11
	ldrb w11, [x9, #11]
	orr x10, x10, x11
	ldrb w11, [x9, #12]
	orr x10, x10, x11
	ldrb w11, [x9, #13]
	orr x10, x10, x11
	ldrb w11, [x9, #14]
	orr x10, x10, x11
	ldrb w11, [x9, #15]
	orr x10, x10, x11
	ldrb w11, [x9, #16]
	orr x10, x10, x11
	ldrb w11, [x9, #17]
	orr x10, x10, x11
	ldrb w11, [x9, #18]
	orr x10, x10, x11
	ldrb w11, [x9, #19]
	orr x10, x10, x11
	ldrb w11, [x9, #20]
	orr x10, x10, x11
	ldrb w11, [x9, #21]
	orr x10, x10, x11
	ldrb w11, [x9, #22]
	orr x10, x10, x11
	ldrb w11, [x9, #23]
	orr x10, x10, x11
	ldrb w11, [x9, #24]
	orr x10, x10, x11
	ldrb w11, [x9, #25]
	orr x10, x10, x11
	ldrb w11, [x9, #26]
	orr x10, x10, x11
	ldrb w11, [x9, #27]
	orr x10, x10, x11
	ldrb w11, [x9, #28]
	orr x10, x10, x11
	ldrb w11, [x9, #29]
	orr x10, x10, x11
	ldrb w11, [x9, #30]
	orr x10, x10, x11
	ldrb w11, [x9, #31]
	orr x10, x10, x11
	sub x10, x10, #1
	lsr x0, x10, #63
	movz x11, #1, lsl #0
	eor x0, x0, x11
	ldr x30, [sp], #16
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x10, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	movi v0.2d, #0
	movi v1.2d, #0
	movi v2.2d, #0
	movi v3.2d, #0
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
	movi v28.2d, #0
	movi v29.2d, #0
	movi v30.2d, #0
	movi v31.2d, #0
	tst x3, x3
	mov v8.d[1], x3
	mov v9.d[1], x3
	mov v10.d[1], x3
	mov v11.d[1], x3
	mov v12.d[1], x3
	mov v13.d[1], x3
	mov v14.d[1], x3
	mov v15.d[1], x3
	add w0, w0, #0
	sub sp, sp, #16
	movi v31.2d, #0
	add x9, sp, #0
	str q31, [x9, #0]
	add sp, sp, #16
	ret
	.p2align 6

vg_x25519_base:
	str x19, [x2, #0]
	str x20, [x2, #8]
	str x21, [x2, #16]
	str x22, [x2, #24]
	str x23, [x2, #32]
	str x24, [x2, #40]
	str x0, [x2, #48]
	add x0, x2, #0
	movz x11, #15, lsl #0
	ldrb w8, [x1, #0]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #768]
	strb w9, [x0, #769]
	ldrb w8, [x1, #1]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #770]
	strb w9, [x0, #771]
	ldrb w8, [x1, #2]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #772]
	strb w9, [x0, #773]
	ldrb w8, [x1, #3]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #774]
	strb w9, [x0, #775]
	ldrb w8, [x1, #4]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #776]
	strb w9, [x0, #777]
	ldrb w8, [x1, #5]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #778]
	strb w9, [x0, #779]
	ldrb w8, [x1, #6]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #780]
	strb w9, [x0, #781]
	ldrb w8, [x1, #7]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #782]
	strb w9, [x0, #783]
	ldrb w8, [x1, #8]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #784]
	strb w9, [x0, #785]
	ldrb w8, [x1, #9]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #786]
	strb w9, [x0, #787]
	ldrb w8, [x1, #10]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #788]
	strb w9, [x0, #789]
	ldrb w8, [x1, #11]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #790]
	strb w9, [x0, #791]
	ldrb w8, [x1, #12]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #792]
	strb w9, [x0, #793]
	ldrb w8, [x1, #13]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #794]
	strb w9, [x0, #795]
	ldrb w8, [x1, #14]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #796]
	strb w9, [x0, #797]
	ldrb w8, [x1, #15]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #798]
	strb w9, [x0, #799]
	ldrb w8, [x1, #16]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #800]
	strb w9, [x0, #801]
	ldrb w8, [x1, #17]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #802]
	strb w9, [x0, #803]
	ldrb w8, [x1, #18]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #804]
	strb w9, [x0, #805]
	ldrb w8, [x1, #19]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #806]
	strb w9, [x0, #807]
	ldrb w8, [x1, #20]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #808]
	strb w9, [x0, #809]
	ldrb w8, [x1, #21]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #810]
	strb w9, [x0, #811]
	ldrb w8, [x1, #22]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #812]
	strb w9, [x0, #813]
	ldrb w8, [x1, #23]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #814]
	strb w9, [x0, #815]
	ldrb w8, [x1, #24]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #816]
	strb w9, [x0, #817]
	ldrb w8, [x1, #25]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #818]
	strb w9, [x0, #819]
	ldrb w8, [x1, #26]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #820]
	strb w9, [x0, #821]
	ldrb w8, [x1, #27]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #822]
	strb w9, [x0, #823]
	ldrb w8, [x1, #28]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #824]
	strb w9, [x0, #825]
	ldrb w8, [x1, #29]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #826]
	strb w9, [x0, #827]
	ldrb w8, [x1, #30]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #828]
	strb w9, [x0, #829]
	ldrb w8, [x1, #31]
	lsr x9, x8, #4
	and x8, x8, x11
	strb w8, [x0, #830]
	strb w9, [x0, #831]
	ldrb w8, [x0, #768]
	movz w9, #8, lsl #0
	and x8, x8, x9
	strb w8, [x0, #768]
	ldrb w8, [x0, #831]
	movz w9, #3, lsl #0
	and x8, x8, x9
	movz w9, #4, lsl #0
	orr x8, x8, x9
	strb w8, [x0, #831]
	movz x4, #19732, lsl #0
	movk x4, #3704, lsl #16
	movk x4, #12927, lsl #32
	movk x4, #9506, lsl #48
	movz x5, #5405, lsl #0
	movk x5, #45271, lsl #16
	movk x5, #55882, lsl #32
	movk x5, #3292, lsl #48
	movz x6, #56252, lsl #0
	movk x6, #36121, lsl #16
	movk x6, #1244, lsl #32
	movk x6, #24478, lsl #48
	movz x7, #6932, lsl #0
	movk x7, #13402, lsl #16
	movk x7, #62822, lsl #32
	movk x7, #2631, lsl #48
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz x4, #63212, lsl #0
	movk x4, #7152, lsl #16
	movk x4, #46503, lsl #32
	movk x4, #42296, lsl #48
	movz x5, #22843, lsl #0
	movk x5, #23337, lsl #16
	movk x5, #47280, lsl #32
	movk x5, #5943, lsl #48
	movz x6, #51705, lsl #0
	movk x6, #39721, lsl #16
	movk x6, #22935, lsl #32
	movk x6, #12652, lsl #48
	movz x7, #638, lsl #0
	movk x7, #13703, lsl #16
	movk x7, #18230, lsl #32
	movk x7, #2371, lsl #48
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz x4, #1, lsl #0
	movk x4, #0, lsl #16
	movk x4, #0, lsl #32
	movk x4, #0, lsl #48
	movz x5, #0, lsl #0
	movk x5, #0, lsl #16
	movk x5, #0, lsl #32
	movk x5, #0, lsl #48
	movz x6, #0, lsl #0
	movk x6, #0, lsl #16
	movk x6, #0, lsl #32
	movk x6, #0, lsl #48
	movz x7, #0, lsl #0
	movk x7, #0, lsl #16
	movk x7, #0, lsl #32
	movk x7, #0, lsl #48
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x4, #21093, lsl #0
	movk x4, #17697, lsl #16
	movk x4, #18186, lsl #32
	movk x4, #52560, lsl #48
	movz x5, #40439, lsl #0
	movk x5, #3071, lsl #16
	movk x5, #8693, lsl #32
	movk x5, #63940, lsl #48
	movz x6, #32329, lsl #0
	movk x6, #58054, lsl #16
	movk x6, #33041, lsl #32
	movk x6, #3634, lsl #48
	movz x7, #49440, lsl #0
	movk x7, #53819, lsl #16
	movk x7, #38278, lsl #32
	movk x7, #14477, lsl #48
	str x4, [x0, #160]
	str x5, [x0, #168]
	str x6, [x0, #176]
	str x7, [x0, #184]
	movz w10, #0, lsl #0
	adrp x1, {VG_ED25519_COMB}
	add x1, x1, {VG_ED25519_COMB}
	movz w19, #0, lsl #0
20:
	add x8, x0, x19
	ldrb w8, [x8, #768]
	sub x8, x8, #8
	lsr x9, x8, #63
	sub x9, x10, x9
	eor x8, x8, x9
	sub x8, x8, x9
	movz w4, #1, lsl #0
	movz w5, #0, lsl #0
	movz w6, #0, lsl #0
	movz w7, #0, lsl #0
	movz w12, #1, lsl #0
	movz w13, #0, lsl #0
	movz w14, #0, lsl #0
	movz w15, #0, lsl #0
	movz w21, #0, lsl #0
	movz w22, #0, lsl #0
	movz w23, #0, lsl #0
	movz w24, #0, lsl #0
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x8, x8, #1
	tst x8, x8
	ldp x2, x3, [x1, #0]
	csel x4, x2, x4, eq
	csel x5, x3, x5, eq
	ldp x2, x3, [x1, #16]
	csel x6, x2, x6, eq
	csel x7, x3, x7, eq
	ldp x2, x3, [x1, #32]
	csel x12, x2, x12, eq
	csel x13, x3, x13, eq
	ldp x2, x3, [x1, #48]
	csel x14, x2, x14, eq
	csel x15, x3, x15, eq
	ldp x2, x3, [x1, #64]
	csel x21, x2, x21, eq
	csel x22, x3, x22, eq
	ldp x2, x3, [x1, #80]
	csel x23, x2, x23, eq
	csel x24, x3, x24, eq
	add x1, x1, #96
	sub x2, x10, #19
	sub x3, x10, #1
	lsr x8, x3, #1
	subs x2, x2, x21
	sbcs x17, x3, x22
	sbcs x20, x3, x23
	sbc x8, x8, x24
	tst x9, x9
	csel x16, x12, x4, ne
	csel x12, x4, x12, ne
	csel x4, x13, x5, ne
	csel x13, x5, x13, ne
	csel x5, x14, x6, ne
	csel x14, x6, x14, ne
	csel x6, x15, x7, ne
	csel x15, x7, x15, ne
	csel x21, x2, x21, ne
	csel x22, x17, x22, ne
	csel x23, x20, x23, ne
	csel x24, x8, x24, ne
	stp x16, x4, [x0, #192]
	stp x5, x6, [x0, #208]
	stp x12, x13, [x0, #224]
	stp x14, x15, [x0, #240]
	stp x21, x22, [x0, #256]
	stp x23, x24, [x0, #272]
	ldp x4, x5, [x0, #96]
	ldp x6, x7, [x0, #112]
	ldp x21, x22, [x0, #64]
	ldp x23, x24, [x0, #80]
	subs x12, x4, x21
	sbcs x13, x5, x22
	movz w2, #38, lsl #0
	sbcs x14, x6, x23
	sbcs x15, x7, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	ldr x3, [x0, #192]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #200]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #208]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #216]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #320]
	stp x6, x7, [x0, #336]
	ldp x4, x5, [x0, #96]
	ldp x6, x7, [x0, #112]
	ldp x21, x22, [x0, #64]
	ldp x23, x24, [x0, #80]
	adds x12, x4, x21
	adcs x13, x5, x22
	movz w2, #38, lsl #0
	adcs x14, x6, x23
	adcs x15, x7, x24
	csel x3, x2, x10, hs
	adds x12, x12, x3
	adcs x13, x13, x10
	adc x14, x14, x10
	ldr x3, [x0, #224]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #232]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #240]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #248]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #352]
	stp x6, x7, [x0, #368]
	ldp x12, x13, [x0, #256]
	ldp x14, x15, [x0, #272]
	ldr x3, [x0, #160]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #168]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #176]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #184]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #384]
	stp x6, x7, [x0, #400]
	ldp x4, x5, [x0, #352]
	ldp x6, x7, [x0, #368]
	ldp x21, x22, [x0, #320]
	ldp x23, x24, [x0, #336]
	subs x12, x4, x21
	sbcs x13, x5, x22
	movz w2, #38, lsl #0
	sbcs x14, x6, x23
	sbcs x15, x7, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	stp x12, x13, [x0, #288]
	stp x14, x15, [x0, #304]
	adds x4, x4, x21
	adcs x5, x5, x22
	movz w2, #38, lsl #0
	adcs x6, x6, x23
	adcs x7, x7, x24
	csel x3, x2, x10, hs
	adds x4, x4, x3
	adcs x5, x5, x10
	adc x6, x6, x10
	stp x4, x5, [x0, #416]
	stp x6, x7, [x0, #432]
	ldp x4, x5, [x0, #128]
	ldp x6, x7, [x0, #144]
	adds x4, x4, x4
	adcs x5, x5, x5
	movz w2, #38, lsl #0
	adcs x6, x6, x6
	adcs x7, x7, x7
	csel x3, x2, x10, hs
	adds x4, x4, x3
	adcs x5, x5, x10
	adc x6, x6, x10
	ldp x21, x22, [x0, #384]
	ldp x23, x24, [x0, #400]
	subs x12, x4, x21
	sbcs x13, x5, x22
	movz w2, #38, lsl #0
	sbcs x14, x6, x23
	sbcs x15, x7, x24
	csel x3, x10, x2, hs
	subs x12, x12, x3
	sbcs x13, x13, x10
	sbcs x14, x14, x10
	sbc x15, x15, x10
	adds x4, x4, x21
	adcs x5, x5, x22
	movz w2, #38, lsl #0
	adcs x6, x6, x23
	adcs x7, x7, x24
	csel x3, x2, x10, hs
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adc x7, x7, x10
	stp x4, x5, [x0, #480]
	stp x6, x7, [x0, #496]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #128]
	stp x6, x7, [x0, #144]
	ldr x3, [x0, #288]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #296]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #304]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #312]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #64]
	stp x6, x7, [x0, #80]
	ldp x12, x13, [x0, #416]
	ldp x14, x15, [x0, #432]
	ldr x3, [x0, #480]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #488]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #496]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #504]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #96]
	stp x6, x7, [x0, #112]
	ldr x3, [x0, #288]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #296]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #304]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #312]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	stp x4, x5, [x0, #160]
	stp x6, x7, [x0, #176]
	add x19, x19, #1
	sub x8, x19, #64
	cbnz x8, 20b
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #128]
	ldr x9, [x0, #96]
	adds x4, x4, x9
	ldr x5, [x0, #136]
	ldr x9, [x0, #104]
	adcs x5, x5, x9
	ldr x6, [x0, #144]
	ldr x9, [x0, #112]
	adcs x6, x6, x9
	ldr x7, [x0, #152]
	ldr x9, [x0, #120]
	adcs x7, x7, x9
	csel x8, x11, x10, hs
	adds x4, x4, x8
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	csel x8, x11, x10, hs
	add x4, x4, x8
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	movz w11, #38, lsl #0
	ldr x4, [x0, #128]
	ldr x9, [x0, #96]
	subs x4, x4, x9
	ldr x5, [x0, #136]
	ldr x9, [x0, #104]
	sbcs x5, x5, x9
	ldr x6, [x0, #144]
	ldr x9, [x0, #112]
	sbcs x6, x6, x9
	ldr x7, [x0, #152]
	ldr x9, [x0, #120]
	sbcs x7, x7, x9
	sbcs x8, x10, x10
	and x8, x8, x11
	subs x4, x4, x8
	sbcs x5, x5, x10
	sbcs x6, x6, x10
	sbcs x7, x7, x10
	sbcs x8, x10, x10
	and x8, x8, x11
	sub x4, x4, x8
	str x4, [x0, #128]
	str x5, [x0, #136]
	str x6, [x0, #144]
	str x7, [x0, #152]
	movz x2, #65517, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #65535, lsl #48
	movz x3, #65535, lsl #0
	movk x3, #65535, lsl #16
	movk x3, #65535, lsl #32
	movk x3, #65535, lsl #48
	movz x8, #65535, lsl #0
	movk x8, #65535, lsl #16
	movk x8, #65535, lsl #32
	movk x8, #65535, lsl #48
	movz x9, #65535, lsl #0
	movk x9, #65535, lsl #16
	movk x9, #65535, lsl #32
	movk x9, #32767, lsl #48
	stp x2, x3, [x0, #192]
	stp x8, x9, [x0, #208]
	movz x2, #0, lsl #0
	movk x2, #0, lsl #16
	movk x2, #0, lsl #32
	movk x2, #0, lsl #48
	movz x3, #0, lsl #0
	movk x3, #0, lsl #16
	movk x3, #0, lsl #32
	movk x3, #0, lsl #48
	movz x8, #0, lsl #0
	movk x8, #0, lsl #16
	movk x8, #0, lsl #32
	movk x8, #0, lsl #48
	movz x9, #0, lsl #0
	movk x9, #0, lsl #16
	movk x9, #0, lsl #32
	movk x9, #0, lsl #48
	stp x2, x3, [x0, #256]
	stp x8, x9, [x0, #272]
	movz x2, #8345, lsl #0
	movk x2, #29954, lsl #16
	movk x2, #40483, lsl #32
	movk x2, #41209, lsl #48
	movz x3, #9621, lsl #0
	movk x3, #7443, lsl #16
	movk x3, #36671, lsl #32
	movk x3, #43206, lsl #48
	movz x8, #21058, lsl #0
	movk x8, #1452, lsl #16
	movk x8, #35128, lsl #32
	movk x8, #27756, lsl #48
	movz x9, #1557, lsl #0
	movk x9, #16759, lsl #16
	movk x9, #2226, lsl #32
	movk x9, #10085, lsl #48
	stp x2, x3, [x0, #288]
	stp x8, x9, [x0, #304]
	ldp x2, x3, [x0, #128]
	ldp x8, x9, [x0, #144]
	movz x16, #0, lsl #0
	movz x17, #19, lsl #0
	adds x9, x9, x9
	lsr x9, x9, #1
	csel x11, x17, x16, hs
	adds x2, x2, x11
	adcs x3, x3, x16
	adcs x8, x8, x16
	adc x9, x9, x16
	adds x11, x2, x17
	adcs x12, x3, x16
	adcs x13, x8, x16
	adc x14, x9, x16
	tst x14, x14
	add x14, x14, x14
	lsr x14, x14, #1
	csel x2, x11, x2, mi
	csel x3, x12, x3, mi
	csel x8, x13, x8, mi
	csel x9, x14, x9, mi
	stp x2, x3, [x0, #224]
	stp x8, x9, [x0, #240]
	movz x20, #0, lsl #0
	movz x19, #10, lsl #0
21:
	sub x19, x19, #1
	ldr x2, [x0, #192]
	ldr x3, [x0, #224]
	movz x14, #16384, lsl #16
	movk x14, #8192, lsl #32
	movk x14, #8192, lsl #48
	movz x15, #32767, lsl #0
	movz x17, #16384, lsl #0
	and x8, x2, x15
	and x9, x3, x15
	movk x8, #32768, lsl #16
	movk x9, #32768, lsl #32
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x8, x8, x14
	lsr x5, x8, #47
	lsl x4, x8, #17
	lsr x4, x4, #48
	sub x5, x5, x17
	sub x4, x4, x17
	add x10, x10, x14
	lsr x7, x10, #47
	lsl x6, x10, #17
	lsr x6, x6, #48
	sub x7, x7, x17
	sub x6, x6, x17
	mul x13, x2, x4
	mul x16, x2, x6
	madd x2, x3, x5, x13
	madd x3, x3, x7, x16
	lsr x2, x2, #15
	lsr x3, x3, #15
	and x8, x2, x15
	and x9, x3, x15
	movk x8, #32768, lsl #16
	movk x9, #32768, lsl #32
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x8, x8, x14
	lsr x11, x8, #47
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x11, x11, x17
	sub x8, x8, x17
	add x10, x10, x14
	lsr x9, x10, #47
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x9, x9, x17
	sub x10, x10, x17
	mul x13, x2, x8
	mul x16, x2, x10
	madd x2, x3, x11, x13
	madd x3, x3, x9, x16
	lsr x2, x2, #15
	lsr x3, x3, #15
	mul x13, x8, x4
	mul x16, x10, x4
	madd x4, x11, x6, x13
	madd x6, x9, x6, x16
	mul x13, x8, x5
	mul x16, x10, x5
	madd x5, x11, x7, x13
	madd x7, x9, x7, x16
	and x8, x2, x15
	and x9, x3, x15
	movk x8, #32768, lsl #16
	movk x9, #32768, lsl #32
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x8, x8, x14
	lsr x11, x8, #47
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x11, x11, x17
	sub x8, x8, x17
	add x10, x10, x14
	lsr x9, x10, #47
	lsl x10, x10, #17
	lsr x10, x10, #48
	sub x9, x9, x17
	sub x10, x10, x17
	mul x13, x2, x8
	mul x16, x2, x10
	madd x2, x3, x11, x13
	madd x3, x3, x9, x16
	lsr x2, x2, #15
	lsr x3, x3, #15
	mul x13, x8, x4
	mul x16, x10, x4
	madd x4, x11, x6, x13
	madd x6, x9, x6, x16
	mul x13, x8, x5
	mul x16, x10, x5
	madd x5, x11, x7, x13
	madd x7, x9, x7, x16
	and x8, x2, x15
	and x9, x3, x15
	movk x8, #32768, lsl #16
	movk x9, #32768, lsl #32
	movz x12, #1, lsl #0
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x10, x9, x8
	sub x11, x9, x8
	tst x9, x12
	csel x10, x10, x9, ne
	ccmp x20, #0, #8, ne
	csel x10, x11, x10, pl
	add x16, x9, x9
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x9, x10, x8
	sub x11, x10, x8
	tst x10, x12
	csel x9, x9, x10, ne
	ccmp x20, #0, #8, ne
	csel x9, x11, x9, pl
	add x16, x10, x10
	add x8, x8, x8
	csel x8, x16, x8, pl
	add x13, x20, #1
	csneg x20, x13, x20, mi
	add x12, x12, x12
	add x8, x8, x14
	lsr x11, x8, #47
	lsl x8, x8, #17
	lsr x8, x8, #48
	sub x11, x11, x17
	sub x8, x8, x17
	add x9, x9, x14
	lsr x10, x9, #47
	lsl x9, x9, #17
	lsr x9, x9, #48
	sub x10, x10, x17
	sub x9, x9, x17
	mul x13, x8, x4
	mul x16, x9, x4
	madd x4, x11, x6, x13
	madd x6, x10, x6, x16
	mul x13, x8, x5
	mul x16, x9, x5
	madd x5, x11, x7, x13
	madd x7, x10, x7, x16
	movz x16, #2048, lsl #48
	add x4, x4, x16
	add x5, x5, x16
	add x6, x6, x16
	add x7, x7, x16
	movz x16, #0, lsl #0
	ldp x2, x3, [x0, #192]
	ldp x8, x9, [x0, #208]
	ldp x11, x12, [x0, #224]
	ldp x13, x14, [x0, #240]
	adds x2, x2, x11
	adcs x3, x3, x12
	adcs x8, x8, x13
	adc x9, x9, x14
	stp x2, x3, [x0, #320]
	stp x8, x9, [x0, #336]
	ldp x11, x12, [x0, #192]
	ldp x13, x14, [x0, #208]
	mul x2, x4, x11
	umulh x3, x4, x11
	mul x15, x4, x12
	adds x3, x3, x15
	umulh x8, x4, x12
	mul x15, x4, x13
	adcs x8, x8, x15
	umulh x9, x4, x13
	mul x15, x4, x14
	adcs x9, x9, x15
	umulh x10, x4, x14
	adc x10, x10, x16
	tst x14, x14
	csel x15, x4, x16, mi
	sub x10, x10, x15
	ldp x11, x12, [x0, #224]
	ldp x13, x14, [x0, #240]
	mul x15, x5, x11
	adds x2, x2, x15
	mul x15, x5, x12
	adcs x3, x3, x15
	mul x15, x5, x13
	adcs x8, x8, x15
	mul x15, x5, x14
	adcs x9, x9, x15
	adc x10, x10, x16
	umulh x15, x5, x11
	adds x3, x3, x15
	umulh x15, x5, x12
	adcs x8, x8, x15
	umulh x15, x5, x13
	adcs x9, x9, x15
	umulh x15, x5, x14
	adc x10, x10, x15
	tst x14, x14
	csel x15, x5, x16, mi
	sub x10, x10, x15
	ldp x11, x12, [x0, #320]
	ldp x13, x14, [x0, #336]
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	extr x9, x10, x9, #59
	subs x2, x2, x11
	sbcs x3, x3, x12
	sbcs x8, x8, x13
	sbc x9, x9, x14
	stp x2, x3, [x0, #352]
	stp x8, x9, [x0, #368]
	ldp x11, x12, [x0, #192]
	ldp x13, x14, [x0, #208]
	mul x2, x6, x11
	umulh x3, x6, x11
	mul x15, x6, x12
	adds x3, x3, x15
	umulh x8, x6, x12
	mul x15, x6, x13
	adcs x8, x8, x15
	umulh x9, x6, x13
	mul x15, x6, x14
	adcs x9, x9, x15
	umulh x10, x6, x14
	adc x10, x10, x16
	tst x14, x14
	csel x15, x6, x16, mi
	sub x10, x10, x15
	ldp x11, x12, [x0, #224]
	ldp x13, x14, [x0, #240]
	mul x15, x7, x11
	adds x2, x2, x15
	mul x15, x7, x12
	adcs x3, x3, x15
	mul x15, x7, x13
	adcs x8, x8, x15
	mul x15, x7, x14
	adcs x9, x9, x15
	adc x10, x10, x16
	umulh x15, x7, x11
	adds x3, x3, x15
	umulh x15, x7, x12
	adcs x8, x8, x15
	umulh x15, x7, x13
	adcs x9, x9, x15
	umulh x15, x7, x14
	adc x10, x10, x15
	tst x14, x14
	csel x15, x7, x16, mi
	sub x10, x10, x15
	ldp x11, x12, [x0, #320]
	ldp x13, x14, [x0, #336]
	extr x2, x3, x2, #59
	extr x3, x8, x3, #59
	extr x8, x9, x8, #59
	extr x9, x10, x9, #59
	subs x2, x2, x11
	sbcs x3, x3, x12
	sbcs x8, x8, x13
	sbc x9, x9, x14
	stp x2, x3, [x0, #224]
	stp x8, x9, [x0, #240]
	ldp x11, x12, [x0, #352]
	ldp x13, x14, [x0, #368]
	stp x11, x12, [x0, #192]
	stp x13, x14, [x0, #208]
	ldp x2, x3, [x0, #256]
	ldp x8, x9, [x0, #272]
	ldp x11, x12, [x0, #288]
	ldp x13, x14, [x0, #304]
	movz x17, #38, lsl #0
	sub x15, x16, x17
	sub x17, x16, #1
	subs x2, x15, x2
	sbcs x3, x17, x3
	sbcs x8, x17, x8
	sbcs x9, x17, x9
	subs x2, x2, x11
	sbcs x3, x3, x12
	sbcs x8, x8, x13
	sbcs x9, x9, x14
	sbc x10, x16, x16
	lsl x11, x2, #59
	extr x12, x3, x2, #5
	extr x13, x8, x3, #5
	extr x14, x9, x8, #5
	extr x15, x10, x9, #5
	movz x17, #19, lsl #0
	stp x11, x12, [x0, #384]
	stp x13, x14, [x0, #400]
	str x15, [x0, #416]
	ldp x11, x12, [x0, #256]
	ldp x13, x14, [x0, #272]
	mul x2, x4, x11
	umulh x3, x4, x11
	mul x15, x4, x12
	adds x3, x3, x15
	umulh x8, x4, x12
	mul x15, x4, x13
	adcs x8, x8, x15
	umulh x9, x4, x13
	mul x15, x4, x14
	adcs x9, x9, x15
	umulh x10, x4, x14
	adc x10, x10, x16
	ldp x11, x12, [x0, #288]
	ldp x13, x14, [x0, #304]
	mul x15, x5, x11
	adds x2, x2, x15
	mul x15, x5, x12
	adcs x3, x3, x15
	mul x15, x5, x13
	adcs x8, x8, x15
	mul x15, x5, x14
	adcs x9, x9, x15
	adc x10, x10, x16
	umulh x15, x5, x11
	adds x3, x3, x15
	umulh x15, x5, x12
	adcs x8, x8, x15
	umulh x15, x5, x13
	adcs x9, x9, x15
	umulh x15, x5, x14
	adc x10, x10, x15
	ldp x11, x12, [x0, #384]
	ldp x13, x14, [x0, #400]
	ldr x15, [x0, #416]
	adds x2, x2, x11
	adcs x3, x3, x12
	adcs x8, x8, x13
	adcs x9, x9, x14
	adc x10, x10, x15
	adds x9, x9, x9
	adc x10, x10, x10
	lsr x9, x9, #1
	mul x11, x10, x17
	umulh x12, x10, x17
	adds x2, x2, x11
	adcs x3, x3, x12
	adcs x8, x8, x16
	adc x9, x9, x16
	stp x2, x3, [x0, #352]
	stp x8, x9, [x0, #368]
	ldp x11, x12, [x0, #256]
	ldp x13, x14, [x0, #272]
	mul x2, x6, x11
	umulh x3, x6, x11
	mul x15, x6, x12
	adds x3, x3, x15
	umulh x8, x6, x12
	mul x15, x6, x13
	adcs x8, x8, x15
	umulh x9, x6, x13
	mul x15, x6, x14
	adcs x9, x9, x15
	umulh x10, x6, x14
	adc x10, x10, x16
	ldp x11, x12, [x0, #288]
	ldp x13, x14, [x0, #304]
	mul x15, x7, x11
	adds x2, x2, x15
	mul x15, x7, x12
	adcs x3, x3, x15
	mul x15, x7, x13
	adcs x8, x8, x15
	mul x15, x7, x14
	adcs x9, x9, x15
	adc x10, x10, x16
	umulh x15, x7, x11
	adds x3, x3, x15
	umulh x15, x7, x12
	adcs x8, x8, x15
	umulh x15, x7, x13
	adcs x9, x9, x15
	umulh x15, x7, x14
	adc x10, x10, x15
	ldp x11, x12, [x0, #384]
	ldp x13, x14, [x0, #400]
	ldr x15, [x0, #416]
	adds x2, x2, x11
	adcs x3, x3, x12
	adcs x8, x8, x13
	adcs x9, x9, x14
	adc x10, x10, x15
	adds x9, x9, x9
	adc x10, x10, x10
	lsr x9, x9, #1
	mul x11, x10, x17
	umulh x12, x10, x17
	adds x2, x2, x11
	adcs x3, x3, x12
	adcs x8, x8, x16
	adc x9, x9, x16
	stp x2, x3, [x0, #288]
	stp x8, x9, [x0, #304]
	ldp x11, x12, [x0, #352]
	ldp x13, x14, [x0, #368]
	stp x11, x12, [x0, #256]
	stp x13, x14, [x0, #272]
	cbnz x19, 21b
	ldp x2, x3, [x0, #256]
	ldp x8, x9, [x0, #272]
	ldp x11, x12, [x0, #256]
	ldp x13, x14, [x0, #272]
	ldr x10, [x0, #216]
	movz x16, #0, lsl #0
	movz x17, #38, lsl #0
	sub x15, x16, x17
	sub x17, x16, #1
	subs x2, x15, x2
	sbcs x3, x17, x3
	sbcs x8, x17, x8
	sbcs x9, x17, x9
	tst x10, x10
	csel x2, x2, x11, mi
	csel x3, x3, x12, mi
	csel x8, x8, x13, mi
	csel x9, x9, x14, mi
	str x2, [x0, #544]
	str x3, [x0, #552]
	str x8, [x0, #560]
	str x9, [x0, #568]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #64]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #72]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #80]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #88]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	str x4, [x0, #64]
	str x5, [x0, #72]
	str x6, [x0, #80]
	str x7, [x0, #88]
	movz w10, #0, lsl #0
	ldr x12, [x0, #544]
	ldr x13, [x0, #552]
	ldr x14, [x0, #560]
	ldr x15, [x0, #568]
	ldr x3, [x0, #96]
	mul x4, x3, x12
	mul x5, x3, x13
	mul x6, x3, x14
	mul x7, x3, x15
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adc x21, x16, x10
	ldr x3, [x0, #104]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x5, x5, x2
	adcs x6, x6, x8
	adcs x7, x7, x9
	adcs x21, x21, x16
	adc x22, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adc x22, x22, x16
	ldr x3, [x0, #112]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x6, x6, x2
	adcs x7, x7, x8
	adcs x21, x21, x9
	adcs x22, x22, x16
	adc x23, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adc x23, x23, x16
	ldr x3, [x0, #120]
	mul x2, x3, x12
	mul x8, x3, x13
	mul x9, x3, x14
	mul x16, x3, x15
	adds x7, x7, x2
	adcs x21, x21, x8
	adcs x22, x22, x9
	adcs x23, x23, x16
	adc x24, x10, x10
	umulh x2, x3, x12
	umulh x8, x3, x13
	umulh x9, x3, x14
	umulh x16, x3, x15
	adds x21, x21, x2
	adcs x22, x22, x8
	adcs x23, x23, x9
	adc x24, x24, x16
	movz w11, #38, lsl #0
	mul x2, x11, x21
	adds x4, x4, x2
	mul x8, x11, x22
	adcs x5, x5, x8
	mul x9, x11, x23
	adcs x6, x6, x9
	mul x16, x11, x24
	adcs x7, x7, x16
	adc x20, x10, x10
	umulh x2, x11, x21
	umulh x8, x11, x22
	umulh x9, x11, x23
	umulh x16, x11, x24
	adds x7, x7, x9
	adc x20, x20, x16
	adds x16, x7, x7
	adc x9, x20, x20
	lsr x7, x16, #1
	movz w11, #19, lsl #0
	mul x9, x9, x11
	adds x4, x4, x9
	adcs x5, x5, x2
	adcs x6, x6, x8
	adc x7, x7, x10
	str x4, [x0, #96]
	str x5, [x0, #104]
	str x6, [x0, #112]
	str x7, [x0, #120]
	movz w10, #0, lsl #0
	movz w11, #19, lsl #0
	movz x2, #65535, lsl #0
	movk x2, #65535, lsl #16
	movk x2, #65535, lsl #32
	movk x2, #32767, lsl #48
	ldr x4, [x0, #64]
	ldr x5, [x0, #72]
	ldr x6, [x0, #80]
	ldr x7, [x0, #88]
	lsr x8, x7, #63
	and x7, x7, x2
	mul x3, x8, x11
	adds x4, x4, x3
	adcs x5, x5, x10
	adcs x6, x6, x10
	adcs x7, x7, x10
	adds x21, x4, x11
	adcs x22, x5, x10
	adcs x23, x6, x10
	adcs x24, x7, x10
	lsr x8, x24, #63
	and x24, x24, x2
	sub x3, x10, x8
	eor x21, x21, x4
	and x21, x21, x3
	eor x4, x4, x21
	eor x22, x22, x5
	and x22, x22, x3
	eor x5, x5, x22
	eor x23, x23, x6
	and x23, x23, x3
	eor x6, x6, x23
	eor x24, x24, x7
	and x24, x24, x3
	eor x7, x7, x24
	add x2, x0, #0
	ldr x0, [x0, #48]
	ldr x19, [x2, #0]
	ldr x20, [x2, #8]
	ldr x21, [x2, #16]
	ldr x22, [x2, #24]
	ldr x23, [x2, #32]
	ldr x24, [x2, #40]
	str x4, [x0, #0]
	str x5, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	movz x1, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	tst x1, x1
	ret
	.p2align 6
