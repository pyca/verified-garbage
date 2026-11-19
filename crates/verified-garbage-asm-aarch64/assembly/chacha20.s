// The functions of `src/chacha20.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_chacha20_init:
	ldr x9, [x1, #0]
	ldr x10, [x1, #8]
	ldr x11, [x1, #16]
	ldr x12, [x1, #24]
	str x9, [x0, #16]
	str x10, [x0, #24]
	str x11, [x0, #32]
	str x12, [x0, #40]
	add x1, x2, #0
	ldr x9, [x1, #0]
	ldr x10, [x1, #8]
	ldr w11, [x1, #0]
	str x9, [x0, #48]
	str x10, [x0, #56]
	movz x12, #30821, lsl #0
	movk x12, #24944, lsl #16
	movk x12, #25710, lsl #32
	movk x12, #13088, lsl #48
	str x12, [x0, #0]
	movz x12, #11570, lsl #0
	movk x12, #31074, lsl #16
	movk x12, #25972, lsl #32
	movk x12, #27424, lsl #48
	str x12, [x0, #8]
	movz x13, #1, lsl #32
	sub x13, x13, x11
	lsl x13, x13, #6
	str x13, [x0, #128]
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x13, #0, lsl #0
	ret
	.p2align 6

vg_chacha20_set_nonce:
	ldr x9, [x1, #0]
	ldr x10, [x1, #8]
	ldr w11, [x1, #0]
	str x9, [x0, #48]
	str x10, [x0, #56]
	movz x12, #30821, lsl #0
	movk x12, #24944, lsl #16
	movk x12, #25710, lsl #32
	movk x12, #13088, lsl #48
	str x12, [x0, #0]
	movz x12, #11570, lsl #0
	movk x12, #31074, lsl #16
	movk x12, #25972, lsl #32
	movk x12, #27424, lsl #48
	str x12, [x0, #8]
	movz x13, #1, lsl #32
	sub x13, x13, x11
	lsl x13, x13, #6
	str x13, [x0, #128]
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x13, #0, lsl #0
	ret
	.p2align 6

vg_chacha20_apply_sve2:
	ldr x9, [x0, #128]
	subs x13, x9, x2
	movz x11, #0, lsl #0
	adcs x11, x11, x11
	lsl x10, x9, #58
	lsr x10, x10, #58
	subs x13, x10, x2
	movz x12, #0, lsl #0
	adcs x12, x12, x12
	cbz x11, 20f
	str x21, [x0, #576]
	str x22, [x0, #584]
	str x23, [x0, #592]
	str x30, [x0, #600]
	add x21, x0, #0
	add x22, x1, #0
	add x23, x2, #0
	sub x9, x9, x2
	str x9, [x21, #608]
	cbz x12, 22f
	b 23f
22:
	add x2, x10, #0
23:
	add x1, x21, #128
	sub x1, x1, x10
	cbz x2, 24f
26:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 26b
	b 25f
24:
25:
	lsr x2, x23, #6
	lsl x2, x2, #6
	cbz x2, 27f
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	ldr x11, [x21, #16]
	ldr x12, [x21, #24]
	ldr x13, [x21, #32]
	ldr x14, [x21, #40]
	ldr x15, [x21, #48]
	ldr x16, [x21, #56]
	str x9, [x21, #192]
	str x10, [x21, #200]
	str x11, [x21, #208]
	str x12, [x21, #216]
	str x13, [x21, #224]
	str x14, [x21, #232]
	str x15, [x21, #240]
	str x16, [x21, #248]
	lsr x17, x2, #6
	add w15, w15, w17
	str w15, [x21, #48]
	add x0, x21, #192
	add x1, x22, #0
	add x3, x21, #256
	add x22, x22, x2
	sub x23, x23, x2
	add x4, x1, #0
	bl {vg_chacha20_xor_sve2}
	b 28f
27:
28:
	cbz x23, 29f
	add x0, x21, #0
	add x1, x21, #64
	bl {vg_chacha20_block}
	ldr w9, [x21, #48]
	add w9, w9, #1
	str w9, [x21, #48]
	add x1, x21, #64
	add x2, x23, #0
	cbz x2, 211f
213:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 213b
	b 212f
211:
212:
	b 210f
29:
210:
	ldr x9, [x21, #608]
	str x9, [x21, #128]
	ldr x30, [x21, #600]
	ldr x22, [x21, #584]
	ldr x23, [x21, #592]
	ldr x21, [x21, #576]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
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
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	add w0, w0, #0
	ret
	.p2align 6

vg_chacha20_apply_neon:
	ldr x9, [x0, #128]
	subs x13, x9, x2
	movz x11, #0, lsl #0
	adcs x11, x11, x11
	lsl x10, x9, #58
	lsr x10, x10, #58
	subs x13, x10, x2
	movz x12, #0, lsl #0
	adcs x12, x12, x12
	cbz x11, 20f
	str x21, [x0, #576]
	str x22, [x0, #584]
	str x23, [x0, #592]
	str x30, [x0, #600]
	add x21, x0, #0
	add x22, x1, #0
	add x23, x2, #0
	sub x9, x9, x2
	str x9, [x21, #608]
	cbz x12, 22f
	b 23f
22:
	add x2, x10, #0
23:
	add x1, x21, #128
	sub x1, x1, x10
	cbz x2, 24f
26:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 26b
	b 25f
24:
25:
	lsr x2, x23, #6
	lsl x2, x2, #6
	cbz x2, 27f
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	ldr x11, [x21, #16]
	ldr x12, [x21, #24]
	ldr x13, [x21, #32]
	ldr x14, [x21, #40]
	ldr x15, [x21, #48]
	ldr x16, [x21, #56]
	str x9, [x21, #192]
	str x10, [x21, #200]
	str x11, [x21, #208]
	str x12, [x21, #216]
	str x13, [x21, #224]
	str x14, [x21, #232]
	str x15, [x21, #240]
	str x16, [x21, #248]
	lsr x17, x2, #6
	add w15, w15, w17
	str w15, [x21, #48]
	add x0, x21, #192
	add x1, x22, #0
	add x3, x21, #256
	add x22, x22, x2
	sub x23, x23, x2
	add x4, x1, #0
	bl {vg_chacha20_xor_neon}
	b 28f
27:
28:
	cbz x23, 29f
	add x0, x21, #0
	add x1, x21, #64
	bl {vg_chacha20_block}
	ldr w9, [x21, #48]
	add w9, w9, #1
	str w9, [x21, #48]
	add x1, x21, #64
	add x2, x23, #0
	cbz x2, 211f
213:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 213b
	b 212f
211:
212:
	b 210f
29:
210:
	ldr x9, [x21, #608]
	str x9, [x21, #128]
	ldr x30, [x21, #600]
	ldr x22, [x21, #584]
	ldr x23, [x21, #592]
	ldr x21, [x21, #576]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
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
	tst x1, x1
	mov v8.d[1], x1
	mov v9.d[1], x1
	add w0, w0, #0
	ret
	.p2align 6

vg_chacha20_apply:
	ldr x9, [x0, #128]
	subs x13, x9, x2
	movz x11, #0, lsl #0
	adcs x11, x11, x11
	lsl x10, x9, #58
	lsr x10, x10, #58
	subs x13, x10, x2
	movz x12, #0, lsl #0
	adcs x12, x12, x12
	cbz x11, 20f
	str x21, [x0, #576]
	str x22, [x0, #584]
	str x23, [x0, #592]
	str x30, [x0, #600]
	add x21, x0, #0
	add x22, x1, #0
	add x23, x2, #0
	sub x9, x9, x2
	str x9, [x21, #608]
	cbz x12, 22f
	b 23f
22:
	add x2, x10, #0
23:
	add x1, x21, #128
	sub x1, x1, x10
	cbz x2, 24f
26:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 26b
	b 25f
24:
25:
	lsr x2, x23, #6
	lsl x2, x2, #6
	cbz x2, 27f
	ldr x9, [x21, #0]
	ldr x10, [x21, #8]
	ldr x11, [x21, #16]
	ldr x12, [x21, #24]
	ldr x13, [x21, #32]
	ldr x14, [x21, #40]
	ldr x15, [x21, #48]
	ldr x16, [x21, #56]
	str x9, [x21, #192]
	str x10, [x21, #200]
	str x11, [x21, #208]
	str x12, [x21, #216]
	str x13, [x21, #224]
	str x14, [x21, #232]
	str x15, [x21, #240]
	str x16, [x21, #248]
	lsr x17, x2, #6
	add w15, w15, w17
	str w15, [x21, #48]
	add x0, x21, #192
	add x1, x22, #0
	add x3, x21, #256
	add x22, x22, x2
	sub x23, x23, x2
	add x4, x1, #0
	bl {vg_chacha20_xor}
	b 28f
27:
28:
	cbz x23, 29f
	add x0, x21, #0
	add x1, x21, #64
	bl {vg_chacha20_block}
	ldr w9, [x21, #48]
	add w9, w9, #1
	str w9, [x21, #48]
	add x1, x21, #64
	add x2, x23, #0
	cbz x2, 211f
213:
	ldrb w9, [x22, #0]
	ldrb w10, [x1, #0]
	eor w9, w9, w10
	strb w9, [x22, #0]
	add x22, x22, #1
	add x1, x1, #1
	sub x2, x2, #1
	sub x23, x23, #1
	cbnz x2, 213b
	b 212f
211:
212:
	b 210f
29:
210:
	ldr x9, [x21, #608]
	str x9, [x21, #128]
	ldr x30, [x21, #600]
	ldr x22, [x21, #584]
	ldr x23, [x21, #592]
	ldr x21, [x21, #576]
	movz x0, #1, lsl #0
	b 21f
20:
	movz x0, #0, lsl #0
21:
	movz x1, #0, lsl #0
	movz x2, #0, lsl #0
	movz x3, #0, lsl #0
	movz x4, #0, lsl #0
	movz x5, #0, lsl #0
	movz x6, #0, lsl #0
	movz x7, #0, lsl #0
	movz x8, #0, lsl #0
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	movz x11, #0, lsl #0
	movz x12, #0, lsl #0
	movz x13, #0, lsl #0
	movz x14, #0, lsl #0
	movz x15, #0, lsl #0
	movz x16, #0, lsl #0
	movz x17, #0, lsl #0
	tst x1, x1
	add w0, w0, #0
	ret
	.p2align 6
