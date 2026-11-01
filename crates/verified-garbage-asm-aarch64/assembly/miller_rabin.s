// The functions of `src/miller_rabin.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_miller_rabin_round:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x3, x11, #0
	add x3, x3, x3
	add x3, x3, x3
	add x3, x3, x11
	add x3, x3, x3
	add x3, x3, x11
	add x3, x3, x0
	add x3, x3, #256
	str x3, [x0, #208]
	movz x3, #14, lsl #0
	str x3, [x0, #240]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x17, [x0, #208]
	add x14, x12, #0
20:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 20b
	ldr x3, [x0, #208]
	ldr x4, [x0, #224]
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x17, [x0, #208]
	add x14, x12, #0
21:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 21b
	ldr x3, [x0, #208]
	ldr x4, [x0, #224]
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
22:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 22b
23:
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	ldr x17, [x0, #208]
	add x14, x12, #0
24:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 24b
	ldr x3, [x0, #208]
	ldr x4, [x0, #224]
	add x3, x3, x4
	str x3, [x0, #208]
	ldr x3, [x0, #240]
	sub x3, x3, #1
	str x3, [x0, #240]
	cbnz x3, 23b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
	add x14, x12, #0
25:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 25b
	ldr x3, [x0, #48]
	str x3, [x0, #232]
	movz x3, #0, lsl #0
	str x3, [x0, #184]
26:
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	ldr x3, [x0, #232]
	sub x3, x3, #1
	str x3, [x0, #232]
	lsl x5, x3, #3
	add x4, x16, x5
	ldr x5, [x4, #0]
	str x5, [x0, #208]
	movz x6, #16, lsl #0
	str x6, [x0, #240]
27:
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
28:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 28b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
29:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 29b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
210:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 210b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
211:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 211b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	ldr x3, [x0, #208]
	lsr x3, x3, #60
	str x3, [x0, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x2, x11, #0
	add x2, x2, x2
	add x2, x2, x2
	add x2, x2, x11
	add x2, x2, x2
	add x2, x2, x11
	add x2, x2, x0
	add x2, x2, #256
	add x13, x11, #0
	add x13, x13, x13
	add x13, x13, x13
	add x13, x13, x11
	add x13, x13, x0
	add x13, x13, #256
	ldr x9, [x0, #8]
	movz x10, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
212:
	eor x3, x10, x9
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x7, x8, hs
	add x16, x2, #0
	add x17, x13, #0
	add x14, x12, #0
213:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	and x3, x3, x15
	eor x4, x4, x3
	str x4, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 213b
	add x2, x2, x11
	add x10, x10, #1
	sub x3, x10, #16
	cbnz x3, 212b
	mov v31.d[0], x30
	bl {vg_rsa_mul_6_6_5}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
214:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 214b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	str x15, [x0, #8]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
215:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 215b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x3, [x0, #208]
	lsr x3, x3, #60
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x8, x7, #1
	csel x6, x8, x7, hs
	ldr x5, [x0, #8]
	orr x15, x15, x5
	and x15, x15, x6
	eor x6, x6, x8
	ldr x4, [x0, #184]
	and x4, x4, x6
	orr x4, x4, x15
	str x4, [x0, #184]
	ldr x3, [x0, #208]
	lsl x3, x3, #4
	str x3, [x0, #208]
	ldr x3, [x0, #240]
	sub x3, x3, #1
	str x3, [x0, #240]
	cbnz x3, 27b
	ldr x3, [x0, #232]
	cbnz x3, 26b
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
216:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 216b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x16, x16, x5
	ldr x3, [x16, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x8, x7, #1
	csel x6, x8, x7, hs
	and x15, x15, x6
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
217:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 217b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x16, x16, x5
	ldr x3, [x16, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x8, x7, #1
	csel x6, x8, x7, hs
	and x15, x15, x6
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	mov v31.d[0], x30
	bl {vg_rsa_square_6_6}
	umov x30, v31.d[0]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x9, #0, lsl #0
	add x14, x12, #0
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x0
	add x16, x16, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x17
	add x17, x17, x0
	add x17, x17, #256
218:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	eor x3, x3, x4
	orr x9, x9, x3
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 218b
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	subs x3, x9, x4
	sub x4, x7, #1
	csel x15, x7, x4, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x16
	add x16, x16, x11
	add x16, x16, x0
	add x16, x16, #256
	lsl x5, x12, #3
	add x16, x16, x5
	ldr x3, [x16, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	movz x7, #0, lsl #0
	sub x8, x7, #1
	csel x6, x8, x7, hs
	and x15, x15, x6
	ldr x4, [x0, #184]
	orr x4, x4, x15
	str x4, [x0, #184]
	ldr x3, [x0, #184]
	movz x4, #1, lsl #0
	and x0, x3, x4
	ret
	.p2align 6
