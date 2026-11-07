// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_generate_init:
	movz x9, #0, lsl #0
	movz x10, #0, lsl #0
	cbz x3, 20f
22:
	ldrb w11, [x2, #0]
	lsl x9, x9, #8
	add x9, x9, x11
	lsr x12, x9, #32
	orr x10, x10, x12
	add w9, w9, #0
	add x2, x2, #1
	sub x3, x3, #1
	cbnz x3, 22b
	b 21f
20:
21:
	movz x13, #1, lsl #0
	movz x14, #2, lsl #0
	movz x17, #0, lsl #0
	movz x15, #512, lsl #0
	subs x16, x1, x15
	csel x13, x13, x14, hs
	movz x15, #8193, lsl #0
	subs x16, x1, x15
	csel x13, x14, x13, hs
	subs x16, x17, x10
	csel x13, x13, x17, hs
	movz x15, #1, lsl #0
	and x16, x9, x15
	subs x16, x16, x15
	csel x13, x13, x17, hs
	subs x16, x15, x9
	csel x13, x17, x13, hs
	lsr x4, x1, #7
	lsl x4, x4, #3
	lsl x5, x4, #3
	lsl x6, x4, #5
	add x5, x5, x6
	lsl x6, x4, #6
	movz x15, #3, lsl #0
	eor x16, x9, x15
	subs x16, x17, x16
	csel x5, x6, x5, hs
	lsl x6, x4, #15
	add x6, x6, x4
	lsl x7, x4, #5
	movz x8, #4, lsl #0
	rev x11, x9
	movz x15, #1, lsl #0
	eor x16, x13, x15
	subs x16, x17, x16
	csel x5, x5, x17, hs
	csel x4, x4, x17, hs
	csel x6, x6, x17, hs
	csel x7, x7, x17, hs
	csel x8, x8, x17, hs
	csel x11, x11, x17, hs
	str x5, [x0, #0]
	str x4, [x0, #8]
	str x6, [x0, #16]
	str x7, [x0, #24]
	str x17, [x0, #32]
	str x8, [x0, #40]
	str x11, [x0, #48]
	add x0, x13, #0
	ret
	.p2align 6

vg_rsa_generate:
	sub sp, sp, #160
	add x14, sp, #0
	ldr x9, [x7, #8]
	ldr x10, [x7, #48]
	str x19, [x14, #72]
	add x19, x14, #0
	str x0, [x19, #0]
	str x2, [x19, #16]
	str x3, [x19, #24]
	str x4, [x19, #32]
	str x5, [x19, #40]
	str x6, [x19, #48]
	str x7, [x19, #56]
	str x9, [x19, #8]
	movz x17, #0, lsl #0
	str x17, [x19, #64]
	lsl x12, x9, #3
	lsl x13, x9, #5
	add x12, x12, x13
	lsl x13, x9, #6
	movz x15, #768, lsl #48
	eor x16, x10, x15
	subs x16, x17, x16
	csel x12, x13, x12, hs
	str x12, [x19, #88]
	str x30, [sp, #-16]!
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	str x9, [x19, #96]
	lsl x10, x10, #2
	str x10, [x19, #104]
	ldr x1, [x19, #96]
	ldr x2, [x19, #104]
	movz x3, #0, lsl #0
20:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 20b
	ldr x10, [x19, #8]
	lsl x11, x10, #2
	add x11, x11, x10
	ldr x9, [x19, #0]
	add x9, x9, x11
	str x9, [x19, #96]
	lsl x10, x10, #2
	str x10, [x19, #104]
	ldr x1, [x19, #96]
	ldr x2, [x19, #104]
	movz x3, #0, lsl #0
21:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 21b
22:
	sub sp, sp, #32
	ldr x8, [x19, #56]
	ldr x10, [x8, #32]
	ldr x1, [x19, #8]
	ldr x9, [x19, #0]
	lsl x5, x1, #2
	add x5, x5, x9
	add x0, x5, x1
	movz x17, #0, lsl #0
	subs x16, x17, x10
	csel x0, x5, x0, hs
	csel x6, x17, x1, hs
	ldr x2, [x19, #16]
	add x3, x8, #48
	movz x4, #8, lsl #0
	ldr x7, [x19, #24]
	ldr x11, [x19, #64]
	add x7, x7, x11
	ldr x12, [x19, #32]
	sub x12, x12, x11
	ldr x13, [x19, #40]
	ldr x14, [x19, #48]
	add x15, sp, #0
	str x12, [x15, #0]
	str x13, [x15, #8]
	str x14, [x15, #16]
	str x8, [x15, #24]
	bl {vg_rsa_prime_search}
	add sp, sp, #32
	add w9, w0, #0
	ldr x11, [x19, #16]
	ldr x10, [x11, #0]
	ldr x12, [x19, #64]
	add x12, x12, x10
	str x12, [x19, #64]
	cbz x9, 23f
	sub x12, x9, #3
	cbz x12, 25f
	cbz x10, 27f
	ldr x8, [x19, #56]
	ldr x10, [x8, #32]
	cbz x10, 29f
	sub sp, sp, #80
	ldr x5, [x19, #8]
	ldr x0, [x19, #0]
	ldr x10, [x19, #56]
	ldr x11, [x19, #40]
	ldr x12, [x19, #48]
	lsl x1, x5, #1
	add x2, x0, x1
	add x3, x1, #0
	add x4, x2, x1
	add x6, x4, x5
	add x7, x5, #0
	add x15, sp, #0
	add x9, x6, x5
	str x9, [x15, #0]
	str x5, [x15, #8]
	add x9, x9, x5
	str x9, [x15, #16]
	str x5, [x15, #24]
	add x9, x9, x5
	str x9, [x15, #32]
	str x5, [x15, #40]
	add x10, x10, #48
	str x10, [x15, #48]
	movz x9, #8, lsl #0
	str x9, [x15, #56]
	str x11, [x15, #64]
	str x12, [x15, #72]
	bl {vg_rsa_keygen_key}
	add sp, sp, #80
	add w9, w0, #0
	sub x12, x9, #1
	cbz x12, 211f
	sub x12, x9, #2
	cbz x12, 213f
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	str x9, [x19, #96]
	lsl x11, x10, #3
	add x11, x11, x10
	str x11, [x19, #104]
	ldr x1, [x19, #96]
	ldr x2, [x19, #104]
	movz x3, #0, lsl #0
215:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 215b
	ldr x8, [x19, #56]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	str x11, [x8, #40]
	movz x11, #2, lsl #0
	str x11, [x19, #80]
	b 214f
213:
	ldr x8, [x19, #56]
	ldr x11, [x19, #88]
	str x11, [x8, #0]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	movz x11, #4, lsl #0
	str x11, [x19, #80]
214:
	b 212f
211:
	ldr x8, [x19, #56]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	str x11, [x8, #40]
	movz x11, #1, lsl #0
	str x11, [x19, #80]
212:
	b 210f
29:
	ldr x8, [x19, #56]
	ldr x11, [x19, #88]
	str x11, [x8, #0]
	movz x11, #1, lsl #0
	str x11, [x8, #32]
	movz x11, #4, lsl #0
	str x11, [x19, #80]
210:
	b 28f
27:
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	str x9, [x19, #96]
	lsl x11, x10, #3
	add x11, x11, x10
	str x11, [x19, #104]
	ldr x1, [x19, #96]
	ldr x2, [x19, #104]
	movz x3, #0, lsl #0
216:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 216b
	ldr x8, [x19, #56]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	str x11, [x8, #40]
	movz x11, #3, lsl #0
	str x11, [x19, #80]
28:
	b 26f
25:
	ldr x8, [x19, #56]
	ldr x10, [x8, #40]
	movz x15, #2, lsl #0
	movz x13, #1, lsl #0
	movz x17, #0, lsl #0
	subs x16, x10, x15
	csel x12, x13, x17, hs
	cbz x12, 217f
	sub x10, x10, #1
	str x10, [x8, #40]
	ldr x8, [x19, #56]
	ldr x11, [x19, #88]
	str x11, [x8, #0]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	movz x11, #4, lsl #0
	str x11, [x19, #80]
	b 218f
217:
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	str x9, [x19, #96]
	lsl x11, x10, #3
	add x11, x11, x10
	str x11, [x19, #104]
	ldr x1, [x19, #96]
	ldr x2, [x19, #104]
	movz x3, #0, lsl #0
219:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 219b
	ldr x8, [x19, #56]
	movz x11, #0, lsl #0
	str x11, [x8, #32]
	str x11, [x8, #40]
	movz x11, #3, lsl #0
	str x11, [x19, #80]
218:
26:
	b 24f
23:
	str x9, [x19, #80]
24:
	ldr x9, [x19, #80]
	sub x9, x9, #4
	cbz x9, 22b
	ldr x30, [sp], #16
	ldr x1, [x19, #16]
	ldr x2, [x19, #64]
	ldr x0, [x19, #80]
	ldr x19, [x19, #72]
	str x2, [x1, #0]
	add sp, sp, #160
	ret
	.p2align 6
