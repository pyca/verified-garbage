// The functions of `src/internal/vg_rsa_prime_search.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_prime_search:
	sub sp, sp, #160
	add x14, sp, #0
	ldr x8, [x14, #160]
	ldr x9, [x14, #168]
	ldr x10, [x14, #176]
	ldr x11, [x14, #184]
	ldr x12, [x11, #0]
	str x19, [x14, #32]
	add x19, x14, #0
	str x0, [x19, #40]
	str x1, [x19, #48]
	str x2, [x19, #56]
	str x3, [x19, #64]
	str x4, [x19, #72]
	str x5, [x19, #80]
	str x6, [x19, #88]
	str x7, [x19, #96]
	str x8, [x19, #104]
	str x9, [x19, #112]
	str x10, [x19, #120]
	str x11, [x19, #144]
	str x12, [x19, #0]
	str x1, [x19, #8]
	lsl x12, x1, #15
	add x12, x12, x1
	str x12, [x19, #16]
	movz x13, #0, lsl #0
	str x13, [x19, #24]
	str x13, [x19, #128]
	str x30, [sp, #-16]!
20:
	ldr x9, [x19, #0]
	cbz x9, 21f
	sub sp, sp, #32
	ldr x0, [x19, #40]
	ldr x1, [x19, #48]
	ldr x2, [x19, #56]
	ldr x3, [x19, #64]
	ldr x4, [x19, #72]
	ldr x5, [x19, #80]
	ldr x6, [x19, #88]
	ldr x7, [x19, #96]
	ldr x9, [x19, #104]
	ldr x10, [x19, #112]
	ldr x12, [x19, #120]
	add x11, sp, #0
	str x9, [x11, #0]
	str x10, [x11, #8]
	str x12, [x11, #16]
	bl {vg_rsa_keygen_candidate}
	add sp, sp, #32
	add w9, w0, #0
	ldr x11, [x19, #56]
	ldr x10, [x11, #0]
	sub x12, x9, #1
	cbz x12, 23f
	cbz x9, 25f
	cbz x10, 27f
	ldr x11, [x19, #96]
	ldr x12, [x19, #104]
	ldr x13, [x19, #128]
	add x11, x11, x10
	sub x12, x12, x10
	add x13, x13, x10
	movz x14, #4, lsl #0
	str x11, [x19, #96]
	str x12, [x19, #104]
	str x13, [x19, #128]
	str x14, [x19, #136]
	sub x13, x9, #2
	cbz x13, 29f
	ldr x11, [x19, #0]
	sub x11, x11, #1
	str x11, [x19, #0]
	b 210f
29:
210:
	b 28f
27:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #136]
	ldr x1, [x19, #40]
	ldr x2, [x19, #48]
	movz x3, #0, lsl #0
211:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 211b
28:
	b 26f
25:
	ldr x10, [x19, #104]
	ldr x11, [x19, #16]
	subs x12, x10, x11
	movz x13, #0, lsl #0
	movz x14, #1, lsl #0
	csel x12, x14, x13, hs
	cbz x12, 212f
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #136]
	ldr x1, [x19, #40]
	ldr x2, [x19, #48]
	movz x3, #0, lsl #0
214:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 214b
	b 213f
212:
	ldr x12, [x19, #8]
	lsl x12, x12, #4
	subs x13, x10, x12
	csel x10, x10, x12, hs
	add x10, x10, x10
	subs x13, x10, x11
	csel x10, x11, x10, hs
	movz x12, #0, lsl #0
	str x10, [x19, #24]
	str x12, [x19, #136]
213:
26:
	b 24f
23:
	ldr x11, [x19, #128]
	add x11, x11, x10
	str x11, [x19, #128]
	movz x10, #0, lsl #0
	movz x11, #1, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #136]
24:
	b 22f
21:
	movz x10, #0, lsl #0
	movz x11, #3, lsl #0
	str x10, [x19, #0]
	str x10, [x19, #24]
	str x11, [x19, #136]
	ldr x1, [x19, #40]
	ldr x2, [x19, #48]
	movz x3, #0, lsl #0
215:
	strb w3, [x1, #0]
	add x1, x1, #1
	sub x2, x2, #1
	cbnz x2, 215b
22:
	ldr x9, [x19, #136]
	sub x9, x9, #4
	cbz x9, 20b
	ldr x30, [sp], #16
	ldr x8, [x19, #144]
	ldr x9, [x19, #0]
	ldr x10, [x19, #8]
	ldr x11, [x19, #16]
	ldr x12, [x19, #24]
	ldr x13, [x19, #56]
	ldr x14, [x19, #128]
	ldr x0, [x19, #136]
	ldr x19, [x19, #32]
	str x9, [x8, #0]
	str x10, [x8, #8]
	str x11, [x8, #16]
	str x12, [x8, #24]
	str x14, [x13, #0]
	add sp, sp, #160
	ret
	.p2align 6
