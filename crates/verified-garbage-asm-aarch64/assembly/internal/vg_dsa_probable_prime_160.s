// The functions of `src/internal/vg_dsa_probable_prime_160.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_probable_prime_160:
	sub sp, sp, #272
	str x0, [sp, #40]
	str x2, [sp, #112]
	str x3, [sp, #120]
	str x4, [sp, #136]
	movz x3, #0, lsl #0
	str x3, [sp, #128]
	ldr x0, [sp, #40]
	movz x3, #28672, lsl #0
	add x0, x0, x3
	movz x12, #4, lsl #0
	str x12, [x0, #48]
	movz x3, #0, lsl #0
	str x3, [x0, #56]
	add x3, x12, #2
	lsl x3, x3, #3
	add x4, x0, #256
	str x4, [x0, #64]
	add x4, x4, x3
	str x4, [x0, #72]
	add x4, x4, x3
	str x4, [x0, #80]
	add x4, x4, x3
	str x4, [x0, #88]
	add x4, x4, x3
	str x4, [x0, #96]
	add x4, x4, x3
	str x4, [x0, #104]
	add x4, x4, x3
	str x4, [x0, #112]
	add x4, x4, x3
	str x4, [x0, #120]
	add x4, x4, x3
	movz x3, #48, lsl #0
	str x3, [x0, #224]
	ldr x3, [sp, #40]
	movz x4, #26624, lsl #0
	add x3, x3, x4
	str x3, [x0, #128]
	movz x3, #20, lsl #0
	str x3, [x0, #136]
	movz x3, #24, lsl #0
	str x3, [x0, #144]
	movz x3, #64, lsl #0
	str x3, [x0, #152]
	ldr x3, [sp, #40]
	movz x4, #25408, lsl #0
	add x3, x3, x4
	str x3, [x0, #160]
	ldr x3, [sp, #112]
	movz x4, #0, lsl #0
	add x3, x3, x4
	str x3, [x0, #192]
	ldr x3, [sp, #120]
	movz x4, #0, lsl #0
	add x3, x3, x4
	str x3, [x0, #200]
	ldr x3, [sp, #128]
	movz x4, #0, lsl #0
	add x3, x3, x4
	str x3, [x0, #216]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
20:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 20b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x0, #256
	ldr x1, [x0, #160]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
21:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 22f
	b 23f
22:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
23:
	cbnz x2, 21b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x9, x11, #0
	add x9, x9, x9
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x9
	add x9, x9, x11
	add x9, x9, x0
	add x9, x9, #256
	add x4, x30, #0
	bl {vg_prime_table_write}
	add x30, x4, #0
	movz x3, #128, lsl #0
	movz x4, #256, lsl #0
	movz x5, #17, lsl #0
	subs x6, x12, x5
	csel x10, x4, x3, hs
	movz x1, #0, lsl #0
	movz x7, #0, lsl #0
	sub x8, x7, #1
24:
	ldr x17, [x9, #0]
	add x9, x9, #8
	add x3, x17, #0
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
25:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 25b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #16
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
26:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 26b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #32
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
27:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 27b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	lsr x3, x17, #48
	movz x4, #65535, lsl #0
	and x3, x3, x4
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	add x13, x3, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	add x14, x12, #0
	movz x2, #0, lsl #0
28:
	ldr x5, [x16, #0]
	add w4, w5, #0
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	lsr x4, x5, #32
	add x4, x4, x2
	mul w6, w4, w15
	mul x6, x6, x13
	add x6, x6, x4
	lsr x2, x6, #32
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 28b
	movz x4, #1, lsl #0
	subs x3, x2, x4
	csel x5, x7, x8, hs
	eor x3, x2, x13
	subs x3, x3, x4
	csel x6, x7, x8, hs
	orr x5, x5, x6
	orr x1, x1, x5
	sub x10, x10, #1
	eor x3, x1, x8
	and x10, x10, x3
	cbnz x10, 24b
	cbz x1, 29f
	movz x3, #3, lsl #0
	str x3, [x0, #248]
	b 210f
29:
	ldr x8, [x0, #64]
	ldr x3, [x8, #0]
	add x4, x3, #0
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	mul x5, x3, x4
	movz x6, #2, lsl #0
	sub x5, x6, x5
	mul x4, x4, x5
	movz x6, #0, lsl #0
	sub x15, x6, x4
	str x15, [x0, #56]
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #120]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
211:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 211b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	cbz x3, 212f
	ldr x12, [x0, #48]
	ldr x9, [x0, #64]
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	cbz x3, 214f
	ldr x11, [x0, #96]
	ldr x9, [x0, #64]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	subs x3, x7, x7
216:
	ldr x4, [x17, #0]
	sbcs x3, x7, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 216b
	lsl x13, x12, #3
	sub x13, x13, #8
	add x13, x9, x13
	ldr x5, [x13, #0]
	sub x2, x7, x5
	sub x2, x2, #1
	movz x10, #0, lsl #0
	movz x4, #1, lsl #0
	movz x13, #64, lsl #0
217:
	lsr x3, x2, #63
	lsl x2, x2, #1
	orr x2, x2, x4
	subs x15, x2, x5
	adc x16, x7, x7
	orr x16, x16, x3
	tst x16, x16
	csel x2, x15, x2, ne
	add x10, x10, x10
	add x10, x10, x16
	sub x13, x13, #1
	cbnz x13, 217b
	str x10, [x6, #0]
	ldr x13, [x0, #48]
	str x13, [x0, #208]
218:
	ldr x9, [x0, #64]
	ldr x11, [x0, #96]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	lsl x13, x12, #3
	sub x13, x13, #8
	add x14, x9, x13
	ldr x5, [x14, #0]
	add x16, x11, x13
	ldr x2, [x16, #0]
	sub x16, x16, #8
	ldr x3, [x16, #0]
	sub x4, x5, x2
	ldr x17, [x6, #0]
	mul x13, x17, x2
	umulh x14, x17, x2
	adds x13, x13, x3
	adc x14, x14, x2
	add x14, x14, #1
	mul x15, x14, x5
	sub x15, x3, x15
	sub x16, x14, #1
	add x17, x15, x5
	subs x3, x13, x15
	csel x14, x16, x14, lo
	csel x15, x17, x15, lo
	subs x3, x15, x5
	adc x14, x14, x7
	movz x16, #0, lsl #0
	sub x16, x16, #1
	tst x4, x4
	csel x1, x16, x14, eq
	lsl x13, x12, #3
	sub x13, x13, #24
	add x16, x11, x13
	ldr x3, [x16, #8]
	ldr x4, [x16, #0]
	add x17, x9, x13
	ldr x15, [x17, #8]
	sub x14, x12, #2
	tst x14, x14
	csel x4, x14, x4, eq
	mul x13, x1, x15
	umulh x14, x1, x15
	mul x16, x1, x5
	umulh x17, x1, x5
	adds x14, x14, x16
	adc x17, x17, x7
	subs x4, x4, x13
	sbcs x3, x3, x14
	sbc x2, x2, x17
	adds x4, x4, x15
	adcs x3, x3, x5
	adc x16, x2, x7
	sub x17, x1, #1
	tst x2, x2
	csel x1, x17, x1, mi
	csel x2, x16, x2, mi
	lsr x2, x2, #63
	sub x1, x1, x2
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	add x2, x7, #0
	movz x15, #0, lsl #0
	sub x15, x15, #1
	add x13, x15, #0
	adds x3, x7, x7
219:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x13
	eor x13, x3, x15
	eor x4, x4, x15
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 219b
	adc x4, x13, x2
	eor x4, x4, x15
	str x4, [x16, #0]
	lsl x13, x12, #3
	add x13, x11, x13
	ldr x3, [x13, #0]
	lsr x3, x3, #63
	sub x15, x7, x3
	add x16, x11, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x3, x7, x7
220:
	ldr x4, [x17, #0]
	and x4, x4, x15
	ldr x3, [x16, #0]
	adcs x3, x3, x4
	str x3, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 220b
	ldr x3, [x16, #0]
	adc x3, x3, x7
	str x3, [x16, #0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 218b
	b 215f
214:
	ldr x12, [x0, #48]
	ldr x8, [x0, #64]
	sub x4, x12, #1
	lsl x4, x4, #3
	add x4, x8, x4
	ldr x3, [x4, #0]
	movz x9, #1, lsl #0
	movz x13, #64, lsl #0
	sub x6, x3, #1
	cbz x6, 221f
223:
	lsr x3, x3, #1
	add x9, x9, x9
	sub x13, x13, #1
	sub x6, x3, #1
	cbnz x6, 223b
	b 222f
221:
222:
	str x13, [x0, #208]
	sub x13, x12, #1
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
224:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 224b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #208]
	ldr x12, [x0, #48]
	add x13, x13, x12
	str x13, [x0, #208]
225:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
226:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 226b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
227:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 227b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
228:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 228b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 225b
	movz x13, #6, lsl #0
	str x13, [x0, #208]
229:
	mov v31.d[0], x30
	bl {vg_rsa_square_4_4}
	umov x30, v31.d[0]
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 229b
215:
	b 213f
212:
	ldr x12, [x0, #48]
	movz x9, #1, lsl #0
	movz x13, #0, lsl #0
	ldr x8, [x0, #96]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
230:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 230b
	lsl x16, x13, #3
	add x16, x8, x16
	str x9, [x16, #0]
	ldr x13, [x0, #48]
	lsl x13, x13, #7
	str x13, [x0, #208]
231:
	ldr x5, [x0, #96]
	ldr x10, [x0, #64]
	ldr x8, [x0, #80]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	movz x7, #0, lsl #0
	add x17, x5, #0
	add x16, x8, #0
	add x14, x12, #0
	adds x3, x7, x7
232:
	ldr x3, [x17, #0]
	adcs x3, x3, x3
	str x3, [x16, #0]
	add x17, x17, #8
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 232b
	adc x3, x7, x7
	str x3, [x16, #0]
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
233:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 233b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
234:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 234b
	ldr x13, [x0, #208]
	sub x13, x13, #1
	str x13, [x0, #208]
	cbnz x13, 231b
213:
	ldr x8, [x0, #80]
	ldr x9, [x0, #120]
	ldr x10, [x0, #64]
	ldr x11, [x0, #96]
	ldr x5, [x0, #112]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
235:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 235b
	add x13, x12, #0
236:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
237:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 237b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
238:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 238b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 236b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
239:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 239b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
240:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 240b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
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
	add x14, x12, #0
241:
	ldr x3, [x16, #0]
	str x3, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 241b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	movz x7, #0, lsl #0
	sub x15, x7, #1
	add x14, x12, #0
	subs x3, x7, x7
	add x16, x0, #256
	add x17, x11, #0
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x17
	add x17, x17, x11
	add x17, x17, x0
	add x17, x17, #256
	add x8, x11, #0
	add x8, x8, x8
	add x8, x8, x8
	add x8, x8, x11
	add x8, x8, x8
	add x8, x8, x0
	add x8, x8, #256
242:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	and x4, x4, x15
	sbcs x3, x3, x4
	str x3, [x8, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x8, x8, #8
	sub x14, x14, #1
	cbnz x14, 242b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x0, #256
	ldr x5, [x16, #0]
	movz x4, #1, lsl #0
	eor x5, x5, x4
	add x16, x16, #8
	sub x14, x12, #1
	movz x7, #0, lsl #0
	sub x8, x7, #1
243:
	ldr x3, [x16, #0]
	subs x6, x5, x4
	csel x6, x7, x8, hs
	and x3, x3, x6
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 243b
	add x10, x11, #0
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x10
	add x10, x10, x11
	add x10, x10, x0
	add x10, x10, #256
	sub x6, x7, x5
	and x6, x6, x5
	lsl x9, x12, #3
	add x9, x10, x9
	str x6, [x9, #0]
	add x15, x8, #0
	add x17, x10, #0
	add x16, x0, #256
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
244:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 244b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #56797, lsl #0
	movk x4, #56797, lsl #16
	movk x4, #56797, lsl #32
	movk x4, #56797, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
245:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 245b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #39321, lsl #0
	movk x4, #39321, lsl #16
	movk x4, #39321, lsl #32
	movk x4, #39321, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
246:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 246b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x4, #4369, lsl #0
	movk x4, #4369, lsl #16
	movk x4, #4369, lsl #32
	movk x4, #4369, lsl #48
	ldr x3, [x9, #0]
	and x3, x3, x4
	movz x4, #1, lsl #0
	subs x3, x3, x4
	csel x15, x8, x7, hs
	add x16, x10, #0
	add x17, x10, #0
	ldr x5, [x16, #0]
	add x16, x16, #8
	sub x14, x12, #1
247:
	ldr x3, [x16, #0]
	lsl x4, x3, #63
	lsr x6, x5, #1
	orr x6, x6, x4
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x5, x3, #0
	sub x14, x14, #1
	cbnz x14, 247b
	lsr x6, x5, #1
	eor x6, x6, x5
	and x6, x6, x15
	eor x6, x6, x5
	str x6, [x17, #0]
	movz x3, #1, lsl #0
	str x3, [x0, #160]
	movz x3, #0, lsl #0
	str x3, [x0, #168]
248:
	ldr x3, [x0, #200]
	ldr x4, [x0, #216]
	sub x3, x3, x4
	ldr x4, [x0, #144]
	subs x3, x3, x4
	movz x7, #0, lsl #0
	movz x4, #1, lsl #0
	csel x5, x4, x7, hs
	cbz x5, 249f
	add x17, x0, #0
	ldr x12, [x0, #192]
	ldr x3, [x0, #216]
	add x12, x12, x3
	add x12, x12, #4
	add x3, x3, #24
	str x3, [x0, #216]
	ldr x2, [x0, #128]
	movz x9, #20, lsl #0
	cbnz x9, 251f
	b 252f
251:
253:
	ldrb w0, [x12, #0]
	strb w0, [x2, #0]
	add x12, x12, #1
	add x2, x2, #1
	sub x9, x9, #1
	cbnz x9, 253b
252:
	add x0, x17, #0
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
254:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 254b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
255:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 256f
	b 257f
256:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
257:
	cbnz x2, 255b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	ldr x5, [x16, #0]
	lsr x5, x5, #1
	add x16, x16, #8
	sub x14, x12, #1
258:
	ldr x3, [x16, #0]
	orr x5, x5, x3
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 258b
	movz x7, #0, lsl #0
	sub x8, x7, #1
	movz x4, #1, lsl #0
	subs x3, x5, x4
	csel x9, x8, x7, hs
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x16, x11, #0
	add x16, x16, x0
	add x16, x16, #256
	add x17, x0, #256
	ldr x3, [x16, #0]
	orr x3, x3, x4
	ldr x4, [x17, #0]
	subs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x12, #1
259:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 259b
	csel x15, x7, x8, hs
	and x9, x9, x15
	str x9, [x0, #0]
	cbz x9, 260f
	b 261f
260:
	ldr x1, [x0, #128]
	ldrb w3, [x1, #0]
	movz x4, #127, lsl #0
	and x3, x3, x4
	strb w3, [x1, #0]
	ldrb w3, [x1, #19]
	movz x4, #2, lsl #0
	orr x3, x3, x4
	strb w3, [x1, #19]
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
262:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 262b
	ldr x12, [x0, #48]
	ldr x11, [x0, #224]
	add x8, x11, #0
	add x8, x8, x0
	add x8, x8, #256
	ldr x1, [x0, #128]
	ldr x2, [x0, #136]
	movz x3, #0, lsl #0
	movz x6, #7, lsl #0
263:
	sub x2, x2, #1
	lsl x3, x3, #8
	ldrb w4, [x1, #0]
	add x3, x3, x4
	add x1, x1, #1
	and x5, x2, x6
	cbz x5, 264f
	b 265f
264:
	add x5, x8, x2
	str x3, [x5, #0]
	movz x3, #0, lsl #0
265:
	cbnz x2, 263b
261:
	ldr x8, [x0, #80]
	ldr x9, [x0, #96]
	ldr x10, [x0, #64]
	ldr x11, [x0, #72]
	ldr x5, [x0, #104]
	ldr x6, [x0, #88]
	ldr x12, [x0, #48]
	ldr x15, [x0, #56]
	movz x7, #0, lsl #0
	add x16, x8, #0
	add x14, x12, #2
266:
	str x7, [x16, #0]
	add x16, x16, #8
	sub x14, x14, #1
	cbnz x14, 266b
	add x13, x12, #0
267:
	ldr x1, [x11, #0]
	add x11, x11, #8
	add x16, x8, #0
	add x17, x9, #0
	add x14, x12, #0
	adds x2, x7, x7
268:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #0]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 268b
	adc x2, x2, x7
	ldr x3, [x16, #0]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #8]
	adc x3, x3, x7
	str x3, [x16, #8]
	ldr x3, [x8, #0]
	mul x1, x3, x15
	ldr x4, [x10, #0]
	mul x2, x1, x4
	umulh x4, x1, x4
	adds x2, x2, x3
	adc x2, x4, x7
	add x16, x8, #0
	add x17, x10, #8
	sub x14, x12, #1
	adds x3, x7, x7
269:
	ldr x3, [x17, #0]
	mul x4, x1, x3
	umulh x3, x1, x3
	adcs x4, x4, x2
	adc x2, x3, x7
	ldr x3, [x16, #8]
	adds x4, x4, x3
	str x4, [x16, #0]
	add x16, x16, #8
	add x17, x17, #8
	sub x14, x14, #1
	cbnz x14, 269b
	adc x2, x2, x7
	ldr x3, [x16, #8]
	adds x3, x3, x2
	str x3, [x16, #0]
	ldr x3, [x16, #16]
	adc x3, x3, x7
	str x3, [x16, #8]
	str x7, [x16, #16]
	sub x13, x13, #1
	cbnz x13, 267b
	add x16, x8, #0
	add x17, x10, #0
	add x13, x6, #0
	add x14, x12, #0
	subs x3, x7, x7
270:
	ldr x3, [x16, #0]
	ldr x4, [x17, #0]
	sbcs x3, x3, x4
	str x3, [x13, #0]
	add x16, x16, #8
	add x17, x17, #8
	add x13, x13, #8
	sub x14, x14, #1
	cbnz x14, 270b
	ldr x3, [x16, #0]
	sbcs x3, x3, x7
	add x16, x8, #0
	add x14, x12, #0
271:
	ldr x3, [x16, #0]
	ldr x4, [x6, #0]
	csel x3, x4, x3, hs
	str x3, [x5, #0]
	add x16, x16, #8
	add x6, x6, #8
	add x5, x5, #8
	sub x14, x14, #1
	cbnz x14, 271b
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	str x19, [x2, #0]
	str x30, [x2, #8]
	add x19, x0, #0
	ldr x1, [x0, #48]
	add x1, x1, #2
	movz x4, #28, lsl #0
	mul x1, x1, x4
	add x1, x1, #32
	bl {vg_dsa_miller_rabin_round}
	add w3, w0, #0
	add x0, x19, #0
	movz x4, #0, lsl #0
	sub x3, x4, x3
	str x3, [x0, #184]
	ldr x2, [x0, #120]
	ldr x3, [x0, #48]
	lsl x3, x3, #3
	add x2, x2, x3
	ldr x30, [x2, #8]
	ldr x19, [x2, #0]
	ldr x3, [x0, #184]
	cbz x3, 272f
	ldr x3, [x0, #160]
	add x3, x3, #1
	str x3, [x0, #160]
	ldr x4, [x0, #0]
	movz x5, #1, lsl #0
	and x4, x4, x5
	ldr x5, [x0, #168]
	add x4, x4, x5
	str x4, [x0, #168]
	movz x9, #4, lsl #0
	movz x10, #1, lsl #0
	movz x5, #17, lsl #0
	subs x6, x3, x5
	csel x13, x10, x9, hs
	ldr x5, [x0, #152]
	subs x6, x4, x5
	csel x13, x13, x9, hs
	str x13, [x0, #248]
	b 273f
272:
	movz x3, #3, lsl #0
	str x3, [x0, #248]
273:
	b 250f
249:
	movz x3, #0, lsl #0
	str x3, [x0, #248]
250:
	ldr x3, [x0, #248]
	sub x3, x3, #4
	cbz x3, 248b
210:
	ldr x3, [x0, #216]
	ldr x4, [sp, #136]
	str x3, [x4, #0]
	ldr x0, [x0, #248]
	lsr x3, x0, #1
	sub x0, x0, x3
	add sp, sp, #272
	ret
	.p2align 6
